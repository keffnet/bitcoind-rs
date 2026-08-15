//! Built-in PCP and NAT-PMP port mapping.
//!
//! Bitcoin Core keeps mappings alive in a background thread and advertises
//! successful external addresses through its address manager.  This module
//! follows the same shape while using Tokio UDP sockets and the platform's
//! routing tables instead of an external port-mapping dependency.

use std::fs;
use std::net::{IpAddr, Ipv4Addr, Ipv6Addr, SocketAddr, SocketAddrV6};
use std::time::{Duration, Instant};

use anyhow::{Context, Result, anyhow, bail};
use rand::random;
use tokio::net::UdpSocket;
use tokio::time::{sleep, timeout};
use tracing::{debug, info, warn};

use crate::Node;

const SERVER_PORT: u16 = 5_351;
const REQUESTED_LIFETIME_SECS: u32 = 2 * 20 * 60;
const RETRY_PERIOD: Duration = Duration::from_secs(5 * 60);
const MAX_TRIES: usize = 3;
const TRY_TIMEOUT: Duration = Duration::from_secs(1);
const PCP_VERSION: u8 = 2;
const PCP_MAP_REQUEST: u8 = 1;
const PCP_MAP_RESPONSE: u8 = 0x81;
const PCP_TCP: u8 = 6;
const PCP_HEADER_SIZE: usize = 24;
const PCP_MAP_SIZE: usize = 36;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Mapping {
    external: SocketAddr,
    lifetime_secs: u32,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum PcpOutcome {
    Mapped(Mapping),
    Unsupported,
}

/// Keep a P2P mapping alive until the node shuts down. Mapping failures are
/// intentionally non-fatal: routers commonly do not implement either
/// protocol, and Core treats that case as a background networking condition.
pub async fn run(node: std::sync::Arc<Node>, port: u16) -> Result<()> {
    if port == 0 {
        return Ok(());
    }

    loop {
        let nonce = random::<[u8; 12]>();
        let mut mappings = Vec::new();

        if let Some(gateway) = default_gateway_v4() {
            match pcp_request(gateway, port, REQUESTED_LIFETIME_SECS, nonce).await {
                Ok(PcpOutcome::Mapped(mapping)) => mappings.push(mapping),
                Ok(PcpOutcome::Unsupported) => {
                    match natpmp_request(gateway, port, REQUESTED_LIFETIME_SECS).await {
                        Ok(mapping) => mappings.push(mapping),
                        Err(error) => debug!(%error, "NAT-PMP port mapping failed"),
                    }
                }
                Err(error) => debug!(%error, "PCP port mapping failed"),
            }
        } else {
            debug!("no IPv4 default gateway found for port mapping");
        }

        if let Some(gateway) = default_gateway_v6() {
            match pcp_request(gateway, port, REQUESTED_LIFETIME_SECS, nonce).await {
                Ok(PcpOutcome::Mapped(mapping)) => mappings.push(mapping),
                Ok(PcpOutcome::Unsupported) => {
                    debug!("IPv6 gateway does not support PCP");
                }
                Err(error) => debug!(%error, "IPv6 PCP port mapping failed"),
            }
        }

        if mappings.is_empty() {
            if !sleep_or_shutdown(&node, RETRY_PERIOD).await {
                return Ok(());
            }
            continue;
        }

        let mut lifetime = REQUESTED_LIFETIME_SECS;
        for mapping in mappings {
            lifetime = lifetime.min(mapping.lifetime_secs);
            info!(address = %mapping.external, lifetime = mapping.lifetime_secs, "P2P port mapped");
            node.add_mapped_address(mapping.external);
        }
        if lifetime < 30 {
            warn!(lifetime, "port mapping returned an unusably short lifetime");
            return Ok(());
        }

        // RFC 6887 recommends renewing in a randomized window from one half
        // to five eighths of the lifetime. A deterministic midpoint keeps
        // this task cheap while preserving a generous renewal margin.
        let renew_after = Duration::from_secs(u64::from(lifetime / 2));
        if !sleep_or_shutdown(&node, renew_after).await {
            return Ok(());
        }
    }
}

async fn sleep_or_shutdown(node: &Node, duration: Duration) -> bool {
    tokio::select! {
        _ = sleep(duration) => true,
        _ = node.wait_for_shutdown() => false,
    }
}

async fn pcp_request(
    gateway: SocketAddr,
    port: u16,
    lifetime_secs: u32,
    nonce: [u8; 12],
) -> Result<PcpOutcome> {
    let bind = match gateway {
        SocketAddr::V4(_) => SocketAddr::from(([0, 0, 0, 0], 0)),
        SocketAddr::V6(address) => SocketAddr::V6(SocketAddrV6::new(
            Ipv6Addr::UNSPECIFIED,
            0,
            0,
            address.scope_id(),
        )),
    };
    let socket = UdpSocket::bind(bind)
        .await
        .with_context(|| format!("binding PCP socket for gateway {gateway}"))?;
    socket
        .connect(gateway)
        .await
        .with_context(|| format!("connecting PCP socket to gateway {gateway}"))?;
    let local = socket.local_addr().context("reading PCP local address")?;

    let mut request = [0u8; PCP_HEADER_SIZE + PCP_MAP_SIZE];
    request[0] = PCP_VERSION;
    request[1] = PCP_MAP_REQUEST;
    request[4..8].copy_from_slice(&lifetime_secs.to_be_bytes());
    request[8..24].copy_from_slice(&pcp_address(local.ip()));
    request[24..36].copy_from_slice(&nonce);
    request[36] = PCP_TCP;
    request[40..42].copy_from_slice(&port.to_be_bytes());
    request[42..44].copy_from_slice(&port.to_be_bytes());

    let response = exchange(&socket, &request, "PCP", |response| {
        (response.len() == 8
            && response[0] == 0
            && u16::from_be_bytes([response[2], response[3]]) == 1)
            || (response.len() >= request.len()
                && response[0] == PCP_VERSION
                && response[1] == PCP_MAP_RESPONSE)
    })
    .await?;
    if response.len() >= 4
        && response[0] == 0
        && u16::from_be_bytes([response[2], response[3]]) == 1
    {
        return Ok(PcpOutcome::Unsupported);
    }
    if response.len() < request.len()
        || response[0] != PCP_VERSION
        || response[1] != PCP_MAP_RESPONSE
    {
        bail!("PCP response has an invalid shape");
    }
    if response[24..36] != nonce {
        bail!("PCP response nonce does not match the request");
    }
    if response[36] != PCP_TCP || u16::from_be_bytes([response[40], response[41]]) != port {
        bail!("PCP response protocol or port does not match the request");
    }
    let result_code = response[3];
    if result_code != 0 {
        bail!("PCP mapping failed with result code {result_code}");
    }
    let external_ip = decode_pcp_address(&response[44..60])
        .ok_or_else(|| anyhow!("PCP response did not contain an external address"))?;
    let external_port = u16::from_be_bytes([response[42], response[43]]);
    let lifetime_secs = u32::from_be_bytes([response[4], response[5], response[6], response[7]]);
    Ok(PcpOutcome::Mapped(Mapping {
        external: SocketAddr::new(external_ip, external_port),
        lifetime_secs,
    }))
}

async fn natpmp_request(gateway: SocketAddr, port: u16, lifetime_secs: u32) -> Result<Mapping> {
    let SocketAddr::V4(gateway) = gateway else {
        bail!("NAT-PMP requires an IPv4 gateway");
    };
    let socket = UdpSocket::bind(SocketAddr::from(([0, 0, 0, 0], 0)))
        .await
        .context("binding NAT-PMP socket")?;
    socket
        .connect(SocketAddr::new((*gateway.ip()).into(), gateway.port()))
        .await
        .with_context(|| format!("connecting NAT-PMP socket to {gateway}"))?;

    let external_response = exchange(&socket, &[0, 0], "NAT-PMP", |response| {
        response.len() >= 12 && response[0] == 0 && response[1] == 0x80
    })
    .await?;
    if external_response.len() < 12 || external_response[0] != 0 || external_response[1] != 0x80 {
        bail!("NAT-PMP external-address response has an invalid shape");
    }
    let result_code = u16::from_be_bytes([external_response[2], external_response[3]]);
    if result_code != 0 {
        bail!("NAT-PMP external-address request failed with result code {result_code}");
    }
    let external_ip = Ipv4Addr::new(
        external_response[8],
        external_response[9],
        external_response[10],
        external_response[11],
    );

    let mut request = [0u8; 12];
    request[0] = 0;
    request[1] = 2;
    request[4..6].copy_from_slice(&port.to_be_bytes());
    request[6..8].copy_from_slice(&port.to_be_bytes());
    request[8..12].copy_from_slice(&lifetime_secs.to_be_bytes());
    let response = exchange(&socket, &request, "NAT-PMP", |response| {
        response.len() >= 16 && response[0] == 0 && response[1] == 0x82
    })
    .await?;
    if response.len() < 16 || response[0] != 0 || response[1] != 0x82 {
        bail!("NAT-PMP mapping response has an invalid shape");
    }
    let result_code = u16::from_be_bytes([response[2], response[3]]);
    if result_code != 0 {
        bail!("NAT-PMP mapping failed with result code {result_code}");
    }
    let internal_port = u16::from_be_bytes([response[8], response[9]]);
    if internal_port != port {
        bail!("NAT-PMP mapping response port does not match the request");
    }
    Ok(Mapping {
        external: SocketAddr::new(
            IpAddr::V4(external_ip),
            u16::from_be_bytes([response[10], response[11]]),
        ),
        lifetime_secs: u32::from_be_bytes([response[12], response[13], response[14], response[15]]),
    })
}

async fn exchange(
    socket: &UdpSocket,
    request: &[u8],
    protocol: &str,
    accept: impl Fn(&[u8]) -> bool,
) -> Result<Vec<u8>> {
    let mut response = [0u8; 1_100];
    for attempt in 0..MAX_TRIES {
        if attempt != 0 {
            debug!(protocol, attempt, "retrying port-mapping request");
        }
        socket
            .send(request)
            .await
            .with_context(|| format!("sending {protocol} request"))?;
        let deadline = Instant::now() + TRY_TIMEOUT;
        loop {
            let remaining = deadline.saturating_duration_since(Instant::now());
            if remaining.is_zero() {
                break;
            }
            match timeout(remaining, socket.recv(&mut response)).await {
                Ok(Ok(length)) if accept(&response[..length]) => {
                    return Ok(response[..length].to_vec());
                }
                Ok(Ok(_)) => {
                    debug!(protocol, "ignoring an unrelated port-mapping response");
                }
                Ok(Err(error)) => {
                    return Err(error).context(format!("receiving {protocol} response"));
                }
                Err(_) => break,
            }
        }
    }
    bail!("{protocol} request failed")
}

fn pcp_address(address: IpAddr) -> [u8; 16] {
    match address {
        IpAddr::V4(address) => {
            let mut encoded = [0u8; 16];
            encoded[10..12].copy_from_slice(&[0xff, 0xff]);
            encoded[12..].copy_from_slice(&address.octets());
            encoded
        }
        IpAddr::V6(address) => address.octets(),
    }
}

fn decode_pcp_address(bytes: &[u8]) -> Option<IpAddr> {
    let bytes: [u8; 16] = bytes.try_into().ok()?;
    if bytes[..10] == [0; 10] && bytes[10..12] == [0xff, 0xff] {
        Some(IpAddr::V4(Ipv4Addr::new(
            bytes[12], bytes[13], bytes[14], bytes[15],
        )))
    } else {
        Some(IpAddr::V6(Ipv6Addr::from(bytes)))
    }
}

#[cfg(target_os = "linux")]
fn default_gateway_v4() -> Option<SocketAddr> {
    let routes = fs::read_to_string("/proc/net/route").ok()?;
    for line in routes.lines().skip(1) {
        let fields = line.split_whitespace().collect::<Vec<_>>();
        if fields.len() < 4 || fields[1] != "00000000" {
            continue;
        }
        let flags = u16::from_str_radix(fields[3], 16).ok()?;
        if flags & 0x2 == 0 {
            continue;
        }
        let gateway = u32::from_str_radix(fields[2], 16).ok()?.to_le_bytes();
        let address = Ipv4Addr::from(gateway);
        if !address.is_unspecified() {
            return Some(SocketAddr::new(IpAddr::V4(address), SERVER_PORT));
        }
    }
    None
}

#[cfg(not(target_os = "linux"))]
fn default_gateway_v4() -> Option<SocketAddr> {
    None
}

#[cfg(target_os = "linux")]
fn default_gateway_v6() -> Option<SocketAddr> {
    let routes = fs::read_to_string("/proc/net/ipv6_route").ok()?;
    for line in routes.lines() {
        let fields = line.split_whitespace().collect::<Vec<_>>();
        if fields.len() < 10 || fields[0] != "00000000000000000000000000000000" || fields[1] != "00"
        {
            continue;
        }
        let gateway = parse_ipv6_hex(fields[4])?;
        if gateway.is_unspecified() {
            continue;
        }
        let scope_id = fs::read_to_string(format!("/sys/class/net/{}/ifindex", fields[9]))
            .ok()
            .and_then(|index| index.trim().parse().ok())
            .unwrap_or(0);
        return Some(SocketAddr::V6(SocketAddrV6::new(
            gateway,
            SERVER_PORT,
            0,
            scope_id,
        )));
    }
    None
}

#[cfg(not(target_os = "linux"))]
fn default_gateway_v6() -> Option<SocketAddr> {
    None
}

#[cfg(target_os = "linux")]
fn parse_ipv6_hex(value: &str) -> Option<Ipv6Addr> {
    if value.len() != 32 {
        return None;
    }
    let mut bytes = [0u8; 16];
    for (index, pair) in value.as_bytes().chunks_exact(2).enumerate() {
        bytes[index] = u8::from_str_radix(std::str::from_utf8(pair).ok()?, 16).ok()?;
    }
    Some(Ipv6Addr::from(bytes))
}

#[cfg(test)]
mod tests {
    use tokio::net::UdpSocket;

    use super::*;

    #[test]
    fn pcp_addresses_round_trip_ipv4_and_ipv6() {
        let ipv4 = IpAddr::V4(Ipv4Addr::new(198, 51, 100, 7));
        assert_eq!(decode_pcp_address(&pcp_address(ipv4)), Some(ipv4));
        let ipv6 = "2001:db8::7".parse().unwrap();
        assert_eq!(decode_pcp_address(&pcp_address(ipv6)), Some(ipv6));
    }

    #[tokio::test]
    async fn pcp_mapping_round_trip() {
        let server = UdpSocket::bind("127.0.0.1:0").await.unwrap();
        let gateway = server.local_addr().unwrap();
        let nonce = [7u8; 12];
        let task = tokio::spawn(async move {
            let mut request = [0u8; 128];
            let (length, peer) = server.recv_from(&mut request).await.unwrap();
            assert_eq!(length, PCP_HEADER_SIZE + PCP_MAP_SIZE);
            assert_eq!(&request[..2], &[PCP_VERSION, PCP_MAP_REQUEST]);
            assert_eq!(&request[24..36], &nonce);
            server.send_to(&[0xff, 0xff], peer).await.unwrap();
            let mut response = [0u8; PCP_HEADER_SIZE + PCP_MAP_SIZE];
            response[0] = PCP_VERSION;
            response[1] = PCP_MAP_RESPONSE;
            response[4..8].copy_from_slice(&1_200u32.to_be_bytes());
            response[24..36].copy_from_slice(&nonce);
            response[36] = PCP_TCP;
            response[40..42].copy_from_slice(&9_001u16.to_be_bytes());
            response[42..44].copy_from_slice(&9_002u16.to_be_bytes());
            response[44..60]
                .copy_from_slice(&pcp_address(IpAddr::V4(Ipv4Addr::new(198, 51, 100, 9))));
            server.send_to(&response, peer).await.unwrap();
        });
        let result = pcp_request(gateway, 9_001, 1_200, nonce).await.unwrap();
        task.await.unwrap();
        assert_eq!(
            result,
            PcpOutcome::Mapped(Mapping {
                external: "198.51.100.9:9002".parse().unwrap(),
                lifetime_secs: 1_200,
            })
        );
    }

    #[tokio::test]
    async fn natpmp_mapping_round_trip() {
        let server = UdpSocket::bind("127.0.0.1:0").await.unwrap();
        let gateway = server.local_addr().unwrap();
        let task = tokio::spawn(async move {
            let mut request = [0u8; 128];
            let (length, peer) = server.recv_from(&mut request).await.unwrap();
            assert_eq!(&request[..length], &[0, 0]);
            let mut external = [0u8; 12];
            external[1] = 0x80;
            external[8..12].copy_from_slice(&[198, 51, 100, 10]);
            server.send_to(&external, peer).await.unwrap();

            let (length, peer) = server.recv_from(&mut request).await.unwrap();
            assert_eq!(length, 12);
            assert_eq!(&request[..2], &[0, 2]);
            let mut mapping = [0u8; 16];
            mapping[1] = 0x82;
            mapping[8..10].copy_from_slice(&9_001u16.to_be_bytes());
            mapping[10..12].copy_from_slice(&9_002u16.to_be_bytes());
            mapping[12..16].copy_from_slice(&1_200u32.to_be_bytes());
            server.send_to(&mapping, peer).await.unwrap();
        });
        let result = natpmp_request(gateway, 9_001, 1_200).await.unwrap();
        task.await.unwrap();
        assert_eq!(
            result,
            Mapping {
                external: "198.51.100.10:9002".parse().unwrap(),
                lifetime_secs: 1_200,
            }
        );
    }
}

//! Network endpoints used by the address manager and BIP155 ADDRv2.

use std::fmt;
use std::net::{IpAddr, Ipv4Addr, Ipv6Addr, SocketAddr};

use anyhow::{Result, bail};
use sha3::{Digest, Sha3_256};

/// A validated endpoint from one of the BIP155 address networks.
///
/// Connected peers still use [`SocketAddr`] because a live TCP connection has
/// already resolved its destination. The address manager keeps the network
/// identity here so Tor, I2P, and CJDNS records survive persistence and relay.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum NetworkEndpoint {
    Ip(SocketAddr),
    OnionV2 { address: [u8; 10], port: u16 },
    OnionV3 { address: [u8; 32], port: u16 },
    I2p { address: [u8; 32], port: u16 },
    Cjdns { address: Ipv6Addr, port: u16 },
}

impl NetworkEndpoint {
    /// Decode a BIP155 network/address pair.
    pub fn from_addr_v2(network: u8, address: &[u8], port: u16) -> Option<Self> {
        if port == 0 {
            return None;
        }
        match network {
            1 => Some(Self::Ip(SocketAddr::new(
                IpAddr::V4(Ipv4Addr::from(<[u8; 4]>::try_from(address).ok()?)),
                port,
            ))),
            2 => Some(Self::Ip(SocketAddr::new(
                IpAddr::V6(Ipv6Addr::from(<[u8; 16]>::try_from(address).ok()?)),
                port,
            ))),
            3 => Some(Self::OnionV2 {
                address: <[u8; 10]>::try_from(address).ok()?,
                port,
            }),
            4 => Some(Self::OnionV3 {
                address: <[u8; 32]>::try_from(address).ok()?,
                port,
            }),
            5 => Some(Self::I2p {
                address: <[u8; 32]>::try_from(address).ok()?,
                port,
            }),
            6 => Some(Self::Cjdns {
                address: Ipv6Addr::from(<[u8; 16]>::try_from(address).ok()?),
                port,
            }),
            _ => None,
        }
    }

    /// Return the BIP155 network ID and raw address bytes.
    pub fn to_addr_v2(&self) -> (u8, Vec<u8>) {
        match self {
            Self::Ip(address) => match address.ip() {
                IpAddr::V4(ip) => (1, ip.octets().to_vec()),
                IpAddr::V6(ip) => (2, ip.octets().to_vec()),
            },
            Self::OnionV2 { address, .. } => (3, address.to_vec()),
            Self::OnionV3 { address, .. } => (4, address.to_vec()),
            Self::I2p { address, .. } => (5, address.to_vec()),
            Self::Cjdns { address, .. } => (6, address.octets().to_vec()),
        }
    }

    pub fn port(&self) -> u16 {
        match self {
            Self::Ip(address) => address.port(),
            Self::OnionV2 { port, .. }
            | Self::OnionV3 { port, .. }
            | Self::I2p { port, .. }
            | Self::Cjdns { port, .. } => *port,
        }
    }

    /// The RPC/`onlynet` network name used for this endpoint.
    pub fn network_name(&self) -> &'static str {
        match self {
            Self::Ip(address) if address.is_ipv4() => "ipv4",
            Self::Ip(_) => "ipv6",
            Self::OnionV2 { .. } | Self::OnionV3 { .. } => "onion",
            Self::I2p { .. } => "i2p",
            Self::Cjdns { .. } => "cjdns",
        }
    }

    /// Return a directly usable socket address for endpoint types that have
    /// one. CJDNS uses IPv6 on the wire and can therefore be passed to a
    /// SOCKS5 proxy as an IPv6 destination, while still retaining its BIP155
    /// network identity in the address manager.
    pub fn socket_addr(&self) -> Option<SocketAddr> {
        match self {
            Self::Ip(address) => Some(*address),
            Self::Cjdns { address, port } => Some(SocketAddr::new((*address).into(), *port)),
            Self::OnionV2 { .. } | Self::OnionV3 { .. } | Self::I2p { .. } => None,
        }
    }

    /// Return a socket address only when the endpoint is valid for legacy
    /// `addr` messages, which have no network discriminator.
    pub fn legacy_socket_addr(&self) -> Option<SocketAddr> {
        match self {
            Self::Ip(address) => Some(*address),
            Self::OnionV2 { .. } | Self::OnionV3 { .. } | Self::I2p { .. } | Self::Cjdns { .. } => {
                None
            }
        }
    }

    /// Host portion used by RPC and SOCKS5 domain requests.
    pub fn host_string(&self) -> String {
        match self {
            Self::Ip(address) => address.ip().to_string(),
            Self::OnionV2 { address, .. } => format!("{}.onion", base32_encode(address)),
            Self::OnionV3 { address, .. } => {
                format!("{}.onion", tor_v3_address(address))
            }
            Self::I2p { address, .. } => format!("{}.b32.i2p", base32_encode(address)),
            Self::Cjdns { address, .. } => address.to_string(),
        }
    }

    /// Parse an address-manager entry. Legacy entries use the full socket
    /// address in `address` and leave `port` absent; BIP155 entries use the
    /// network-specific host string plus a separate port.
    pub fn parse(network: Option<&str>, address: &str, port: Option<u16>) -> Result<Self> {
        let Some(network) = network else {
            let socket = address.parse::<SocketAddr>()?;
            if socket.port() == 0 {
                bail!("network endpoint port must be non-zero")
            }
            return Ok(Self::Ip(socket));
        };
        let port = port.ok_or_else(|| anyhow::anyhow!("network endpoint is missing a port"))?;
        if port == 0 {
            bail!("network endpoint port must be non-zero")
        }
        match network {
            "ipv4" => {
                let ip = address.parse::<Ipv4Addr>()?;
                Ok(Self::Ip(SocketAddr::new(ip.into(), port)))
            }
            "ipv6" => {
                let ip = address.parse::<Ipv6Addr>()?;
                Ok(Self::Ip(SocketAddr::new(ip.into(), port)))
            }
            "cjdns" => Ok(Self::Cjdns {
                address: address.parse::<Ipv6Addr>()?,
                port,
            }),
            "onion" => parse_onion(address, port),
            "i2p" => Ok(Self::I2p {
                address: decode_fixed_base32::<32>(
                    address.strip_suffix(".b32.i2p").unwrap_or(address),
                )?,
                port,
            }),
            _ => bail!("unknown network endpoint type '{network}'"),
        }
    }
}

impl fmt::Display for NetworkEndpoint {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Ip(_) => {
                if let Some(address) = self.socket_addr() {
                    return address.fmt(formatter);
                }
                unreachable!("IP endpoint has a socket address")
            }
            Self::Cjdns { .. } => {
                if let Some(address) = self.socket_addr() {
                    return address.fmt(formatter);
                }
                unreachable!("CJDNS endpoint has a socket address")
            }
            Self::OnionV2 { .. } | Self::OnionV3 { .. } | Self::I2p { .. } => {
                write!(formatter, "{}:{}", self.host_string(), self.port())
            }
        }
    }
}

fn parse_onion(address: &str, port: u16) -> Result<NetworkEndpoint> {
    let label = address.strip_suffix(".onion").unwrap_or(address);
    let decoded = base32_decode(label)?;
    match decoded.len() {
        10 => Ok(NetworkEndpoint::OnionV2 {
            address: decoded.try_into().expect("length checked"),
            port,
        }),
        35 => {
            let public_key: [u8; 32] = decoded[..32].try_into().expect("length checked");
            let checksum = tor_v3_checksum(&public_key);
            if decoded[32..34] != checksum || decoded[34] != 3 {
                bail!("invalid Tor v3 onion checksum")
            }
            Ok(NetworkEndpoint::OnionV3 {
                address: public_key,
                port,
            })
        }
        _ => bail!("invalid onion address length"),
    }
}

fn tor_v3_address(address: &[u8; 32]) -> String {
    let checksum = tor_v3_checksum(address);
    let mut encoded = [0u8; 35];
    encoded[..32].copy_from_slice(address);
    encoded[32..34].copy_from_slice(&checksum);
    encoded[34] = 3;
    base32_encode(&encoded)
}

fn tor_v3_checksum(address: &[u8; 32]) -> [u8; 2] {
    let mut hasher = Sha3_256::new();
    hasher.update(b".onion checksum");
    hasher.update(address);
    hasher.update([3]);
    let digest = hasher.finalize();
    [digest[0], digest[1]]
}

fn base32_encode(bytes: &[u8]) -> String {
    const ALPHABET: &[u8; 32] = b"abcdefghijklmnopqrstuvwxyz234567";
    let mut output = String::with_capacity(bytes.len().saturating_mul(8).div_ceil(5));
    let mut buffer = 0u32;
    let mut bits = 0u8;
    for &byte in bytes {
        buffer = (buffer << 8) | u32::from(byte);
        bits = bits.saturating_add(8);
        while bits >= 5 {
            bits -= 5;
            output.push(char::from(ALPHABET[((buffer >> bits) & 0x1f) as usize]));
        }
        if bits == 0 {
            buffer = 0;
        } else {
            buffer &= (1 << bits) - 1;
        }
    }
    if bits != 0 {
        output.push(char::from(
            ALPHABET[((buffer << (5 - bits)) & 0x1f) as usize],
        ));
    }
    output
}

fn base32_decode(value: &str) -> Result<Vec<u8>> {
    let mut output = Vec::with_capacity(value.len().saturating_mul(5) / 8);
    let mut buffer = 0u32;
    let mut bits = 0u8;
    for byte in value.bytes() {
        let value = match byte.to_ascii_lowercase() {
            b'a'..=b'z' => byte.to_ascii_lowercase() - b'a',
            b'2'..=b'7' => byte - b'2' + 26,
            _ => bail!("invalid base32 character"),
        };
        buffer = (buffer << 5) | u32::from(value);
        bits = bits.saturating_add(5);
        if bits >= 8 {
            bits -= 8;
            output.push((buffer >> bits) as u8);
            if bits == 0 {
                buffer = 0;
            } else {
                buffer &= (1 << bits) - 1;
            }
        }
    }
    if bits >= 5 || (bits > 0 && (buffer & ((1u32 << bits) - 1)) != 0) {
        bail!("invalid base32 padding")
    }
    Ok(output)
}

fn decode_fixed_base32<const LENGTH: usize>(value: &str) -> Result<[u8; LENGTH]> {
    base32_decode(value)?.try_into().map_err(|bytes: Vec<u8>| {
        anyhow::anyhow!("invalid base32 length {}, expected {LENGTH}", bytes.len())
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn decodes_and_formats_all_bip155_networks() {
        let endpoints = [
            NetworkEndpoint::Ip("192.0.2.1:8333".parse().unwrap()),
            NetworkEndpoint::Ip("[2001:db8::1]:8333".parse().unwrap()),
            NetworkEndpoint::OnionV2 {
                address: [1; 10],
                port: 8333,
            },
            NetworkEndpoint::OnionV3 {
                address: [2; 32],
                port: 8333,
            },
            NetworkEndpoint::I2p {
                address: [3; 32],
                port: 8333,
            },
            NetworkEndpoint::Cjdns {
                address: "fc00::1".parse().unwrap(),
                port: 8333,
            },
        ];
        for endpoint in endpoints {
            let (network, address) = endpoint.to_addr_v2();
            let decoded = NetworkEndpoint::from_addr_v2(network, &address, endpoint.port())
                .expect("valid BIP155 endpoint");
            assert_eq!(decoded, endpoint);
            assert!(!endpoint.host_string().is_empty());
        }
    }

    #[test]
    fn tor_v3_round_trips_with_checksum() {
        let endpoint = NetworkEndpoint::OnionV3 {
            address: [9; 32],
            port: 9735,
        };
        let host = endpoint.host_string();
        assert_eq!(
            NetworkEndpoint::parse(Some("onion"), &host, Some(9735)).unwrap(),
            endpoint
        );
    }

    #[test]
    fn rejects_invalid_bip155_lengths_and_ports() {
        assert!(NetworkEndpoint::from_addr_v2(3, &[0; 9], 8333).is_none());
        assert!(NetworkEndpoint::from_addr_v2(4, &[0; 32], 0).is_none());
        assert!(NetworkEndpoint::parse(Some("i2p"), "abcd", Some(8333)).is_err());
    }
}

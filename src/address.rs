//! Network endpoints used by the address manager and BIP155 ADDRv2.

use std::fmt;
use std::net::{IpAddr, Ipv4Addr, Ipv6Addr, SocketAddr};

use anyhow::{Result, anyhow, bail};
use sha3::{Digest, Sha3_256};

/// A validated endpoint from one of the BIP155 address networks.
///
/// Connected peers normally use [`SocketAddr`], while manual hostname peers
/// retain a `Dns` identity so proxy routing and RPC reporting do not lose the
/// unresolved destination. The address manager keeps the network identity
/// here so Tor, I2P, and CJDNS records survive persistence and relay.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum NetworkEndpoint {
    Ip(SocketAddr),
    Dns { host: String, port: u16 },
    OnionV2 { address: [u8; 10], port: u16 },
    OnionV3 { address: [u8; 32], port: u16 },
    I2p { address: [u8; 32], port: u16 },
    Cjdns { address: Ipv6Addr, port: u16 },
}

impl NetworkEndpoint {
    /// Classify a socket-shaped address for the networks this node can route
    /// directly. Core treats the CJDNS fc00::/8 prefix as a separate network
    /// whenever CJDNS reachability is enabled.
    pub fn from_socket(address: SocketAddr) -> Self {
        match address {
            SocketAddr::V6(address) if is_ipv4_mapped(address.ip()) => Self::Ip(SocketAddr::new(
                IpAddr::V4(mapped_ipv4(address.ip())),
                address.port(),
            )),
            SocketAddr::V6(address) if address.ip().octets()[0] == 0xfc => Self::Cjdns {
                address: *address.ip(),
                port: address.port(),
            },
            address => Self::Ip(address),
        }
    }

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
            6 => {
                let address = <[u8; 16]>::try_from(address).ok()?;
                (address[0] == 0xfc).then(|| Self::Cjdns {
                    address: Ipv6Addr::from(address),
                    port,
                })
            }
            _ => None,
        }
    }

    /// Return the BIP155 network ID and raw address bytes.
    pub fn to_addr_v2(&self) -> Option<(u8, Vec<u8>)> {
        match self {
            Self::Ip(address) => match address.ip() {
                IpAddr::V4(ip) => Some((1, ip.octets().to_vec())),
                IpAddr::V6(ip) => Some((2, ip.octets().to_vec())),
            },
            Self::Dns { .. } => None,
            Self::OnionV2 { address, .. } => Some((3, address.to_vec())),
            Self::OnionV3 { address, .. } => Some((4, address.to_vec())),
            Self::I2p { address, .. } => Some((5, address.to_vec())),
            Self::Cjdns { address, .. } => Some((6, address.octets().to_vec())),
        }
    }

    pub fn port(&self) -> u16 {
        match self {
            Self::Ip(address) => address.port(),
            Self::Dns { port, .. }
            | Self::OnionV2 { port, .. }
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
            Self::Dns { .. } => "not_publicly_routable",
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
            Self::Dns { .. } => None,
            Self::Cjdns { address, port } => Some(SocketAddr::new((*address).into(), *port)),
            Self::OnionV2 { .. } | Self::OnionV3 { .. } | Self::I2p { .. } => None,
        }
    }

    /// Socket-shaped identity used by the legacy peer facade when a remote
    /// endpoint is represented by a hostname rather than an IP literal.
    pub fn peer_socket_addr(&self) -> SocketAddr {
        self.socket_addr()
            .unwrap_or_else(|| SocketAddr::new(Ipv4Addr::UNSPECIFIED.into(), self.port()))
    }

    /// Return a socket address only when the endpoint is valid for legacy
    /// `addr` messages, which have no network discriminator.
    pub fn legacy_socket_addr(&self) -> Option<SocketAddr> {
        match self {
            Self::Ip(address) => Some(*address),
            Self::Dns { .. }
            | Self::OnionV2 { .. }
            | Self::OnionV3 { .. }
            | Self::I2p { .. }
            | Self::Cjdns { .. } => None,
        }
    }

    /// Host portion used by RPC and SOCKS5 domain requests.
    pub fn host_string(&self) -> String {
        match self {
            Self::Ip(address) => address.ip().to_string(),
            Self::Dns { host, .. } => host.clone(),
            Self::OnionV2 { address, .. } => format!("{}.onion", base32_encode(address)),
            Self::OnionV3 { address, .. } => {
                format!("{}.onion", tor_v3_address(address))
            }
            Self::I2p { address, .. } => format!("{}.b32.i2p", base32_encode(address)),
            Self::Cjdns { address, .. } => address.to_string(),
        }
    }

    /// Whether Core's normal proxy selection applies to this endpoint.
    ///
    /// Core maps non-routable IPv4/IPv6 addresses to `NET_UNROUTABLE`, which
    /// bypasses the configured network proxy. Named privacy networks and
    /// CJDNS remain proxyable when a proxy is configured.
    pub fn uses_proxy_by_default(&self) -> bool {
        match self {
            Self::Ip(address) => is_core_routable_ip(address.ip()),
            Self::Dns { .. }
            | Self::OnionV2 { .. }
            | Self::OnionV3 { .. }
            | Self::I2p { .. }
            | Self::Cjdns { .. } => true,
        }
    }

    pub fn requires_proxy(&self) -> bool {
        match self {
            Self::Dns { host, .. } => host.ends_with(".onion") || host.ends_with(".b32.i2p"),
            Self::OnionV2 { .. } | Self::OnionV3 { .. } | Self::I2p { .. } => true,
            Self::Ip(_) | Self::Cjdns { .. } => false,
        }
    }

    /// Construct a hostname endpoint used by manual connections. Hostnames
    /// are intentionally not address-manager entries because ADDRv2 has no
    /// representation for unresolved names.
    pub fn dns(host: String, port: u16) -> Result<Self> {
        if host.is_empty()
            || host.len() > 255
            || host.chars().any(|character| {
                character.is_whitespace() || matches!(character, ':' | '[' | ']' | '/')
            })
        {
            bail!("invalid hostname")
        }
        if port == 0 {
            bail!("network endpoint port must be non-zero")
        }
        Ok(Self::Dns { host, port })
    }

    /// Parse a manual endpoint accepted by Core-style `-connect`/`addnode`
    /// interfaces. Numeric socket addresses retain their explicit port,
    /// numeric IP literals without a port use `default_port`, and hostnames
    /// remain unresolved so a SOCKS5 proxy can receive the original name.
    pub fn parse_manual(value: &str, default_port: u16) -> Result<Self> {
        if default_port == 0 {
            bail!("default network endpoint port must be non-zero")
        }
        if let Ok(address) = value.parse::<SocketAddr>() {
            if address.port() == 0 {
                bail!("network endpoint port must be non-zero")
            }
            return Ok(Self::from_socket(address));
        }
        if let Ok(address) = value.parse::<IpAddr>() {
            return Ok(Self::from_socket(SocketAddr::new(address, default_port)));
        }
        let (host, port) = match value.rsplit_once(':') {
            Some((host, port)) if !host.is_empty() => {
                let port = port
                    .parse::<u16>()
                    .map_err(|error| anyhow!("invalid network address {value}: {error}"))?;
                (host.trim_start_matches('[').trim_end_matches(']'), port)
            }
            None => (value, default_port),
            Some(_) => bail!("invalid network address {value}"),
        };
        Self::dns(host.to_owned(), port)
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
            return Ok(Self::from_socket(socket));
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
            "cjdns" => {
                let address = address.parse::<Ipv6Addr>()?;
                if address.octets()[0] != 0xfc {
                    bail!("invalid CJDNS address prefix")
                }
                Ok(Self::Cjdns { address, port })
            }
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

fn is_ipv4_mapped(address: &Ipv6Addr) -> bool {
    let segments = address.segments();
    segments[..6] == [0, 0, 0, 0, 0, 0xffff]
}

fn mapped_ipv4(address: &Ipv6Addr) -> Ipv4Addr {
    let segments = address.segments();
    Ipv4Addr::new(
        (segments[6] >> 8) as u8,
        segments[6] as u8,
        (segments[7] >> 8) as u8,
        segments[7] as u8,
    )
}

fn is_core_routable_ip(address: IpAddr) -> bool {
    match address {
        IpAddr::V4(address) => {
            let [first, second, third, _] = address.octets();
            !(first == 0
                || first == 127
                || first == 10
                || (first == 172 && (16..=31).contains(&second))
                || (first == 192 && second == 168)
                || (first == 169 && second == 254)
                || (first == 100 && (64..=127).contains(&second))
                || (first == 198 && (second == 18 || second == 19))
                || (first == 192 && second == 0 && third == 2)
                || (first == 198 && second == 51 && third == 100)
                || (first == 203 && second == 0 && third == 113)
                || address.is_broadcast()
                || address.is_multicast())
        }
        IpAddr::V6(address) => {
            let segments = address.segments();
            !(address.is_unspecified()
                || address.is_loopback()
                || address.is_unicast_link_local()
                || address.is_unique_local()
                || address.is_multicast()
                || (segments[0] == 0x2001 && segments[1] == 0x0db8)
                || (segments[0] == 0x2001 && (0x0010..=0x001f).contains(&segments[1]))
                || (segments[0] == 0x2001 && (0x0020..=0x002f).contains(&segments[1])))
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
            Self::Dns { .. } | Self::OnionV2 { .. } | Self::OnionV3 { .. } | Self::I2p { .. } => {
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
            let (network, address) = endpoint.to_addr_v2().unwrap();
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
        assert!(NetworkEndpoint::from_addr_v2(6, &[0xfd; 16], 8333).is_none());
        assert!(NetworkEndpoint::parse(Some("i2p"), "abcd", Some(8333)).is_err());
        assert!(NetworkEndpoint::parse(Some("cjdns"), "fd00::1", Some(8333)).is_err());
    }

    #[test]
    fn classifies_cjdns_socket_addresses() {
        assert_eq!(
            NetworkEndpoint::from_socket("[fc00::1]:8333".parse().unwrap()),
            NetworkEndpoint::Cjdns {
                address: "fc00::1".parse().unwrap(),
                port: 8333,
            }
        );
        assert_eq!(
            NetworkEndpoint::from_socket("[fd00::1]:8333".parse().unwrap()),
            NetworkEndpoint::Ip("[fd00::1]:8333".parse().unwrap())
        );
    }

    #[test]
    fn hostname_endpoints_are_not_bip155_addresses() {
        let endpoint = NetworkEndpoint::dns("example.invalid".to_owned(), 8333).unwrap();
        assert_eq!(endpoint.to_string(), "example.invalid:8333");
        assert_eq!(endpoint.host_string(), "example.invalid");
        assert_eq!(endpoint.socket_addr(), None);
        assert_eq!(endpoint.to_addr_v2(), None);
    }

    #[test]
    fn parses_manual_endpoints_with_default_ports() {
        assert_eq!(
            NetworkEndpoint::parse_manual("192.0.2.1", 18444).unwrap(),
            NetworkEndpoint::Ip("192.0.2.1:18444".parse().unwrap())
        );
        assert_eq!(
            NetworkEndpoint::parse_manual("example.invalid", 18444).unwrap(),
            NetworkEndpoint::Dns {
                host: "example.invalid".to_owned(),
                port: 18444,
            }
        );
        assert_eq!(
            NetworkEndpoint::parse_manual("example.invalid:9735", 18444).unwrap(),
            NetworkEndpoint::Dns {
                host: "example.invalid".to_owned(),
                port: 9735,
            }
        );
        assert!(NetworkEndpoint::parse_manual("example.invalid:0", 18444).is_err());
    }

    #[test]
    fn normalizes_ipv4_mapped_socket_addresses() {
        assert_eq!(
            NetworkEndpoint::from_socket("[::ffff:192.0.2.1]:8333".parse().unwrap()),
            NetworkEndpoint::Ip("192.0.2.1:8333".parse().unwrap())
        );
    }

    #[test]
    fn matches_core_proxy_network_selection() {
        for address in [
            "8.8.8.8:8333",
            "[2001:4860:4860::8888]:8333",
            "[fc00::1]:8333",
        ] {
            let endpoint = NetworkEndpoint::from_socket(address.parse().unwrap());
            assert!(endpoint.uses_proxy_by_default(), "{endpoint}");
        }
        for address in [
            "127.0.0.1:8333",
            "192.168.1.1:8333",
            "192.0.2.1:8333",
            "[::1]:8333",
            "[fe80::1]:8333",
            "[2001:db8::1]:8333",
            "[2001:10::1]:8333",
        ] {
            let endpoint = NetworkEndpoint::from_socket(address.parse().unwrap());
            assert!(!endpoint.uses_proxy_by_default(), "{endpoint}");
        }
    }
}

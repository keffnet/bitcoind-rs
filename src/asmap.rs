//! Core-compatible compressed IP-to-ASN maps used for peer diversity.
//!
//! ASMap files contain a little-endian bitstream of instructions describing a
//! binary trie over 128-bit IP addresses. The instruction arguments use the
//! variable-length encoding from Bitcoin Core's `util/asmap.cpp`.

use std::net::{IpAddr, SocketAddr};
use std::path::Path;

use anyhow::{Context, Result, bail};
use bitcoin::hashes::{Hash, sha256d};

use crate::address::NetworkEndpoint;

/// Internal marker used by configuration to select Core's embedded v31.1 map.
/// It is never treated as a filesystem path.
pub(crate) const EMBEDDED_ASMAP_PATH: &str = "<embedded-asmap-v31.1>";

#[derive(Clone, Debug)]
pub struct AsMap {
    data: Vec<u8>,
    version: [u8; 32],
}

impl AsMap {
    pub fn embedded() -> Result<Self> {
        Self::from_bytes(include_bytes!("data/ip_asn.dat"))
            .context("Could not read embedded asmap data")
    }

    pub fn embedded_len() -> usize {
        include_bytes!("data/ip_asn.dat").len()
    }

    pub fn from_file(path: &Path) -> Result<Self> {
        let data = std::fs::read(path)
            .with_context(|| format!("Could not find asmap file \"{}\"", path.display()))?;
        Self::from_bytes(&data)
            .with_context(|| format!("Could not parse asmap file \"{}\"", path.display()))
    }

    pub fn from_bytes(data: &[u8]) -> Result<Self> {
        if data.is_empty() || !sanity_check(data, 128) {
            bail!("ASMap data failed the 128-bit sanity check");
        }
        let mut version = sha256d::Hash::hash(data).to_byte_array();
        version.reverse();
        Ok(Self {
            data: data.to_owned(),
            version,
        })
    }

    pub fn version_hex(&self) -> String {
        hex::encode(self.version)
    }

    /// Return the mapped ASN, or `None` for non-clearnet/unmapped endpoints.
    pub fn mapped_as(&self, endpoint: &NetworkEndpoint) -> Option<u32> {
        let address = match endpoint {
            NetworkEndpoint::Ip(SocketAddr::V4(address)) => IpAddr::V4(*address.ip()),
            NetworkEndpoint::Ip(SocketAddr::V6(address)) => IpAddr::V6(*address.ip()),
            // Core only uses ASMap for IPv4 and IPv6 address classes. Tor,
            // I2P, CJDNS, and unresolved names retain their normal groups.
            NetworkEndpoint::Dns { .. }
            | NetworkEndpoint::OnionV2 { .. }
            | NetworkEndpoint::OnionV3 { .. }
            | NetworkEndpoint::I2p { .. }
            | NetworkEndpoint::Cjdns { .. } => return None,
        };
        self.mapped_as_ip(address)
    }

    pub fn mapped_as_ip(&self, address: IpAddr) -> Option<u32> {
        let mut bytes = [0u8; 16];
        match address {
            IpAddr::V4(address) => {
                bytes[..12].copy_from_slice(&[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0xff, 0xff]);
                bytes[12..].copy_from_slice(&address.octets());
            }
            IpAddr::V6(address) => bytes = address.octets(),
        }
        interpret(&self.data, &bytes).filter(|asn| *asn != 0)
    }
}

fn read_bit_le(data: &[u8], position: &mut usize) -> Option<bool> {
    let byte = *data.get(*position / 8)?;
    let bit = (byte >> (*position % 8)) & 1;
    *position += 1;
    Some(bit != 0)
}

fn read_bit_be(data: &[u8], position: &mut usize) -> Option<bool> {
    let byte = *data.get(*position / 8)?;
    let bit = (byte >> (7 - (*position % 8))) & 1;
    *position += 1;
    Some(bit != 0)
}

fn decode_bits(data: &[u8], position: &mut usize, minimum: u8, bit_sizes: &[u8]) -> Option<u32> {
    let mut value = u32::from(minimum);
    for (index, bit_size) in bit_sizes.iter().copied().enumerate() {
        let continuation = if index + 1 == bit_sizes.len() {
            false
        } else {
            read_bit_le(data, position)?
        };
        if continuation {
            value = value.checked_add(1u32.checked_shl(u32::from(bit_size))?)?;
            continue;
        }
        for bit in 0..bit_size {
            if read_bit_le(data, position)? {
                value = value.checked_add(1u32 << (bit_size - 1 - bit))?;
            }
        }
        return Some(value);
    }
    None
}

fn decode_type(data: &[u8], position: &mut usize) -> Option<u32> {
    decode_bits(data, position, 0, &[0, 0, 1])
}

fn decode_asn(data: &[u8], position: &mut usize) -> Option<u32> {
    decode_bits(data, position, 1, &[15, 16, 17, 18, 19, 20, 21, 22, 23, 24])
}

fn decode_match(data: &[u8], position: &mut usize) -> Option<u32> {
    decode_bits(data, position, 2, &[1, 2, 3, 4, 5, 6, 7, 8])
}

fn decode_jump(data: &[u8], position: &mut usize) -> Option<u32> {
    decode_bits(
        data,
        position,
        17,
        &[
            5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27,
            28, 29, 30,
        ],
    )
}

fn interpret(data: &[u8], address: &[u8; 16]) -> Option<u32> {
    let end = data.len().saturating_mul(8);
    let mut position = 0usize;
    let mut address_bit = 0usize;
    let mut default_asn = 0u32;
    while position < end {
        match decode_type(data, &mut position)? {
            0 => return decode_asn(data, &mut position),
            1 => {
                let jump = usize::try_from(decode_jump(data, &mut position)?).ok()?;
                if address_bit == 128 || jump >= end.saturating_sub(position) {
                    return None;
                }
                if read_bit_be(address, &mut address_bit)? {
                    position = position.checked_add(jump)?;
                }
            }
            2 => {
                let value = decode_match(data, &mut position)?;
                let match_length = usize::try_from(u32::BITS - value.leading_zeros() - 1).ok()?;
                if match_length > 128usize.saturating_sub(address_bit) {
                    return None;
                }
                for bit in 0..match_length {
                    let expected = ((value >> (match_length - 1 - bit)) & 1) != 0;
                    if read_bit_be(address, &mut address_bit)? != expected {
                        return Some(default_asn);
                    }
                }
            }
            3 => default_asn = decode_asn(data, &mut position)?,
            _ => return None,
        }
    }
    None
}

fn sanity_check(data: &[u8], mut bits: usize) -> bool {
    let end = data.len().saturating_mul(8);
    let mut position = 0usize;
    let mut jumps = Vec::<(usize, usize)>::new();
    let mut previous = 1u32;
    let mut had_incomplete_match = false;

    while position != end {
        if jumps.last().is_some_and(|(target, _)| position >= *target) {
            return false;
        }
        let Some(opcode) = decode_type(data, &mut position) else {
            return false;
        };
        match opcode {
            0 => {
                if previous == 3 || decode_asn(data, &mut position).is_none() {
                    return false;
                }
                if jumps.is_empty() {
                    if end.saturating_sub(position) > 7 {
                        return false;
                    }
                    while position != end {
                        if read_bit_le(data, &mut position) != Some(false) {
                            return false;
                        }
                    }
                    return true;
                }
                let Some((target, remaining_bits)) = jumps.pop() else {
                    return false;
                };
                if position != target {
                    return false;
                }
                bits = remaining_bits;
                previous = 1;
            }
            1 => {
                let Some(jump) =
                    decode_jump(data, &mut position).and_then(|jump| usize::try_from(jump).ok())
                else {
                    return false;
                };
                if jump > end.saturating_sub(position) || bits == 0 {
                    return false;
                }
                bits -= 1;
                let target = position.saturating_add(jump);
                if jumps
                    .last()
                    .is_some_and(|(old_target, _)| target >= *old_target)
                {
                    return false;
                }
                jumps.push((target, bits));
                previous = 1;
            }
            2 => {
                let Some(value) = decode_match(data, &mut position) else {
                    return false;
                };
                let match_length =
                    usize::try_from(u32::BITS - value.leading_zeros() - 1).unwrap_or(usize::MAX);
                if previous != 2 {
                    had_incomplete_match = false;
                }
                if match_length < 8 && had_incomplete_match {
                    return false;
                }
                if bits < match_length {
                    return false;
                }
                bits -= match_length;
                had_incomplete_match = match_length < 8;
                previous = 2;
            }
            3 => {
                if previous == 3 || decode_asn(data, &mut position).is_none() {
                    return false;
                }
                previous = 3;
            }
            _ => return false,
        }
    }
    false
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::net::Ipv4Addr;

    // Bitcoin Core's small artificial map used by its AddrMan tests:
    // 250.0.0.0/8 -> AS1000, and 101.1.0.0/16 through 101.8.0.0/16
    // -> AS1 through AS8.
    const CORE_TEST_MAP: &[u8] = &[
        0xfb, 0x03, 0xec, 0x0f, 0xb0, 0x3f, 0xc0, 0xfe, 0x00, 0xfb, 0x03, 0xec, 0x0f, 0xb0, 0x3f,
        0xc0, 0xfe, 0x00, 0xfb, 0x03, 0xec, 0x0f, 0xb0, 0xff, 0xff, 0xfe, 0xff, 0xed, 0xb0, 0xff,
        0xd4, 0x86, 0xe6, 0x28, 0x29, 0x00, 0x00, 0x40, 0x00, 0x00, 0x40, 0x00, 0x40, 0x99, 0x01,
        0x00, 0x80, 0x01, 0x80, 0x04, 0x00, 0x00, 0x05, 0x00, 0x06, 0x00, 0x1c, 0xf0, 0x39,
    ];

    #[test]
    fn interprets_core_test_map() {
        let map = AsMap::from_bytes(CORE_TEST_MAP).unwrap();
        assert_eq!(map.mapped_as_ip("250.1.1.1".parse().unwrap()), Some(1000));
        assert_eq!(map.mapped_as_ip("101.1.1.1".parse().unwrap()), Some(1));
        assert_eq!(map.mapped_as_ip("101.8.1.1".parse().unwrap()), Some(8));
        assert_eq!(map.mapped_as_ip("101.0.1.1".parse().unwrap()), Some(1));
        assert_eq!(map.mapped_as_ip("1.1.1.1".parse().unwrap()), None);
    }

    #[test]
    fn rejects_empty_and_non_sane_maps() {
        assert!(AsMap::from_bytes(&[]).is_err());
        assert!(AsMap::from_bytes(&[0xff; 8]).is_err());
    }

    #[test]
    fn all_return_map_is_valid() {
        let map = AsMap::from_bytes(&[0, 0, 0]).unwrap();
        assert_eq!(map.mapped_as_ip(IpAddr::V4(Ipv4Addr::LOCALHOST)), Some(1));
    }

    #[test]
    fn embedded_v31_map_is_valid() {
        let map = AsMap::embedded().unwrap();
        assert_eq!(AsMap::embedded_len(), 1_519_688);
        assert!(map.mapped_as_ip("1.1.1.1".parse().unwrap()).is_some());
    }
}

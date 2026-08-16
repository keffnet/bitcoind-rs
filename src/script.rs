//! Small script-classification helpers whose semantics must match Bitcoin Core.
//!
//! rust-bitcoin's convenience predicates are intentionally useful and fast, but
//! a few of them are broader than Core's policy `Solver`. RPC output, standard
//! transaction policy, and BIP37 all expose the narrower Core classification.

use bitcoin::Script;

/// Match Core's `CPubKey::ValidSize` check.
///
/// This is deliberately only a size/prefix check. Core's solver does not
/// validate that the point lies on secp256k1 here; script execution performs
/// the eventual key validation when a signature is checked.
pub(crate) fn is_core_pubkey_size(pubkey: &[u8]) -> bool {
    matches!(
        (pubkey.len(), pubkey.first().copied()),
        (33, Some(0x02 | 0x03)) | (65, Some(0x04 | 0x06 | 0x07))
    )
}

/// Return the parsed bare-multisig threshold and public keys using Core's
/// `MatchMultisig` rules, or `None` when the script is not a Core multisig.
pub(crate) fn core_multisig_solution(script: &Script) -> Option<(u8, Vec<Vec<u8>>)> {
    let operations = parse_operations(script)?;
    if operations.is_empty() || script.as_bytes().last() != Some(&0xae) {
        return None;
    }

    let required = core_script_number(operations.first()?, 1, 20)?;
    let mut index = 1;
    let mut public_keys = Vec::new();
    while let Some(operation) = operations.get(index) {
        if !is_core_pubkey_size(&operation.1) {
            break;
        }
        public_keys.push(operation.1.clone());
        index += 1;
    }

    let public_key_count = core_script_number(operations.get(index)?, required, 20)?;
    if public_keys.len() != usize::from(public_key_count) || index + 2 != operations.len() {
        return None;
    }

    Some((required, public_keys))
}

pub(crate) fn is_core_multisig(script: &Script) -> bool {
    core_multisig_solution(script).is_some()
}

/// Match Core's `MatchPayToPubkey` rules, including its direct-push and key
/// prefix requirements. In particular, non-minimal P2PK pushes are not a
/// solver match.
pub(crate) fn is_core_p2pk(script: &Script) -> bool {
    let bytes = script.as_bytes();
    let key_len = match bytes.len() {
        35 if bytes.first() == Some(&0x21) => 33,
        67 if bytes.first() == Some(&0x41) => 65,
        _ => return false,
    };
    bytes.last() == Some(&0xac) && is_core_pubkey_size(&bytes[1..1 + key_len])
}

/// Parse script operations in the same shape as Core's `CScript::GetOp`.
/// The opcode is retained because Core's numeric parser also enforces minimal
/// push encodings.
fn parse_operations(script: &Script) -> Option<Vec<(u8, Vec<u8>)>> {
    let bytes = script.as_bytes();
    let mut offset = 0usize;
    let mut operations = Vec::new();

    while offset < bytes.len() {
        let opcode = *bytes.get(offset)?;
        offset += 1;
        let length = match opcode {
            0x01..=0x4b => usize::from(opcode),
            0x4c => {
                let length = usize::from(*bytes.get(offset)?);
                offset += 1;
                length
            }
            0x4d => {
                let length = u16::from_le_bytes(bytes.get(offset..offset + 2)?.try_into().ok()?);
                offset += 2;
                usize::from(length)
            }
            0x4e => {
                let length = u32::from_le_bytes(bytes.get(offset..offset + 4)?.try_into().ok()?);
                offset += 4;
                usize::try_from(length).ok()?
            }
            _ => 0,
        };
        let end = offset.checked_add(length)?;
        let data = bytes.get(offset..end)?.to_vec();
        offset = end;
        operations.push((opcode, data));
    }

    Some(operations)
}

/// Core's `GetScriptNumber(opcode, data, min, max)` for the ranges used by
/// `MatchMultisig`.
fn core_script_number(operation: &(u8, Vec<u8>), min: u8, max: u8) -> Option<u8> {
    let (opcode, data) = operation;
    let value = if (0x51..=0x60).contains(opcode) {
        i64::from(*opcode - 0x50)
    } else if (0x01..=0x4e).contains(opcode) && is_minimal_push(*opcode, data) {
        decode_minimal_script_number(data)?
    } else {
        return None;
    };

    u8::try_from(value)
        .ok()
        .filter(|value| (min..=max).contains(value))
}

fn is_minimal_push(opcode: u8, data: &[u8]) -> bool {
    if data.is_empty() {
        return opcode == 0x00;
    }
    if data.len() == 1 {
        let value = data[0];
        if (1..=16).contains(&value) {
            return opcode == 0x50 + value;
        }
        if value == 0x81 {
            return opcode == 0x4f;
        }
    }
    if data.len() <= 75 {
        opcode == data.len() as u8
    } else if data.len() <= u8::MAX as usize {
        opcode == 0x4c
    } else if data.len() <= u16::MAX as usize {
        opcode == 0x4d
    } else {
        opcode == 0x4e
    }
}

fn decode_minimal_script_number(data: &[u8]) -> Option<i64> {
    if data.len() > 4 {
        return None;
    }
    if data.last().is_some_and(|last| {
        last & 0x7f == 0 && (data.len() == 1 || data[data.len() - 2] & 0x80 == 0)
    }) {
        return None;
    }

    let mut value = 0i64;
    for (index, byte) in data.iter().enumerate() {
        value |= i64::from(*byte) << (8 * index);
    }
    if data.last().is_some_and(|last| last & 0x80 != 0) {
        value &= !(0x80i64 << (8 * (data.len() - 1)));
        Some(-value)
    } else {
        Some(value)
    }
}

#[cfg(test)]
mod tests {
    use bitcoin::ScriptBuf;

    use super::{core_multisig_solution, is_core_multisig, is_core_p2pk};

    #[test]
    fn core_p2pk_requires_a_core_key_prefix() {
        let mut script = vec![0x21, 0x02];
        script.extend_from_slice(&[0; 32]);
        script.push(0xac);
        assert!(is_core_p2pk(ScriptBuf::from_bytes(script).as_script()));

        let mut invalid = vec![0x21, 0x05];
        invalid.extend_from_slice(&[0; 32]);
        invalid.push(0xac);
        assert!(!is_core_p2pk(ScriptBuf::from_bytes(invalid).as_script()));
    }

    #[test]
    fn core_multisig_rejects_invalid_key_sizes_and_zero_threshold() {
        let invalid_key = ScriptBuf::from_bytes(vec![0x51, 0x01, 0x01, 0x51, 0xae]);
        assert!(!is_core_multisig(invalid_key.as_script()));

        let zero_threshold = ScriptBuf::from_bytes(vec![0x00, 0x01, 0x01, 0x51, 0xae]);
        assert!(!is_core_multisig(zero_threshold.as_script()));
    }

    #[test]
    fn core_multisig_accepts_valid_size_even_if_point_is_not_valid() {
        let mut script = vec![0x51, 0x21, 0x02];
        script.extend_from_slice(&[0; 32]);
        script.extend_from_slice(&[0x51, 0xae]);
        let solution = core_multisig_solution(ScriptBuf::from_bytes(script).as_script());
        assert_eq!(
            solution.map(|(required, keys)| (required, keys.len())),
            Some((1, 1))
        );
    }
}

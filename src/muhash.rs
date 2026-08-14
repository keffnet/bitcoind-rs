//! Bitcoin Core's MuHash3072 set accumulator.
//!
//! The production Core implementation uses fixed-width limb arithmetic. This
//! module keeps the same wire/hash algorithm while using a big integer for the
//! 3072-bit field element. MuHash is only on the UTXO-statistics path, so this
//! keeps the consensus and RPC implementation straightforward while retaining
//! the important property that insertion/removal order does not matter.

use std::sync::OnceLock;

use bitcoin::hashes::Hash;
use chacha20::ChaCha20;
use chacha20::cipher::{KeyIvInit, StreamCipher};
use num_bigint::BigUint;
use num_traits::One;
use sha2::{Digest, Sha256};

const BYTE_SIZE: usize = 384;
const MODULUS_DIFF: u32 = 1_103_717;

fn modulus() -> &'static BigUint {
    static MODULUS: OnceLock<BigUint> = OnceLock::new();
    MODULUS.get_or_init(|| (BigUint::one() << 3072) - BigUint::from(MODULUS_DIFF))
}

/// A MuHash3072 accumulator represented as a numerator/denominator fraction.
///
/// Keeping removals in the denominator avoids an expensive modular inverse for
/// every deleted UTXO. The inverse is calculated only when `finalize` is called,
/// matching Core's accumulator semantics.
#[derive(Clone, Debug)]
pub struct MuHash3072 {
    numerator: BigUint,
    denominator: BigUint,
}

impl Default for MuHash3072 {
    fn default() -> Self {
        Self {
            numerator: BigUint::one(),
            denominator: BigUint::one(),
        }
    }
}

impl MuHash3072 {
    /// Construct a singleton accumulator from arbitrary bytes.
    pub fn from_bytes(data: &[u8]) -> Self {
        let mut result = Self::default();
        result.insert(data);
        result
    }

    /// Insert one set element.
    pub fn insert(&mut self, data: &[u8]) {
        let element = hash_to_num(data);
        self.numerator = (&self.numerator * element) % modulus();
    }

    /// Remove one set element.
    pub fn remove(&mut self, data: &[u8]) {
        let element = hash_to_num(data);
        self.denominator = (&self.denominator * element) % modulus();
    }

    /// Union this accumulator with another accumulator.
    pub fn combine(&mut self, other: &Self) {
        self.numerator = (&self.numerator * &other.numerator) % modulus();
        self.denominator = (&self.denominator * &other.denominator) % modulus();
    }

    /// Finalize to the conventional Bitcoin hash hex representation.
    pub fn finalize(&self) -> String {
        let exponent = modulus().clone() - BigUint::from(2u8);
        let inverse = self.denominator.modpow(&exponent, modulus());
        let value = (&self.numerator * inverse) % modulus();
        let mut bytes = value.to_bytes_le();
        bytes.resize(BYTE_SIZE, 0);
        let digest = Sha256::digest(bytes);
        let mut internal = [0u8; 32];
        internal.copy_from_slice(&digest);
        // Bitcoin's uint256 stores the SHA-256 digest bytes in memory but
        // renders them in reverse byte order in GetHex()/RPC output.
        internal.reverse();
        bitcoin::hashes::sha256::Hash::from_byte_array(internal).to_string()
    }
}

fn hash_to_num(data: &[u8]) -> BigUint {
    let key = Sha256::digest(data);
    let mut key_bytes = [0u8; 32];
    key_bytes.copy_from_slice(&key);
    let nonce = [0u8; 12];
    let mut stream = [0u8; BYTE_SIZE];
    let mut cipher = ChaCha20::new((&key_bytes).into(), (&nonce).into());
    cipher.apply_keystream(&mut stream);
    BigUint::from_bytes_le(&stream)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn from_int(value: u8) -> MuHash3072 {
        let mut data = [0u8; 32];
        data[0] = value;
        MuHash3072::from_bytes(&data)
    }

    #[test]
    fn matches_core_muhash_arithmetic_vector() {
        // This is Core's 0 / 2 vector. The singleton input is the 32-byte
        // value {2, 0, ...}.
        let mut quotient = from_int(0);
        quotient.combine(&from_int(1));
        let mut two = [0u8; 32];
        two[0] = 2;
        quotient.remove(&two);
        assert_eq!(
            quotient.finalize(),
            "10d312b100cbd32ada024a6646e40d3482fcff103668d2625f10002a607d5863"
        );
    }

    #[test]
    fn insertion_and_removal_are_order_independent() {
        let mut left = MuHash3072::default();
        left.insert(b"a");
        left.insert(b"b");
        let mut right = MuHash3072::default();
        right.insert(b"b");
        right.insert(b"a");
        assert_eq!(left.finalize(), right.finalize());

        left.remove(b"a");
        right.remove(b"a");
        assert_eq!(left.finalize(), right.finalize());
    }
}

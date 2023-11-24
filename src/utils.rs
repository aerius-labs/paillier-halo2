use halo2_proofs::{dev::VerifyFailure, plonk::Error};
use num_bigint::{BigUint, RandomBits};
use rand::{thread_rng, Rng};
use std::fmt;

pub enum CircuitError {
    /// Thrown when `MockProver::run` fails to prove the circuit.
    ProverError(Error),
    /// Thrown when verification fails.
    VerifierError(Vec<VerifyFailure>),
}

impl fmt::Debug for CircuitError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            CircuitError::ProverError(prover_error) => {
                write!(f, "prover error in circuit: {prover_error}")
            }
            CircuitError::VerifierError(verifier_error) => {
                write!(f, "verifier error in circuit: {verifier_error:#?}")
            }
        }
    }
}

/// # random BigUint x-bits long
/// returns a BigUint with bit length = bit_length
pub fn get_random_x_bit_bn(bit_length: usize) -> BigUint {
    let mut rng = thread_rng();
    let mut b = BigUint::default();
    while b.bits() != (bit_length as u64) {
        b = rng.sample(RandomBits::new(bit_length as u64));
    }
    b
}

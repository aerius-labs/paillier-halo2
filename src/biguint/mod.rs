pub mod chip;

use halo2_base::{ utils::BigPrimeField, halo2_proofs::circuit::Value, AssignedValue };
use halo2_ecc::bigint::OverflowInteger;
use num_bigint::BigUint;

#[derive(Debug, Clone)]
pub struct AssignedBigUint<F: BigPrimeField> {
    int: OverflowInteger<F>,
    value: Value<BigUint>,
}

impl<F: BigPrimeField> AssignedBigUint<F> {
    pub fn new(int: OverflowInteger<F>, value: Value<BigUint>) -> Self {
        Self { int, value }
    }

    pub fn int_ref(&self) -> &OverflowInteger<F> {
        &self.int
    }

    pub fn value(&self) -> Value<BigUint> {
        self.value.clone()
    }

    pub fn num_limbs(&self) -> usize {
        self.int.limbs.len()
    }

    pub fn extend_limbs(&self, num_extend_limbs: usize, zero_value: AssignedValue<F>) -> Self {
        let max_limb_bits = self.int_ref().max_limb_bits;
        let pre_num_limbs = self.num_limbs();
        let mut limbs = self.int.limbs.clone();
        for _ in 0..num_extend_limbs {
            limbs.push(zero_value.clone());
        }
        assert_eq!(pre_num_limbs + num_extend_limbs, limbs.len());
        let int = OverflowInteger::new(limbs, max_limb_bits);
        Self::new(int, self.value())
    }
}

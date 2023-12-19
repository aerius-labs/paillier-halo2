use halo2_base::{
    utils::{ BigPrimeField, decompose_biguint },
    gates::{ RangeChip, RangeInstructions },
    Context,
    halo2_proofs::{ circuit::Value, plonk::Error },
};
use halo2_ecc::bigint::{ OverflowInteger, mul_no_carry };
use num_bigint::BigUint;

use super::{ AssignedBigUint, Fresh, Muled };

#[derive(Clone, Debug)]
pub struct BigUintChip<F: BigPrimeField> {
    pub range: RangeChip<F>,
    pub limb_bits: usize,
}

impl<F: BigPrimeField> BigUintChip<F> {
    pub fn construct(range: RangeChip<F>, limb_bits: usize) -> Self {
        Self { range, limb_bits }
    }

    pub fn range(&self) -> &RangeChip<F> {
        &self.range
    }

    pub fn limb_bits(&self) -> usize {
        self.limb_bits
    }

    pub fn bits_size(val: &BigUint) -> usize {
        val.bits() as usize
    }

    pub fn num_limbs(&self, val: &BigUint) -> usize {
        let bits = Self::bits_size(&val);
        let num_limbs = if bits % self.limb_bits == 0 {
            bits / self.limb_bits
        } else {
            bits / self.limb_bits + 1
        };
        num_limbs
    }

    pub fn assign_integer(
        &self,
        ctx: &mut Context<F>,
        value: BigUint,
        bit_len: usize
    ) -> Result<AssignedBigUint<F, Fresh>, Error> {
        assert_eq!(bit_len % self.limb_bits, 0);
        let num_limbs = bit_len / self.limb_bits;
        let limbs = decompose_biguint::<F>(&value, num_limbs, self.limb_bits);
        let assigned_limbs = ctx.assign_witnesses(limbs);
        for limb in assigned_limbs.iter() {
            self.range().range_check(ctx, *limb, self.limb_bits);
        }
        let int = OverflowInteger::new(assigned_limbs, self.limb_bits);
        Ok(AssignedBigUint::new(int, Value::known(value.clone())))
    }

    pub fn assign_constant(
        &self,
        ctx: &mut Context<F>,
        value: BigUint
    ) -> Result<AssignedBigUint<F, Fresh>, Error> {
        let num_limbs = self.num_limbs(&value);
        let limbs = decompose_biguint::<F>(&value, num_limbs, self.limb_bits);
        let assigned_limbs = ctx.assign_witnesses(limbs);
        let int = OverflowInteger::new(assigned_limbs, self.limb_bits);
        Ok(AssignedBigUint::new(int, Value::known(value.clone())))
    }

    pub fn mul(
        &self,
        ctx: &mut Context<F>,
        a: &AssignedBigUint<F, Fresh>,
        b: &AssignedBigUint<F, Fresh>
    ) -> Result<AssignedBigUint<F, Muled>, Error> {
        let n1 = a.num_limbs();
        let n2 = b.num_limbs();
        let num_limbs = n1 + n2 - 1;
        let zero_value = ctx.load_zero();
        let a = a.extend_limbs(num_limbs - n1, zero_value);
        let b = b.extend_limbs(num_limbs - n2, zero_value);
        let num_limbs_log2_ceil = (num_limbs as f32).log2().ceil() as usize;
        let int = mul_no_carry::truncate(
            self.range().gate(),
            ctx,
            a.int,
            b.int,
            num_limbs_log2_ceil
        );
        let value = a.value.zip(b.value).map(|(a, b)| a * b);
        Ok(AssignedBigUint::new(int, value))
    }
}

#[cfg(test)]
mod test {
    use halo2_base::{
        gates::circuit::{ builder::RangeCircuitBuilder, CircuitBuilderStage },
        halo2_proofs::{ halo2curves::grumpkin::Fq as Fr, circuit::Value },
    };
    use num_bigint::RandBigInt;
    use rand::thread_rng;

    use super::BigUintChip;

    #[test]
    fn test_mul() {
        const NUM_BIT_LEN: usize = 256;
        const LIMB_BIT_LEN: usize = 64;

        let mut rng = thread_rng();

        let mut builder = RangeCircuitBuilder::<Fr>
            ::from_stage(CircuitBuilderStage::Mock)
            .use_k(13 as usize)
            .use_lookup_bits(10);
        let range = builder.range_chip();

        let big_uint_chip = BigUintChip::construct(range, LIMB_BIT_LEN);

        let ctx = builder.main(0);

        let a = rng.gen_biguint(NUM_BIT_LEN as u64);
        let b = rng.gen_biguint(NUM_BIT_LEN as u64);

        let a_assigned = big_uint_chip.assign_integer(ctx, a.clone(), NUM_BIT_LEN).unwrap();
        let b_assigned = big_uint_chip.assign_integer(ctx, b.clone(), NUM_BIT_LEN).unwrap();

        let c_assigned = big_uint_chip.mul(ctx, &a_assigned, &b_assigned).unwrap();

        let res = a.clone() * b.clone();

        c_assigned
            .value()
            .zip(Value::known(res.clone()))
            .map(|(a, b)| {
                assert_eq!(a, b);
            });
    }
}

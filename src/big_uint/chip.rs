use halo2_base::{
    utils::{ BigPrimeField, decompose_biguint, fe_to_biguint, biguint_to_fe },
    gates::{ RangeChip, RangeInstructions, GateInstructions },
    Context,
    halo2_proofs::{ circuit::Value, plonk::Error },
    AssignedValue,
    QuantumCell,
};
use halo2_ecc::bigint::{ OverflowInteger, mul_no_carry, big_is_zero };
use num_bigint::BigUint;

use super::{ AssignedBigUint, Fresh, Muled, RefreshAux };

#[derive(Clone, Debug)]
pub struct BigUintChip<'a, F: BigPrimeField> {
    pub range: &'a RangeChip<F>,
    pub limb_bits: usize,
}

impl<'a, F: BigPrimeField> BigUintChip<'a, F> {
    pub fn construct(range: &'a RangeChip<F>, limb_bits: usize) -> Self {
        Self { range, limb_bits }
    }

    pub fn range(&self) -> &'a RangeChip<F> {
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

    // TODO - check if can remove this
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

    /// Returns an assigned bit representing whether `a` is zero or not.
    pub fn is_zero(
        &self,
        ctx: &mut Context<F>,
        a: &AssignedBigUint<F, Fresh>
    ) -> Result<AssignedValue<F>, Error> {
        let out = big_is_zero::positive(self.range.gate(), ctx, a.int.clone());
        Ok(out)
    }

    /// Returns an assigned bit representing whether `a` and `b` are equivalent, whose [`RangeType`] is [`Fresh`].
    pub fn is_equal_fresh(
        &self,
        ctx: &mut Context<F>,
        a: &AssignedBigUint<F, Fresh>,
        b: &AssignedBigUint<F, Fresh>
    ) -> Result<AssignedValue<F>, Error> {
        let gate = self.range.gate();
        let a_limbs = a.int.limbs.clone();
        let b_limbs = b.int.limbs.clone();
        assert_eq!(a_limbs.len(), b_limbs.len());
        let mut partial = gate.is_equal(ctx, a_limbs[0], b_limbs[0]);
        for (a_limb, b_limb) in a_limbs.iter().zip(b_limbs.iter()) {
            let eq_limb = gate.is_equal(ctx, *a_limb, *b_limb);
            partial = gate.and(ctx, eq_limb, partial);
        }
        Ok(partial)
    }

    /// Assert that an assigned bit representing whether `a` and `b` are equivalent, whose [`RangeType`] is [`Fresh`].
    pub fn assert_equal_fresh(
        &self,
        ctx: &mut Context<F>,
        a: &AssignedBigUint<F, Fresh>,
        b: &AssignedBigUint<F, Fresh>
    ) -> Result<(), Error> {
        let result = self.is_equal_fresh(ctx, a, b)?;
        self.range.gate().assert_is_const(ctx, &result, &F::ONE);
        Ok(())
    }

    pub fn refresh(
        &self,
        ctx: &mut Context<F>,
        a: &AssignedBigUint<F, Muled>,
        aux: &RefreshAux
    ) -> Result<AssignedBigUint<F, Fresh>, Error> {
        let gate = self.range.gate();

        // For converting `a` to a [`Fresh`] type integer, we decompose each limb of `a` into `self.limb_width`-bits values.
        assert_eq!(self.limb_bits, aux.limb_bits);
        // The i-th value of `aux.increased_limbs_vec` represents the number of increased values when converting i-th limb of `a` into `self.limb_width`-bits values.
        let increased_limbs_vec = aux.increased_limbs_vec.clone();
        let num_limbs_l = aux.num_limbs_l;
        let num_limbs_r = aux.num_limbs_r;
        // The following assertion holds since `a` is the product of two integers `l` and `r` whose number of limbs is `num_limbs_l` and `num_limbs_r`, respectively.
        assert_eq!(a.num_limbs(), num_limbs_l + num_limbs_r - 1);
        let num_limbs_fresh = increased_limbs_vec.len();

        let mut refreshed_limbs = Vec::with_capacity(num_limbs_fresh);
        let zero_assigned = ctx.load_zero();
        let a_limbs = a.limbs();
        for i in 0..a.num_limbs() {
            refreshed_limbs.push(a_limbs[i].clone());
        }
        for _ in 0..num_limbs_fresh - a.num_limbs() {
            refreshed_limbs.push(zero_assigned.clone());
        }
        let limb_max = BigUint::from(1u64) << self.limb_bits;
        for i in 0..num_limbs_fresh {
            // `i`-th overflowing limb value.
            let mut limb = refreshed_limbs[i].clone();
            for j in 0..increased_limbs_vec[i] + 1 {
                // `n` is lower `self.limb_width` bits of `limb`.
                // `q` is any other upper bits.
                let (q, n) = self.div_mod_unsafe(ctx, &limb, &limb_max);
                if j == 0 {
                    // When `j=0`, `n` is a new `i`-th limb value.
                    refreshed_limbs[i] = n;
                } else {
                    // When `j>0`, `n` is carried to the `i+j`-th limb.
                    refreshed_limbs[i + j] = gate.add(
                        ctx,
                        QuantumCell::Existing(refreshed_limbs[i + j]),
                        QuantumCell::Existing(n)
                    );
                }
                // We use `q` as the next `limb`.
                limb = q;
            }
            // `limb` should be zero because we decomposed all bits of the `i`-th overflowing limb value into `self.limb_width` bits values.
            gate.assert_is_const(ctx, &limb, &F::ZERO);
        }
        let range = self.range();
        for limb in refreshed_limbs.iter() {
            range.range_check(ctx, *limb, self.limb_bits);
        }
        let int = OverflowInteger::new(refreshed_limbs, self.limb_bits);
        let new_assigned_int = AssignedBigUint::new(int, a.value());
        Ok(new_assigned_int)
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

    pub fn div_mod_unsafe(
        &self,
        ctx: &mut Context<F>,
        a: &AssignedValue<F>,
        b: &BigUint
    ) -> (AssignedValue<F>, AssignedValue<F>) {
        let gate = self.range.gate();

        let a_big = fe_to_biguint(a.value());
        let (q_big, r_big) = (a_big.clone() / b, a_big.clone() % b);

        let (q_val, r_val) = (biguint_to_fe::<F>(&q_big), biguint_to_fe::<F>(&r_big));

        let (q, r) = (ctx.load_witness(q_val), ctx.load_witness(r_val));
        let prod = gate.mul(ctx, QuantumCell::Existing(q), QuantumCell::Constant(biguint_to_fe(b)));
        let a_prod_sub = gate.sub(ctx, QuantumCell::Existing(*a), QuantumCell::Existing(prod));
        let is_eq = gate.is_equal(ctx, QuantumCell::Existing(r), QuantumCell::Existing(a_prod_sub));
        gate.assert_is_const(ctx, &is_eq, &F::ONE);
        (q, r)
    }
}

#[cfg(test)]
mod test {
    use halo2_base::{
        gates::RangeChip,
        halo2_proofs::circuit::Value,
        Context,
        utils::{ BigPrimeField, testing::base_test },
    };
    use num_bigint::{ RandBigInt, BigUint };
    use rand::thread_rng;

    use crate::big_uint::RefreshAux;

    use super::BigUintChip;

    #[test]
    fn test_mul() {
        const NUM_BIT_LEN: usize = 264;
        const LIMB_BIT_LEN: usize = 88;

        let mut rng = thread_rng();

        fn mul_circuit<F: BigPrimeField>(
            ctx: &mut Context<F>,
            range: &RangeChip<F>,
            num_bit_len: usize,
            limb_bit_len: usize,
            a: BigUint,
            b: BigUint,
            res: BigUint
        ) {
            let chip = BigUintChip::construct(range, limb_bit_len);

            let a_assigned = chip.assign_integer(ctx, a.clone(), num_bit_len).unwrap();
            let b_assigned = chip.assign_integer(ctx, b.clone(), num_bit_len).unwrap();

            let c_assigned = chip.mul(ctx, &a_assigned, &b_assigned).unwrap();
            let aux = RefreshAux::new(limb_bit_len, a_assigned.num_limbs(), b_assigned.num_limbs());
            let c_assigned = chip.refresh(ctx, &c_assigned, &aux).unwrap();

            let res_assigned = chip.assign_integer(ctx, res.clone(), num_bit_len * 2).unwrap();

            c_assigned
                .value()
                .zip(Value::known(res.clone()))
                .map(|(a, b)| {
                    assert_eq!(a, b);
                });
            chip.assert_equal_fresh(ctx, &c_assigned, &res_assigned).unwrap();
        }

        base_test()
            .k(13)
            .lookup_bits(12)
            .expect_satisfied(true)
            .run(|ctx, chip| {
                let a = rng.gen_biguint(NUM_BIT_LEN as u64);
                let b = rng.gen_biguint(NUM_BIT_LEN as u64);
                let res = a.clone() * b.clone();
                mul_circuit(ctx, chip, NUM_BIT_LEN, LIMB_BIT_LEN, a, b, res);
            })
    }
}

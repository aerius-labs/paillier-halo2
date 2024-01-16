use halo2_base::{
    gates::{GateInstructions, RangeChip, RangeInstructions},
    halo2_proofs::{circuit::Value, plonk::Error},
    utils::{biguint_to_fe, decompose_biguint, fe_to_biguint, BigPrimeField},
    AssignedValue, Context, QuantumCell,
};
use halo2_ecc::bigint::{big_is_zero, mul_no_carry, OverflowInteger};
use num_bigint::BigUint;

use super::{AssignedBigUint, Fresh, Muled, RefreshAux};

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
        self.range
    }

    pub fn limb_bits(&self) -> usize {
        self.limb_bits
    }

    pub fn bits_size(val: &BigUint) -> usize {
        val.bits() as usize
    }

    pub fn num_limbs(&self, val: &BigUint) -> usize {
        let bits = Self::bits_size(val);
        if bits % self.limb_bits == 0 {
            bits / self.limb_bits
        } else {
            bits / self.limb_bits + 1
        }
    }

    /// Returns the maximum limb size of [`Muled`] type integers.
    fn compute_muled_limb_max(limb_width: usize, min_n: usize) -> BigUint {
        let one = BigUint::from(1usize);
        let out_base = BigUint::from(1usize) << limb_width;
        BigUint::from(min_n) * (&out_base - &one) * (&out_base - &one) + (&out_base - &one)
    }

    pub fn assign_integer(
        &self,
        ctx: &mut Context<F>,
        value: Value<BigUint>,
        bit_len: usize,
    ) -> Result<AssignedBigUint<F, Fresh>, Error> {
        assert_eq!(bit_len % self.limb_bits, 0);
        let num_limbs = bit_len / self.limb_bits;
        let limbs = value
            .as_ref()
            .map(|v| decompose_biguint::<F>(v, num_limbs, self.limb_bits))
            .transpose_vec(num_limbs);
        let mut assigned_limbs = Vec::new();
        for limb in limbs.iter() {
            limb.map(|l| assigned_limbs.push(ctx.load_witness(l)));
        }
        for limb in assigned_limbs.iter() {
            self.range().range_check(ctx, *limb, self.limb_bits);
        }
        let int = OverflowInteger::new(assigned_limbs, self.limb_bits);
        Ok(AssignedBigUint::new(int, value.clone()))
    }

    // TODO - check if can remove this
    pub fn assign_constant(
        &self,
        ctx: &mut Context<F>,
        value: BigUint,
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
        a: &AssignedBigUint<F, Fresh>,
    ) -> Result<AssignedValue<F>, Error> {
        let out = big_is_zero::positive(self.range.gate(), ctx, a.int.clone());
        Ok(out)
    }

    /// Returns an assigned bit representing whether `a` and `b` are equivalent, whose [`RangeType`] is [`Fresh`].
    pub fn is_equal_fresh(
        &self,
        ctx: &mut Context<F>,
        a: &AssignedBigUint<F, Fresh>,
        b: &AssignedBigUint<F, Fresh>,
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

    /// Returns an assigned bit representing whether `a` and `b` are equivalent, whose [`RangeType`] is [`Muled`].
    pub fn is_equal_muled(
        &self,
        ctx: &mut Context<F>,
        a: &AssignedBigUint<F, Muled>,
        b: &AssignedBigUint<F, Muled>,
        num_limbs_l: usize,
        num_limbs_r: usize,
    ) -> Result<AssignedValue<F>, Error> {
        // The following constraints are designed with reference to EqualWhenCarried template in https://github.com/jacksoom/circom-bigint/blob/master/circuits/mult.circom.
        // We use lookup tables to optimize range checks.
        let min_n = if num_limbs_r >= num_limbs_l {
            num_limbs_l
        } else {
            num_limbs_r
        };
        // Each limb of `a` and `b` is less than `min_n * (1^(limb_bits) - 1)^2  + (1^(limb_bits) - 1)`.
        let muled_limb_max = Self::compute_muled_limb_max(self.limb_bits, min_n);
        let muled_limb_max_fe = biguint_to_fe::<F>(&muled_limb_max);
        let num_limbs = num_limbs_l + num_limbs_r - 1;
        let muled_limb_max_bits = Self::bits_size(&(&muled_limb_max * 2u32));
        let carry_bits = muled_limb_max_bits - self.limb_bits;
        let gate = self.range.gate();
        let range = self.range();

        // The naive approach is to subtract the two integers limb by limb and:
        //  a. Verify that they sum to zero along the way while
        //  b. Propagating carries
        // but this doesn't work because early sums might be negative.
        // So instead we verify that `a - b + word_max = word_max`.
        let limb_max = BigUint::from(1u64) << self.limb_bits;
        let zero = ctx.load_zero();
        let mut accumulated_extra = zero;
        let mut carry = Vec::with_capacity(num_limbs);
        let mut cs = Vec::with_capacity(num_limbs);
        carry.push(zero);
        let mut eq_bit = ctx.load_constant(F::ONE);
        let a_limbs = a.limbs();
        let b_limbs = b.limbs();
        for i in 0..num_limbs {
            // `sum = a - b + word_max`
            let a_b_sub = gate.sub(
                ctx,
                QuantumCell::Existing(a_limbs[i]),
                QuantumCell::Existing(b_limbs[i]),
            );
            let sum = gate.sum(
                ctx,
                vec![
                    QuantumCell::Existing(a_b_sub),
                    QuantumCell::Existing(carry[i]),
                    QuantumCell::Constant(muled_limb_max_fe),
                ],
            );
            // `c` is lower `self.limb_width` bits of `sum`.
            // `new_carry` is any other upper bits.
            let (new_carry, c) = self.div_mod_unsafe(ctx, &sum, &limb_max);
            carry.push(new_carry);
            cs.push(c);

            // `accumulated_extra` is the sum of `word_max`.
            accumulated_extra = gate.add(
                ctx,
                QuantumCell::Existing(accumulated_extra),
                QuantumCell::Constant(muled_limb_max_fe),
            );
            let (q_acc, mod_acc) = self.div_mod_unsafe(ctx, &accumulated_extra, &limb_max);
            // If and only if `a` is equal to `b`, lower `self.limb_width` bits of `sum` and `accumulated_extra` are the same.
            let cs_acc_eq = gate.is_equal(
                ctx,
                QuantumCell::Existing(cs[i]),
                QuantumCell::Existing(mod_acc),
            );
            eq_bit = gate.and(
                ctx,
                QuantumCell::Existing(eq_bit),
                QuantumCell::Existing(cs_acc_eq),
            );
            accumulated_extra = q_acc;

            if i < num_limbs - 1 {
                // Assert that each carry fits in `carry_bits` bits.
                range.range_check(ctx, carry[i + 1], carry_bits);
            } else {
                // The final carry should match the `accumulated_extra`.
                let final_carry_eq = gate.is_equal(
                    ctx,
                    QuantumCell::Existing(carry[i + 1]),
                    QuantumCell::Existing(accumulated_extra),
                );
                eq_bit = gate.and(
                    ctx,
                    QuantumCell::Existing(eq_bit),
                    QuantumCell::Existing(final_carry_eq),
                );
            }
        }
        Ok(eq_bit)
    }

    /// Assert that an assigned bit representing whether `a` and `b` are equivalent, whose [`RangeType`] is [`Fresh`].
    pub fn assert_equal_fresh(
        &self,
        ctx: &mut Context<F>,
        a: &AssignedBigUint<F, Fresh>,
        b: &AssignedBigUint<F, Fresh>,
    ) -> Result<(), Error> {
        let result = self.is_equal_fresh(ctx, a, b)?;
        self.range.gate().assert_is_const(ctx, &result, &F::ONE);
        Ok(())
    }

    pub fn refresh(
        &self,
        ctx: &mut Context<F>,
        a: &AssignedBigUint<F, Muled>,
        aux: &RefreshAux,
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
        for limb in a_limbs.iter().take(a.num_limbs()) {
            refreshed_limbs.push(*limb);
        }
        for _ in 0..num_limbs_fresh - a.num_limbs() {
            refreshed_limbs.push(zero_assigned);
        }
        let limb_max = BigUint::from(1u64) << self.limb_bits;
        for i in 0..num_limbs_fresh {
            // `i`-th overflowing limb value.
            let mut limb = refreshed_limbs[i];
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
                        QuantumCell::Existing(n),
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
        b: &AssignedBigUint<F, Fresh>,
    ) -> Result<AssignedBigUint<F, Muled>, Error> {
        let n1 = a.num_limbs();
        let n2 = b.num_limbs();
        let num_limbs = n1 + n2 - 1;
        let zero_value = ctx.load_zero();
        let a = a.extend_limbs(num_limbs - n1, zero_value);
        let b = b.extend_limbs(num_limbs - n2, zero_value);
        let num_limbs_log2_ceil = (num_limbs as f32).log2().ceil() as usize;
        let int =
            mul_no_carry::truncate(self.range().gate(), ctx, a.int, b.int, num_limbs_log2_ceil);
        let value = a.value.zip(b.value).map(|(a, b)| a * b);
        Ok(AssignedBigUint::new(int, value))
    }

    pub fn square(
        &self,
        ctx: &mut Context<F>,
        a: &AssignedBigUint<F, Fresh>,
    ) -> Result<AssignedBigUint<F, Muled>, Error> {
        self.mul(ctx, a, a)
    }

    pub fn div_mod_unsafe(
        &self,
        ctx: &mut Context<F>,
        a: &AssignedValue<F>,
        b: &BigUint,
    ) -> (AssignedValue<F>, AssignedValue<F>) {
        let gate = self.range.gate();

        let a_big = fe_to_biguint(a.value());
        let (q_big, r_big) = (a_big.clone() / b, a_big.clone() % b);

        let (q_val, r_val) = (biguint_to_fe::<F>(&q_big), biguint_to_fe::<F>(&r_big));

        let (q, r) = (ctx.load_witness(q_val), ctx.load_witness(r_val));
        let prod = gate.mul(
            ctx,
            QuantumCell::Existing(q),
            QuantumCell::Constant(biguint_to_fe(b)),
        );
        let a_prod_sub = gate.sub(ctx, QuantumCell::Existing(*a), QuantumCell::Existing(prod));
        let is_eq = gate.is_equal(
            ctx,
            QuantumCell::Existing(r),
            QuantumCell::Existing(a_prod_sub),
        );
        gate.assert_is_const(ctx, &is_eq, &F::ONE);
        (q, r)
    }

    /// Given two inputs `a,b` and a modulus `n`, performs the modular multiplication `a * b mod n`.
    ///
    /// # Arguments
    /// * `ctx` - a region context.
    /// * `a` - input of multiplication.
    /// * `b` - input of multiplication.
    /// * `n` - a modulus.
    ///
    /// # Return values
    /// Returns the modular multiplication result `a * b mod n` as [`AssignedInteger<F, Fresh>`].
    /// # Requirements
    /// Before calling this function, you must assert that `a<n` and `b<n`.
    pub fn mul_mod(
        &self,
        ctx: &mut Context<F>,
        a: &AssignedBigUint<F, Fresh>,
        b: &AssignedBigUint<F, Fresh>,
        n: &AssignedBigUint<F, Fresh>,
    ) -> Result<AssignedBigUint<F, Fresh>, Error> {
        // The following constraints are designed with reference to AsymmetricMultiplierReducer template in https://github.com/jacksoom/circom-bigint/blob/master/circuits/mult.circom.
        // However, we do not regroup multiple limbs like the circom-bigint implementation because addition is not free, i.e., it makes constraints as well as multiplication, in the Plonk constraints system.
        // Besides, we use lookup tables to optimize range checks.
        let limb_bits = self.limb_bits;
        let n1 = a.num_limbs();
        let n2 = b.num_limbs();
        assert_eq!(n1, n.num_limbs());
        let (a_big, b_big, n_big) = (a.value(), b.value(), n.value());
        // 1. Compute the product as `BigUint`.
        let full_prod_big = a_big * b_big;
        // 2. Compute the quotient and remainder when the product is divided by `n`.
        let (q_big, prod_big) = full_prod_big
            .zip(n_big.as_ref())
            .map(|(full_prod, n)| (&full_prod / n, &full_prod % n))
            .unzip();

        // 3. Assign the quotient and remainder after checking the range of each limb.
        let assign_q = self.assign_integer(ctx, q_big, n2 * limb_bits)?;
        let assign_n = self.assign_integer(ctx, n_big, n1 * limb_bits)?;
        let assign_prod = self.assign_integer(ctx, prod_big, n1 * limb_bits)?;
        // 4. Assert `a * b = quotient_int * n + prod_int`, i.e., `prod_int = (a * b) mod n`.
        let ab = self.mul(ctx, a, b)?;
        let qn = self.mul(ctx, &assign_q, &assign_n)?;
        let gate = self.range.gate();
        let n_sum = n1 + n2;
        let qn_prod = {
            let value = qn
                .value
                .as_ref()
                .zip(assign_prod.value.as_ref())
                .map(|(a, b)| a + b);
            let mut limbs = Vec::with_capacity(n1 + n2 - 1);
            let qn_limbs = qn.limbs();
            let prod_limbs = assign_prod.limbs();
            for i in 0..n_sum - 1 {
                if i < n1 {
                    limbs.push(gate.add(
                        ctx,
                        QuantumCell::Existing(qn_limbs[i]),
                        QuantumCell::Existing(prod_limbs[i]),
                    ));
                } else {
                    limbs.push(qn_limbs[i]);
                }
            }
            let int = OverflowInteger::new(limbs, self.limb_bits);
            AssignedBigUint::<F, Muled>::new(int, value)
        };
        let is_eq = self.is_equal_muled(ctx, &ab, &qn_prod, n1, n2)?;
        gate.assert_is_const(ctx, &is_eq, &F::ONE);
        Ok(assign_prod)
    }

    /// Given a input `a` and a modulus `n`, performs the modular square `a^2 mod n`.
    pub fn square_mod(
        &self,
        ctx: &mut Context<F>,
        a: &AssignedBigUint<F, Fresh>,
        n: &AssignedBigUint<F, Fresh>,
    ) -> Result<AssignedBigUint<F, Fresh>, Error> {
        self.mul_mod(ctx, a, a, n)
    }

    /// Given a base `a`, a fixed exponent `e`, and a modulus `n`, performs the modular power `a^e mod n`.
    pub fn pow_mod_fixed_exp(
        &self,
        ctx: &mut Context<F>,
        a: &AssignedBigUint<F, Fresh>,
        e: &BigUint,
        n: &AssignedBigUint<F, Fresh>,
    ) -> Result<AssignedBigUint<F, Fresh>, Error> {
        let num_limbs = a.num_limbs();
        assert_eq!(num_limbs, n.num_limbs());
        let num_e_bits = Self::bits_size(e);
        // Decompose `e` into bits.
        let e_bits = e
            .to_bytes_le()
            .into_iter()
            .flat_map(|v| {
                (0..8)
                    .map(|i: u8| ((v >> i) & 1u8) == 1u8)
                    .collect::<Vec<bool>>()
            })
            .collect::<Vec<bool>>();
        let e_bits = e_bits[0..num_e_bits].to_vec();
        let mut acc = self.assign_constant(ctx, BigUint::from(1usize))?;
        let zero = ctx.load_zero();
        acc = acc.extend_limbs(num_limbs - acc.num_limbs(), zero);
        let mut squared: AssignedBigUint<F, Fresh> = a.clone();
        for e_bit in e_bits.into_iter() {
            let cur_sq = squared;
            // Square `squared`.
            squared = self.square_mod(ctx, &cur_sq, n)?;
            if !e_bit {
                continue;
            }
            // If `e_bit = 1`, update `acc` to `acc * cur_sq`.
            acc = self.mul_mod(ctx, &acc, &cur_sq, n)?;
        }
        Ok(acc)
    }
}

#[cfg(test)]
mod test {
    use halo2_base::{
        gates::RangeChip,
        halo2_proofs::circuit::Value,
        utils::{testing::base_test, BigPrimeField},
        Context,
    };
    use num_bigint::{BigUint, RandBigInt};
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
            res: BigUint,
        ) {
            let chip = BigUintChip::construct(range, limb_bit_len);

            let a_assigned = chip
                .assign_integer(ctx, Value::known(a.clone()), num_bit_len)
                .unwrap();
            let b_assigned = chip
                .assign_integer(ctx, Value::known(b.clone()), num_bit_len)
                .unwrap();

            let c_assigned = chip.mul(ctx, &a_assigned, &b_assigned).unwrap();
            let aux = RefreshAux::new(limb_bit_len, a_assigned.num_limbs(), b_assigned.num_limbs());
            let c_assigned = chip.refresh(ctx, &c_assigned, &aux).unwrap();

            let res_assigned = chip
                .assign_integer(ctx, Value::known(res.clone()), num_bit_len * 2)
                .unwrap();

            c_assigned.value().zip(res_assigned.value()).map(|(a, b)| {
                assert_eq!(a, b);
            });
            chip.assert_equal_fresh(ctx, &c_assigned, &res_assigned)
                .unwrap();
        }

        base_test()
            .k(13)
            .lookup_bits(12)
            .expect_satisfied(true)
            .run(|ctx, chip| {
                let a = rng.gen_biguint((NUM_BIT_LEN-1) as u64);
                let b = rng.gen_biguint((NUM_BIT_LEN-1) as u64);
                let res = a.clone() * b.clone();
                mul_circuit(ctx, chip, NUM_BIT_LEN, LIMB_BIT_LEN, a, b, res);
            })
    }

    #[test]
    fn test_mul_mod() {
        const NUM_BIT_LEN: usize = 264;
        const LIMB_BIT_LEN: usize = 88;

        let mut rng = thread_rng();

        fn mul_mod_circuit<F: BigPrimeField>(
            ctx: &mut Context<F>,
            range: &RangeChip<F>,
            num_bit_len: usize,
            limb_bit_len: usize,
            a: BigUint,
            b: BigUint,
            modulus: BigUint,
            res: BigUint,
        ) {
            let chip = BigUintChip::construct(range, limb_bit_len);

            let a_assigned = chip
                .assign_integer(ctx, Value::known(a.clone()), num_bit_len)
                .unwrap();
            let b_assigned = chip
                .assign_integer(ctx, Value::known(b.clone()), num_bit_len)
                .unwrap();
            let modulus_assigned = chip
                .assign_integer(ctx, Value::known(modulus.clone()), num_bit_len)
                .unwrap();

            let c_assigned = chip
                .mul_mod(ctx, &a_assigned, &b_assigned, &modulus_assigned)
                .unwrap();

            let res_assigned = chip
                .assign_integer(ctx, Value::known(res.clone()), num_bit_len)
                .unwrap();

            c_assigned.value().zip(res_assigned.value()).map(|(a, b)| {
                assert_eq!(a, b);
                println!("c_assigned ={:?} \n res_assigned={:?}",a,b);
            });
            chip.assert_equal_fresh(ctx, &c_assigned, &res_assigned)
                .unwrap();
        }

        base_test()
            .k(16)
            .lookup_bits(15)
            .expect_satisfied(true)
            .run(|ctx, chip| {
                let a = rng.gen_biguint((NUM_BIT_LEN-1) as u64);
                let b = rng.gen_biguint((NUM_BIT_LEN-1) as u64);
                let modulus = rng.gen_biguint((NUM_BIT_LEN-1) as u64);
                let res = (a.clone() * b.clone()) % modulus.clone();
                mul_mod_circuit(ctx, chip, NUM_BIT_LEN, LIMB_BIT_LEN, a, b, modulus, res);
            })
    }

    #[test]
    fn test_pow_mod_fixed_exp() {
        const NUM_BIT_LEN: usize = 264;
        const LIMB_BIT_LEN: usize = 88;

        let mut rng = thread_rng();

        fn pow_mod_fixed_exp_circuit<F: BigPrimeField>(
            ctx: &mut Context<F>,
            range: &RangeChip<F>,
            num_bit_len: usize,
            limb_bit_len: usize,
            a: BigUint,
            e: BigUint,
            n: BigUint,
            res: BigUint,
        ) {
            let chip = BigUintChip::construct(range, limb_bit_len);

            let a_assigned = chip
                .assign_integer(ctx, Value::known(a.clone()), num_bit_len)
                .unwrap();
            let n_assigned = chip
                .assign_integer(ctx, Value::known(n.clone()), num_bit_len)
                .unwrap();

            let c_assigned = chip
                .pow_mod_fixed_exp(ctx, &a_assigned, &e, &n_assigned)
                .unwrap();

            let res_assigned = chip
                .assign_integer(ctx, Value::known(res.clone()), num_bit_len)
                .unwrap();

            c_assigned.value().zip(res_assigned.value()).map(|(a, b)| {
                println!("c_assign ={:?} \n res_assign={:?}",a,b);
                assert_eq!(a, b);
            });
            chip.assert_equal_fresh(ctx, &c_assigned, &res_assigned)
                .unwrap();
        }

        base_test()
            .k(16)
            .lookup_bits(15)
            .expect_satisfied(true)
            .run(|ctx, chip| {
                let a = rng.gen_biguint((NUM_BIT_LEN-1) as u64);
                let e = rng.gen_biguint(64 as u64); // Choosing a smaller exponent for efficiency
                let n = rng.gen_biguint((NUM_BIT_LEN-1) as u64);
                let res = a.modpow(&e, &n);
                pow_mod_fixed_exp_circuit(ctx, chip, NUM_BIT_LEN, LIMB_BIT_LEN, a, e, n, res);
            })
    }
}

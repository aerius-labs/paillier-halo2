use halo2_base::{
    halo2_proofs::{circuit::Value, plonk::Error},
    utils::BigPrimeField,
    Context,
};
use num_bigint::BigUint;

use crate::big_uint::{chip::BigUintChip, AssignedBigUint, Fresh, RefreshAux};

#[derive(Debug, Clone)]
pub struct PaillierChip<'a, F: BigPrimeField> {
    pub biguint: &'a BigUintChip<'a, F>,
    pub enc_bits: usize,
    pub n: &'a BigUint,
    pub g: &'a BigUint,
}

impl<'a, F: BigPrimeField> PaillierChip<'a, F> {
    pub fn construct(
        biguint: &'a BigUintChip<'a, F>,
        enc_bits: usize,
        n: &'a BigUint,
        g: &'a BigUint,
    ) -> Self {
        Self {
            biguint,
            enc_bits,
            n,
            g,
        }
    }

    pub fn encrypt(
        &self,
        ctx: &mut Context<F>,
        m: &BigUint,
        r: &BigUint,
    ) -> Result<AssignedBigUint<F, Fresh>, Error> {
        let n_assigned =
            self.biguint
                .assign_integer(ctx, Value::known(self.n.clone()), self.enc_bits)?;
        let mut g_assigned =
            self.biguint
                .assign_integer(ctx, Value::known(self.g.clone()), self.enc_bits)?;
        let mut r_assigned =
            self.biguint
                .assign_integer(ctx, Value::known(r.clone()), self.enc_bits)?;

        let n2 = self.biguint.square(ctx, &n_assigned)?;
        let aux = RefreshAux::new(
            self.biguint.limb_bits,
            n_assigned.num_limbs(),
            n_assigned.num_limbs(),
        );
        let n2 = self.biguint.refresh(ctx, &n2, &aux)?;

        let zero_value = ctx.load_zero();

        g_assigned = g_assigned.extend_limbs(n2.num_limbs() - g_assigned.num_limbs(), zero_value);
        let gm = self.biguint.pow_mod_fixed_exp(ctx, &g_assigned, m, &n2)?;

        r_assigned = r_assigned.extend_limbs(n2.num_limbs() - r_assigned.num_limbs(), zero_value);
        let rn = self
            .biguint
            .pow_mod_fixed_exp(ctx, &r_assigned, self.n, &n2)?;

        let c = self.biguint.mul_mod(ctx, &gm, &rn, &n2)?;

        Ok(c)
    }
    pub fn add(
        &self,
        ctx: &mut Context<F>,
        c1: &AssignedBigUint<F, Fresh>,
        c2: &AssignedBigUint<F, Fresh>,
    ) -> Result<AssignedBigUint<F, Fresh>, Error> {
        let mut c1_assigned = c1.clone();

        let mut c2_assigned = c2.clone();

        let n_assigned =
            self.biguint
                .assign_integer(ctx, Value::known(self.n.clone()), self.enc_bits)?;
        let n2 = self.biguint.square(ctx, &n_assigned)?;
        let aux = RefreshAux::new(
            self.biguint.limb_bits,
            n_assigned.num_limbs(),
            n_assigned.num_limbs(),
        );
        let n2 = self.biguint.refresh(ctx, &n2, &aux)?;

        let zero_value = ctx.load_zero();

        c1_assigned =
            c1_assigned.extend_limbs(n2.num_limbs() - c1_assigned.num_limbs(), zero_value);
        c2_assigned =
            c2_assigned.extend_limbs(n2.num_limbs() - c2_assigned.num_limbs(), zero_value);
        let result = self.biguint.mul_mod(ctx, &c1_assigned, &c2_assigned, &n2)?;

        Ok(result)
    }
}

pub fn paillier_enc(n: &BigUint, g: &BigUint, m: &BigUint, r: &BigUint) -> BigUint {
    let n2 = n * n;
    let gm = g.modpow(m, &n2);
    let rn = r.modpow(n, &n2);
    (gm * rn) % n2
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

    use crate::{big_uint::chip::BigUintChip, paillier::paillier_enc};

    #[test]
    fn test_paillier_encryption() {
        const ENC_BIT_LEN: usize = 128;
        const LIMB_BIT_LEN: usize = 64;

        let mut rng = thread_rng();

        fn paillier_enc_circuit<F: BigPrimeField>(
            ctx: &mut Context<F>,
            range: &RangeChip<F>,
            enc_bit_len: usize,
            limb_bit_len: usize,
            n: &BigUint,
            g: &BigUint,
            m: &BigUint,
            r: &BigUint,
            res: &BigUint,
        ) {
            let biguint_chip = BigUintChip::construct(range, limb_bit_len);
            let paillier_chip = super::PaillierChip::construct(&biguint_chip, enc_bit_len, n, g);

            let c_assigned = paillier_chip.encrypt(ctx, &m, &r).unwrap();

            let res_assigned = biguint_chip
                .assign_integer(ctx, Value::known(res.clone()), enc_bit_len * 2)
                .unwrap();

            c_assigned.value().zip(res_assigned.value()).map(|(a, b)| {
                assert_eq!(a, b);
            });
            biguint_chip
                .assert_equal_fresh(ctx, &c_assigned, &res_assigned)
                .unwrap();
        }

        base_test()
            .k(16)
            .lookup_bits(15)
            .expect_satisfied(true)
            .run(|ctx, range| {
                // Define n, g, m, and r for the test
                let n = rng.gen_biguint(ENC_BIT_LEN as u64);
                let g = rng.gen_biguint(ENC_BIT_LEN as u64);
                let m = rng.gen_biguint(ENC_BIT_LEN as u64);
                let r = rng.gen_biguint(ENC_BIT_LEN as u64);

                let expected_c = paillier_enc(&n, &g, &m, &r);

                paillier_enc_circuit(
                    ctx,
                    range,
                    ENC_BIT_LEN,
                    LIMB_BIT_LEN,
                    &n,
                    &g,
                    &m,
                    &r,
                    &expected_c,
                );
            });
    }
    #[test]
    fn test_encryption_addition() {
        const ENC_BIT_LEN: usize = 128;
        const LIMB_BIT_LEN: usize = 64;

        let mut rng = thread_rng();

        fn paillier_enc_add<F: BigPrimeField>(
            ctx: &mut Context<F>,
            range: &RangeChip<F>,
            enc_bit_len: usize,
            limb_bit_len: usize,
            n: &BigUint,
            g: &BigUint,
            m1: &BigUint,
            r1: &BigUint,
            m2:&BigUint,
            r2:&BigUint,
            res: &BigUint,
        ) {
            let biguint_chip = BigUintChip::construct(range, limb_bit_len);
            let paillier_chip = super::PaillierChip::construct(&biguint_chip, enc_bit_len, n, g);

            let c1_assigned = paillier_chip.encrypt(ctx, &m1, &r1).unwrap();
            let c2_assigned = paillier_chip.encrypt(ctx, &m2, &r2).unwrap();

            let c_add_assigned = paillier_chip.add(ctx, &c1_assigned, &c2_assigned).unwrap();

            let res_assigned = biguint_chip
                .assign_integer(ctx, Value::known(res.clone()), enc_bit_len * 2)
                .unwrap();

            c_add_assigned
                .value()
                .zip(res_assigned.value())
                .map(|(a, b)| {
                    assert_eq!(a, b);
                });
            biguint_chip
                .assert_equal_fresh(ctx, &c_add_assigned, &res_assigned)
                .unwrap();
        }

        fn paillier_add(n: &BigUint, c1: &BigUint, c2: &BigUint) -> BigUint {
            let n2 = n * n;
            (c1 * c2) % n2
        }

        base_test()
            .k(16)
            .lookup_bits(15)
            .expect_satisfied(true)
            .run(|ctx, range| {
                // Define parameters for the test
                let n = rng.gen_biguint(ENC_BIT_LEN as u64);
                let g = rng.gen_biguint(ENC_BIT_LEN as u64);
                let m1 = rng.gen_biguint(ENC_BIT_LEN as u64);
                let r1 = rng.gen_biguint(ENC_BIT_LEN as u64);
                let m2 = rng.gen_biguint(ENC_BIT_LEN as u64);
                let r2 = rng.gen_biguint(ENC_BIT_LEN as u64);

                let c1 = paillier_enc(&n, &g, &m1, &r1);
                let c2 =paillier_enc(&n, &g, &m2, &r2);
                let expected_c12 = paillier_add(&n, &c1, &c2);

                paillier_enc_add(
                    ctx,
                    range,
                    ENC_BIT_LEN,
                    LIMB_BIT_LEN,
                    &n,
                    &g,
                    &m1,
                    &r1,
                    &m2,
                    &r2,
                    &expected_c12,
                );
            });
    }
}

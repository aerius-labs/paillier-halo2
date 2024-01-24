use biguint_halo2::big_uint::{ chip::BigUintChip, AssignedBigUint, Fresh, RefreshAux };
use halo2_base::{ halo2_proofs::plonk::Error, utils::{ fe_to_biguint, BigPrimeField }, Context };
use num_bigint::BigUint;
use num_traits::Zero;

pub struct EncryptionPublicKeyAssigned<F: BigPrimeField> {
    pub n: AssignedBigUint<F, Fresh>,
    pub g: AssignedBigUint<F, Fresh>,
}

#[derive(Debug, Clone)]
pub struct PaillierChip<'a, F: BigPrimeField> {
    pub biguint: &'a BigUintChip<'a, F>,
    pub enc_bits: usize,
}

impl<'a, F: BigPrimeField> PaillierChip<'a, F> {
    pub fn construct(biguint: &'a BigUintChip<'a, F>, enc_bits: usize) -> Self {
        Self { biguint, enc_bits }
    }

    pub fn get_biguint(&self, assigned: &AssignedBigUint<F, Fresh>) -> BigUint {
        assigned
            .limbs()
            .iter()
            .rev()
            .fold(BigUint::zero(), |acc, acell| {
                (acc << assigned.int_ref().max_limb_bits) + fe_to_biguint(acell.value())
            })
    }

    pub fn encrypt(
        &self,
        ctx: &mut Context<F>,
        pk_enc: &EncryptionPublicKeyAssigned<F>,
        m: &AssignedBigUint<F, Fresh>,
        r: &AssignedBigUint<F, Fresh>
    ) -> Result<AssignedBigUint<F, Fresh>, Error> {
        let n2 = self.biguint.square(ctx, &pk_enc.n)?;
        let aux = RefreshAux::new(
            self.biguint.limb_bits,
            pk_enc.n.num_limbs(),
            pk_enc.n.num_limbs()
        );
        let n2 = self.biguint.refresh(ctx, &n2, &aux)?;

        let zero_value = ctx.load_zero();

        let g_extended = pk_enc.g.extend_limbs(n2.num_limbs() - pk_enc.g.num_limbs(), zero_value);
        let m_biguint = self.get_biguint(m);
        let gm = self.biguint.pow_mod_fixed_exp(ctx, &g_extended, &m_biguint, &n2)?;

        let r_extended = r.extend_limbs(n2.num_limbs() - r.num_limbs(), zero_value);
        let n_biguint = self.get_biguint(&pk_enc.n);
        let rn = self.biguint.pow_mod_fixed_exp(ctx, &r_extended, &n_biguint, &n2)?;

        let c = self.biguint.mul_mod(ctx, &gm, &rn, &n2)?;

        Ok(c)
    }

    pub fn add(
        &self,
        ctx: &mut Context<F>,
        pk_enc: &EncryptionPublicKeyAssigned<F>,
        c1: &AssignedBigUint<F, Fresh>,
        c2: &AssignedBigUint<F, Fresh>
    ) -> Result<AssignedBigUint<F, Fresh>, Error> {
        let n2 = self.biguint.square(ctx, &pk_enc.n)?;
        let aux = RefreshAux::new(
            self.biguint.limb_bits,
            pk_enc.n.num_limbs(),
            pk_enc.n.num_limbs()
        );
        let n2 = self.biguint.refresh(ctx, &n2, &aux)?;

        let zero_value = ctx.load_zero();

        let c1_extended = c1.extend_limbs(n2.num_limbs() - c1.num_limbs(), zero_value);
        let c2_extended = c2.extend_limbs(n2.num_limbs() - c2.num_limbs(), zero_value);
        let result = self.biguint.mul_mod(ctx, &c1_extended, &c2_extended, &n2)?;

        Ok(result)
    }
}

pub fn paillier_enc_native(n: &BigUint, g: &BigUint, m: &BigUint, r: &BigUint) -> BigUint {
    let n2 = n * n;
    let gm = g.modpow(m, &n2);
    let rn = r.modpow(n, &n2);
    (gm * rn) % n2
}

pub fn paillier_add_native(n: &BigUint, c1: &BigUint, c2: &BigUint) -> BigUint {
    let n2 = n * n;
    (c1 * c2) % n2
}

#[cfg(test)]
mod test {
    use biguint_halo2::big_uint::chip::BigUintChip;
    use halo2_base::{
        gates::RangeChip,
        halo2_proofs::circuit::Value,
        utils::{ testing::base_test, BigPrimeField },
        Context,
    };
    use num_bigint::{ BigUint, RandBigInt };
    use rand::thread_rng;

    use crate::paillier::paillier_enc_native;

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
            n: BigUint,
            g: BigUint,
            m: BigUint,
            r: BigUint,
            res: BigUint
        ) {
            let biguint_chip = BigUintChip::construct(range, limb_bit_len);
            let paillier_chip = super::PaillierChip::construct(&biguint_chip, enc_bit_len);

            let n_assigned = biguint_chip
                .assign_integer(ctx, Value::known(n.clone()), enc_bit_len)
                .unwrap();
            let g_assigned = biguint_chip
                .assign_integer(ctx, Value::known(g.clone()), enc_bit_len)
                .unwrap();
            let pk_enc = super::EncryptionPublicKeyAssigned {
                n: n_assigned,
                g: g_assigned,
            };

            let m_assigned = biguint_chip
                .assign_integer(ctx, Value::known(m.clone()), enc_bit_len)
                .unwrap();
            let r_assigned = biguint_chip
                .assign_integer(ctx, Value::known(r.clone()), enc_bit_len)
                .unwrap();

            let c_assigned = paillier_chip.encrypt(ctx, &pk_enc, &m_assigned, &r_assigned).unwrap();

            let res_assigned = biguint_chip
                .assign_integer(ctx, Value::known(res.clone()), enc_bit_len * 2)
                .unwrap();

            c_assigned
                .value()
                .zip(res_assigned.value())
                .map(|(a, b)| {
                    assert_eq!(a, b);
                });
            biguint_chip.assert_equal_fresh(ctx, &c_assigned, &res_assigned).unwrap();
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

                let res = paillier_enc_native(&n, &g, &m, &r);

                paillier_enc_circuit(ctx, range, ENC_BIT_LEN, LIMB_BIT_LEN, n, g, m, r, res);
            });
    }

    #[test]
    fn test_encryption_addition() {
        const ENC_BIT_LEN: usize = 264;
        const LIMB_BIT_LEN: usize = 88;

        let mut rng = thread_rng();

        fn paillier_enc_add<F: BigPrimeField>(
            ctx: &mut Context<F>,
            range: &RangeChip<F>,
            enc_bit_len: usize,
            limb_bit_len: usize,
            n: BigUint,
            g: BigUint,
            c1: BigUint,
            c2: BigUint,
            res: BigUint
        ) {
            let biguint_chip = BigUintChip::construct(range, limb_bit_len);
            let paillier_chip = super::PaillierChip::construct(&biguint_chip, enc_bit_len);

            let n_assigned = biguint_chip
                .assign_integer(ctx, Value::known(n.clone()), enc_bit_len)
                .unwrap();
            let g_assigned = biguint_chip
                .assign_integer(ctx, Value::known(g.clone()), enc_bit_len)
                .unwrap();
            let pk_enc = super::EncryptionPublicKeyAssigned {
                n: n_assigned,
                g: g_assigned,
            };

            let c1_assigned = biguint_chip
                .assign_integer(ctx, Value::known(c1.clone()), enc_bit_len)
                .unwrap();
            let c2_assigned = biguint_chip
                .assign_integer(ctx, Value::known(c2.clone()), enc_bit_len)
                .unwrap();

            let c_add_assigned = paillier_chip
                .add(ctx, &pk_enc, &c1_assigned, &c2_assigned)
                .unwrap();

            let res_assigned = biguint_chip
                .assign_integer(ctx, Value::known(res.clone()), enc_bit_len * 2)
                .unwrap();

            c_add_assigned
                .value()
                .zip(res_assigned.value())
                .map(|(a, b)| {
                    assert_eq!(a, b);
                });
            biguint_chip.assert_equal_fresh(ctx, &c_add_assigned, &res_assigned).unwrap();
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
                let c1 = rng.gen_biguint(ENC_BIT_LEN as u64);
                let c2 = rng.gen_biguint(ENC_BIT_LEN as u64);
                let res = paillier_add(&n, &c1, &c2);

                paillier_enc_add(ctx, range, ENC_BIT_LEN, LIMB_BIT_LEN, n, g, c1, c2, res);
            });
    }
}

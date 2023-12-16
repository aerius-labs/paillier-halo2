use halo2_base::{
    utils::PrimeField,
    Context,
    halo2_proofs::{ plonk::Error, circuit::Value },
    gates::GateInstructions,
};
use num_bigint::BigUint;

use crate::big_uint::{ AssignedBigUint, Fresh, BigUintConfig, BigUintInstructions, RefreshAux };

#[derive(Clone, Debug)]
pub struct PaillierConfig<F: PrimeField> {
    pub biguint_config: BigUintConfig<F>,
}

impl<F: PrimeField> PaillierConfig<F> {
    pub fn extend_limbs<'v>(
        &self,
        ctx: &mut Context<'v, F>,
        a: &AssignedBigUint<'v, F, Fresh>,
        target_num_limbs: usize
    ) -> Result<AssignedBigUint<'v, F, Fresh>, Error> {
        let current_num_limbs = a.num_limbs();
        if current_num_limbs >= target_num_limbs {
            return Ok(a.clone());
        }

        let zero = self.biguint_config.gate().load_zero(ctx);
        let extended_a = a.extend_limbs(target_num_limbs - current_num_limbs, zero);
        Ok(extended_a)
    }

    pub fn paillier_encrypt<'v>(
        &self,
        ctx: &mut Context<'v, F>,
        aux: &RefreshAux,
        n: &BigUint,
        g: &AssignedBigUint<'v, F, Fresh>,
        m: &BigUint,
        r: &AssignedBigUint<'v, F, Fresh>
    ) -> Result<AssignedBigUint<'v, F, Fresh>, Error> {
        // Ensure that BigUintConfig is accessible here
        let biguint_config = &self.biguint_config;

        let n_assigned = biguint_config.assign_integer(
            ctx,
            Value::known(n.to_owned()),
            biguint_config.limb_bits * 2 // ! Specific to total bits
        )?;

        // Calculate n^2 (n squared)
        let n2 = biguint_config.square(ctx, &n_assigned)?;
        let n2 = biguint_config.refresh(ctx, &n2, aux)?;

        // Calculate g^m mod n^2
        let g_ext = self.extend_limbs(ctx, g, n2.num_limbs())?;
        let gm = biguint_config.pow_mod_fixed_exp(ctx, &g_ext, m, &n2)?;

        // Calculate r^n mod n^2
        let r_ext = self.extend_limbs(ctx, r, n2.num_limbs())?;
        let rn = biguint_config.pow_mod_fixed_exp(ctx, &r_ext, n, &n2)?;

        // Calculate c = (g^m * r^n) mod n^2
        let c = biguint_config.mul_mod(ctx, &gm, &rn, &n2)?;

        Ok(c)
    }
}

#[cfg(test)]
mod test {
    use std::marker::PhantomData;
    use halo2_base::{
        utils::PrimeField,
        halo2_proofs::{
            halo2curves::bn256::Fr,
            plonk::{ Error, Circuit, ConstraintSystem },
            circuit::{ Layouter, SimpleFloorPlanner },
            dev::MockProver,
        },
        gates::range::RangeConfig,
    };
    use halo2_base::gates::range::RangeStrategy::Vertical;
    use num_bigint::{ BigUint, RandBigInt };
    use crate::big_uint::{ BigUintConfig, BigUintInstructions, RefreshAux };

    use super::PaillierConfig;

    fn calc_enc(n: BigUint, g: BigUint, m: BigUint, r: BigUint) -> BigUint {
        let n2 = n.clone() * &n;
        let gm = g.modpow(&m, &n2);
        let rn = r.modpow(&n, &n2);
        let c = (gm * rn) % n2;
        c
    }

    struct TestPaillierEncryptCircuit<F: PrimeField> {
        n: BigUint,
        g: BigUint,
        m: BigUint,
        r: BigUint,
        _f: PhantomData<F>,
    }

    impl<F: PrimeField> Circuit<F> for TestPaillierEncryptCircuit<F> {
        type Config = PaillierConfig<F>;
        type FloorPlanner = SimpleFloorPlanner;

        fn without_witnesses(&self) -> Self {
            unimplemented!();
        }

        fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
            // TODO: Figure out why num_advice = 60 works
            let range_config = RangeConfig::configure(meta, Vertical, &[60], &[4], 1, 12, 0, 13);
            let biguint_config = BigUintConfig::construct(range_config, 64);
            PaillierConfig { biguint_config }
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<F>
        ) -> Result<(), Error> {
            layouter.assign_region(
                || "Paillier encrypt test",
                |region| {
                    let mut ctx = config.biguint_config.new_context(region);
                    let aux = RefreshAux::new(64, 2, 2);
                    let g_assigned = config.biguint_config.assign_constant(
                        &mut ctx,
                        self.g.clone()
                    )?;
                    let r_assigned = config.biguint_config.assign_constant(
                        &mut ctx,
                        self.r.clone()
                    )?;

                    let encrypted = config.paillier_encrypt(
                        &mut ctx,
                        &aux,
                        &self.n,
                        &g_assigned,
                        &self.m,
                        &r_assigned
                    )?;
                    let expected = calc_enc(
                        self.n.clone(),
                        self.g.clone(),
                        self.m.clone(),
                        self.r.clone()
                    );
                    let expected_assigned = config.biguint_config.assign_constant(
                        &mut ctx,
                        expected
                    )?;

                    // Assert that the encryption result matches the expected result
                    config.biguint_config.assert_equal_fresh(
                        &mut ctx,
                        &encrypted,
                        &expected_assigned
                    )?;
                    Ok(())
                }
            )?;
            Ok(())
        }
    }

    #[test]
    fn test_paillier_encrypt() {
        for _ in 0..10 {
            // Initialize test parameters
            let mut rng = rand::thread_rng();

            let n = rng.gen_biguint(128);
            let g = rng.gen_biguint(128);
            let m = rng.gen_biguint(128);
            let r = rng.gen_biguint(128);

            // Construct the test circuit
            let circuit = TestPaillierEncryptCircuit::<Fr> {
                n,
                g,
                m,
                r,
                _f: PhantomData,
            };

            // Set the circuit width and run the prover
            let k = 13; // Circuit width parameter
            let prover = MockProver::run(k, &circuit, vec![]).unwrap();

            // Verify the proof
            assert!(prover.verify().is_ok());
        }
    }
}

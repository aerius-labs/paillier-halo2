use halo2_proofs::{
    circuit::{Layouter, SimpleFloorPlanner},
    halo2curves::bn256::Fr,
    plonk::{Circuit, ConstraintSystem, Error},
};
use mylib::circuits::{
    modexp::ModExpChip,
    range::{RangeCheckChip, RangeCheckConfig},
    CommonGateConfig,
};
use num_bigint::BigUint;

use crate::chips::helper::{HelperChip, HelperChipConfig};

#[derive(Debug, Clone)]
pub struct TestModExpConfig {
    pub modexp_config: CommonGateConfig,
    pub helper_config: HelperChipConfig,
    pub rangecheck_config: RangeCheckConfig,
}

#[derive(Clone, Debug, Default)]
pub struct ModExpCircuit {
    base: BigUint,
    exp: BigUint,
    modulus: BigUint,
    bn_test_res: BigUint,
}

impl Circuit<Fr> for ModExpCircuit {
    type Config = TestModExpConfig;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self::default()
    }

    fn configure(meta: &mut ConstraintSystem<Fr>) -> Self::Config {
        let rangecheck_config = RangeCheckChip::<Fr>::configure(meta);
        Self::Config {
            modexp_config: ModExpChip::<Fr>::configure(meta, &rangecheck_config),
            helper_config: HelperChip::configure(meta),
            rangecheck_config,
        }
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<Fr>,
    ) -> Result<(), Error> {
        let modexp_chip = ModExpChip::<Fr>::new(config.clone().modexp_config);
        let helper_chip = HelperChip::new(config.clone().helper_config);
        let mut range_chip = RangeCheckChip::<Fr>::new(config.rangecheck_config);
        layouter.assign_region(
            || "assign mod exp",
            |mut region| {
                range_chip.initialize(&mut region)?;
                let mut offset = 0;
                let base = helper_chip.assign_base(&mut region, &mut offset, &self.base)?;
                let exp = helper_chip.assign_exp(&mut region, &mut offset, &self.exp)?;
                let modulus =
                    helper_chip.assign_modulus(&mut region, &mut offset, &self.modulus)?;
                let result =
                    helper_chip.assign_results(&mut region, &mut offset, &self.bn_test_res)?;
                let rem = modexp_chip.mod_exp(
                    &mut region,
                    &mut range_chip,
                    &mut offset,
                    &base,
                    &exp,
                    &modulus,
                )?;
                for i in 0..4 {
                    println!(
                        "rem is {:?}, \t result is {:?}",
                        &rem.limbs[i].value, &result.limbs[i].value
                    );
                    println!("remcell is \t{:?}", &rem.limbs[i].cell);
                    println!("resultcell is \t {:?}", &result.limbs[i].cell);
                    region.constrain_equal(
                        rem.limbs[i].clone().cell.unwrap().cell(),
                        result.limbs[i].clone().cell.unwrap().cell(),
                    )?;
                }
                println!("offset final {offset}");
                Ok(())
            },
        )?;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::utils::{get_random_x_bit_bn, CircuitError};
    use halo2_proofs::dev::MockProver;

    const LIMB_WIDTH: usize = 108;

    #[test]
    fn test_modexp_circuit() -> Result<(), CircuitError> {
        const NUM_TESTS: usize = 5;

        let mut bn_base_test_vectors: Vec<BigUint> = Vec::with_capacity(NUM_TESTS);
        let mut bn_modulus_test_vectors: Vec<BigUint> = Vec::with_capacity(NUM_TESTS);
        let mut bn_exp_test_vectors: Vec<BigUint> = Vec::with_capacity(NUM_TESTS);

        let bit_len_b: [usize; NUM_TESTS] = [1, 4, 8, 250, 255];
        let bit_len_m: [usize; NUM_TESTS] = [1, 4, 8, 255, 254];
        let bit_len_e: [usize; NUM_TESTS] = [
            1,
            LIMB_WIDTH - 1,
            LIMB_WIDTH + 1,
            LIMB_WIDTH + LIMB_WIDTH - 1,
            LIMB_WIDTH + LIMB_WIDTH + LIMB_WIDTH - 90,
        ];

        for i in 0..NUM_TESTS {
            bn_base_test_vectors.push(get_random_x_bit_bn(bit_len_b[i]));
            bn_modulus_test_vectors.push(get_random_x_bit_bn(bit_len_m[i]));
            bn_exp_test_vectors.push(get_random_x_bit_bn(bit_len_e[i]));
        }

        for i in 0..NUM_TESTS {
            let base_testcase = bn_base_test_vectors[i].clone();
            let modulus_testcase = bn_modulus_test_vectors[i].clone();
            let exp_testcase = bn_exp_test_vectors[i].clone();
            let bn_test_res = base_testcase
                .clone()
                .modpow(&exp_testcase, &modulus_testcase);
            println!(
                "testcase: (0x{})^(0x{}) mod 0x{} = 0x{}",
                base_testcase.clone().to_str_radix(16),
                exp_testcase.clone().to_str_radix(16),
                modulus_testcase.clone().to_str_radix(16),
                bn_test_res.to_str_radix(16)
            );

            let base = base_testcase.clone();
            let exp = exp_testcase.clone();
            let modulus = modulus_testcase.clone();

            let test_circuit = ModExpCircuit {
                base,
                exp,
                modulus,
                bn_test_res,
            };

            let prover = match MockProver::run(16, &test_circuit, vec![]) {
                Ok(prover_run) => prover_run,
                Err(prover_error) => {
                    return Err(CircuitError::ProverError(prover_error));
                }
            };

            match prover.verify() {
                Ok(_) => (),
                Err(verifier_error) => {
                    return Err(CircuitError::VerifierError(verifier_error));
                }
            };
        }
        Ok(())
    }
}

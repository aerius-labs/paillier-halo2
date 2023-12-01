use std::ops::Mul;

use halo2_proofs::{
    circuit::{Layouter, SimpleFloorPlanner},
    halo2curves::bn256::Fr,
    plonk::{Circuit, ConstraintSystem, Error},
};
use mylib::circuits::{
    modexp::{ModExpChip, Number},
    range::{RangeCheckChip, RangeCheckConfig},
    CommonGateConfig,
};
use num_bigint::BigUint;

use crate::chips::helper::{HelperChip, HelperChipConfig};

#[derive(Debug, Clone)]
pub struct TestEncConfig {
    pub modexp_config_g: CommonGateConfig,
    pub modexp_config_r: CommonGateConfig,
    pub mul_config: CommonGateConfig,
    pub helper_config: HelperChipConfig,
    pub rangecheck_config: RangeCheckConfig,
}

#[derive(Clone, Debug, Default)]
pub struct EncCircuit {
    g: BigUint,
    m: BigUint,
    r: BigUint,
    n: BigUint,
    modulus: BigUint,
    bn_test_res1: BigUint,
    bn_test_res2: BigUint,
    bn_test_mulout: BigUint,
}
//bn_test_res1/2 expected value of g^m mod modulus/r^n mod modulus
//bn_test_mulout expected value of bn_test_res1 * res2 mod modulus

impl Circuit<Fr> for EncCircuit {
    type Config = TestEncConfig;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self::default()
    }

    fn configure(meta: &mut ConstraintSystem<Fr>) -> Self::Config {
        let rangecheck_config = RangeCheckChip::<Fr>::configure(meta);
        Self::Config {
            modexp_config_g: ModExpChip::<Fr>::configure(meta, &rangecheck_config),
            modexp_config_r: ModExpChip::<Fr>::configure(meta, &rangecheck_config),
            mul_config: ModExpChip::<Fr>::configure(meta, &rangecheck_config),
            helper_config: HelperChip::configure(meta),
            rangecheck_config,
        }
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<Fr>,
    ) -> Result<(), Error> {
        let modexp_chip_g = ModExpChip::<Fr>::new(config.clone().modexp_config_g);
        let modexp_chip_r = ModExpChip::<Fr>::new(config.clone().modexp_config_r);
        let mul_chip = ModExpChip::<Fr>::new(config.clone().mul_config);

        let helper_chip = HelperChip::new(config.clone().helper_config);
        let mut range_chip = RangeCheckChip::<Fr>::new(config.rangecheck_config);
        layouter.assign_region(
            || "assign mod exp",
            |mut region| {
                range_chip.initialize(&mut region)?;
                let mut offset = 0;
                let g = helper_chip.assign_base(&mut region, &mut offset, &self.g)?;
                let m = helper_chip.assign_exp(&mut region, &mut offset, &self.m)?;
             //n^2
                let n_sqr= self.n.clone().mul(self.n.clone());
                let n_sqr=helper_chip.assign_base(&mut region, &mut offset, &n_sqr)?;

                let r = helper_chip.assign_base(&mut region, &mut offset, &self.r)?;
                let n = helper_chip.assign_exp(&mut region, &mut offset, &self.n)?;

                let modulus =
                    helper_chip.assign_modulus(&mut region, &mut offset, &self.modulus)?;
                let result1 =
                    helper_chip.assign_results(&mut region, &mut offset, &self.bn_test_res1)?;

                let result2 =
                    helper_chip.assign_results(&mut region, &mut offset, &self.bn_test_res2)?;

                let mul_result =
                    helper_chip.assign_results(&mut region, &mut offset, &self.bn_test_mulout)?;

                let rem1 = modexp_chip_g.mod_exp(
                    &mut region,
                    &mut range_chip,
                    &mut offset,
                    &g,
                    &m,
                    &modulus,
                )?;
                for i in 0..4 {
                    println!(
                        "rem is {:?}, \t result is {:?}",
                        &rem1.limbs[i].value, &result1.limbs[i].value
                    );
                    println!("remcell is \t{:?}", &rem1.limbs[i].cell);
                    println!("                    --------------------------------------------------------           ");
                    println!("resultcell is \t {:?}", &result1.limbs[i].cell);
                    // region.constrain_equal(
                    //     rem1.limbs[i].clone().cell.unwrap().cell(),
                    //     result1.limbs[i].clone().cell.unwrap().cell(),
                    // )?;
                }

                let rem2 = modexp_chip_r.mod_mult(
                    &mut region,
                    &mut range_chip,
                    &mut offset,
                    &r,
                    &n,
                    &modulus,
                )?;
                for i in 0..4 {
                    // println!(
                    //     "rem is {:?}, \t result is {:?}",
                    //     &rem2.limbs[i].value, &result2.limbs[i].value
                    // );
                    // println!("remcell is \t{:?}", &rem2.limbs[i].cell);
                    // println!("resultcell is \t {:?}", &result2.limbs[i].cell);
                    // region.constrain_equal(
                    //     rem2.limbs[i].clone().cell.unwrap().cell(),
                    //     result2.limbs[i].clone().cell.unwrap().cell(),
                    // )?;
                }
                let mul_out = mul_chip.mod_mult(
                    &mut region,
                    &mut range_chip,
                    &mut offset,
                    &rem1,
                    &rem2,
                    &modulus,
                )?;
            

                for i in 0..4 {
                    // println!(
                    //     "final out is {:?}, \t result is {:?}",
                    //     &mul_out.limbs[i].value, &mul_result.limbs[i].value
                    // );
                      println!("remcell is \t{:?}", &mul_out.limbs[i].clone().cell.unwrap());
                      //println!("resultcell is \t {:?}", &mul_result.limbs[i].cell);
                    // region.constrain_equal(
                    //     mul_out.limbs[i].clone().cell.unwrap().cell(),
                    //     mul_result.limbs[i].clone().cell.unwrap().cell(),
                    // )?;
                    // region.constrain_equal(
                    //     modulus.limbs[i].clone().cell.unwrap().cell(),
                    //     n_sqr.limbs[i].clone().cell.unwrap().cell(),
                    // )?;
                  //  region.constrain_instance(cell, column, row)
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
    use std::ops::Mul;

    use super::*;
    use crate::utils::{get_random_x_bit_bn, CircuitError};
    use halo2_proofs::dev::MockProver;

   // const LIMB_WIDTH: usize = 108;

    #[test]
    fn test_enc_circuit() -> Result<(), CircuitError> {
        const NUM_TESTS: usize = 5;

        let mut bn_g_test_vectors: Vec<BigUint> = Vec::with_capacity(NUM_TESTS);
        let mut bn_r_test_vectors: Vec<BigUint> = Vec::with_capacity(NUM_TESTS);

        let mut bn_modulus_test_vectors: Vec<BigUint> = Vec::with_capacity(NUM_TESTS);
        let mut bn_m_test_vectors: Vec<BigUint> = Vec::with_capacity(NUM_TESTS);
        let mut bn_n_test_vectors: Vec<BigUint> = Vec::with_capacity(NUM_TESTS);

        let bit_len_g: [usize; NUM_TESTS] = [1, 4, 8, 250, 255];
        let bit_len_r: [usize; NUM_TESTS] = [1, 4, 8, 25, 254];
        let bit_len_mod: [usize; NUM_TESTS] = [1, 16, 64, 100, 225];
        let bit_len_m: [usize; NUM_TESTS] = [1, 4, 8, 10, 15];
        let bit_len_n = bit_len_m.clone();

        for i in 0..NUM_TESTS {
            bn_g_test_vectors.push(get_random_x_bit_bn(bit_len_g[i]));
            bn_modulus_test_vectors.push(get_random_x_bit_bn(bit_len_mod[i]));
            bn_m_test_vectors.push(get_random_x_bit_bn(bit_len_m[i]));
            bn_r_test_vectors.push(get_random_x_bit_bn(bit_len_r[i]));
            bn_n_test_vectors.push(get_random_x_bit_bn(bit_len_n[i]));
        }

        for i in 0..NUM_TESTS {
            let g_testcase = bn_g_test_vectors[i].clone();
            let modulus_testcase = bn_modulus_test_vectors[i].clone();
            let m_testcase = bn_m_test_vectors[i].clone();
            let r_testcase = bn_r_test_vectors[i].clone();
            let n_testcase = bn_n_test_vectors[i].clone();
            let bn_test_res1 = g_testcase.clone().modpow(&m_testcase, &modulus_testcase);
            let bn_test_res2 = r_testcase.clone().modpow(&n_testcase, &modulus_testcase);

            let temp = bn_test_res1.clone().mul(bn_test_res2.clone());
            let one =BigUint::try_from(1).unwrap();
            let bn_test_mulout=temp.clone().modpow(&one, &modulus_testcase);
            println!(
                "testcase g^m : (0x{})^(0x{}) mod 0x{} = 0x{}",
                g_testcase.clone().to_str_radix(16),
                m_testcase.clone().to_str_radix(16),
                modulus_testcase.clone().to_str_radix(16),
                bn_test_res1.clone().to_str_radix(16)
            );

            println!(
                "testcase r^n : (0x{})^(0x{}) mod 0x{} = 0x{}",
                r_testcase.clone().to_str_radix(16),
                n_testcase.clone().to_str_radix(16),
                modulus_testcase.clone().to_str_radix(16),
                bn_test_res2.clone().to_str_radix(16)
            );

            println!(
                "testcase g^m *r^n mod n^2 : (0x{})^(0x{}) mod 0x{} = 0x{}",
                bn_test_res1.clone().to_str_radix(16),
                bn_test_res2.clone().to_str_radix(16),
                modulus_testcase.clone().to_str_radix(16),
                bn_test_mulout.to_str_radix(16)
            );

            let g = g_testcase.clone();
            let m = m_testcase.clone();
            let r = r_testcase.clone();
            let n = n_testcase.clone();
            let modulus = modulus_testcase.clone();

            let test_circuit = EncCircuit {
                g,
                m,
                r,
                n,
                modulus,
                bn_test_res1,
                bn_test_res2,
                bn_test_mulout,
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

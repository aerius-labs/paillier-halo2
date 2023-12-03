use std::ops::Mul;

use halo2_proofs::{
    circuit::{Layouter, SimpleFloorPlanner},
    halo2curves::bn256::Fr,
    plonk::{Circuit, ConstraintSystem, Error, Fixed},
};
use mylib::circuits::{
    modexp::ModExpChip,
    range::{RangeCheckChip, RangeCheckConfig},
    CommonGateConfig,
};
use num_bigint::BigUint;

use crate::chips::helper::{HelperChip, HelperChipConfig};

#[derive(Debug, Clone)]
pub struct TestEncConfig {
    pub modexp_config: CommonGateConfig,
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

impl Circuit<Fr> for EncCircuit {
    type Config = TestEncConfig;
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
        let gm_chip = ModExpChip::<Fr>::new(config.clone().modexp_config);
        let rn_chip = ModExpChip::<Fr>::new(config.clone().modexp_config);
        let helper_chip = HelperChip::new(config.clone().helper_config);
        let mul_chip = ModExpChip::<Fr>::new(config.clone().modexp_config);
        let mut range_chip = RangeCheckChip::<Fr>::new(config.rangecheck_config);
        layouter.assign_region(
            || "assign mod m",
            |mut region| {
                range_chip.initialize(&mut region)?;
                let mut offset = 0;
                let g = helper_chip.assign_base(&mut region, &mut offset, &self.g)?;
                let m = helper_chip.assign_exp(&mut region, &mut offset, &self.m)?;
                let modulus =
                    helper_chip.assign_modulus(&mut region, &mut offset, &self.modulus)?;
                let res_gm =
                    helper_chip.assign_results(&mut region, &mut offset, &self.bn_test_res1)?;
                let g_m =
                    gm_chip.mod_exp(&mut region, &mut range_chip, &mut offset, &g, &m, &modulus)?;
                for i in 0..4 {
                    // println!(
                    //     "g_m is {:?}, \t res_gm is {:?}",
                    //     &g_m.limbs[i].value, &res_gm.limbs[i].value
                    //  );
                    // println!("remcell is#### \t{:?}", &g_m.limbs[i].cell);
                    // println!("                      _______________________________                      ");
                    // println!("resultcell is \t {:?}", &res_gm.limbs[i].cell);
                    region.constrain_equal(
                        g_m.limbs[i].clone().cell.unwrap().cell(),
                        res_gm.limbs[i].clone().cell.unwrap().cell(),
                    )?;
                }

                let r = helper_chip.assign_base(&mut region, &mut offset, &self.r)?;
                let n = helper_chip.assign_exp(&mut region, &mut offset, &self.n)?;
                let check_mod =
                    helper_chip.assign_results(&mut region, &mut offset, &self.modulus)?;
                let res_rn =
                    helper_chip.assign_results(&mut region, &mut offset, &self.bn_test_res2)?;
                let r_n =
                    rn_chip.mod_exp(&mut region, &mut range_chip, &mut offset, &r, &n, &modulus)?;
                println!("##################################################################");
                for i in 0..4 {
                    // println!(
                    //     "r_n is {:?}, \t res_rn is {:?}",
                    //     &r_n.limbs[i].value, &res_rn.limbs[i].value
                    // );
                    // println!("remcell is#### \t{:?}", &r_n.limbs[i].cell);
                    // println!("                      _______________________________                      ");
                    // println!("resultcell is \t {:?}", &res_rn.limbs[i].cell);
                    region.constrain_equal(
                        r_n.limbs[i].clone().cell.unwrap().cell(),
                        res_rn.limbs[i].clone().cell.unwrap().cell(),
                    )?;
                }
                let mul_result =
                    helper_chip.assign_results(&mut region, &mut offset, &self.bn_test_mulout)?;
                let n_sqr = self.n.clone().mul(self.n.clone());
                let n_sqr = helper_chip.assign_results(&mut region, &mut offset, &n_sqr)?;

                let mul_out = mul_chip.mod_mult(
                    &mut region,
                    &mut range_chip,
                    &mut offset,
                    &g_m,
                    &r_n,
                    &modulus,
                )?;
                for i in 0..4 {
                    println!(
                        "circuit out is {:?}, \ncalculatedd_out is {:?}",
                        &mul_out.limbs[i].value, &mul_result.limbs[i].value
                    );
                    println!(
                        "n^2 out is {:?}, \nmodulus{:?}",
                        &n_sqr.limbs[i].value, &check_mod.limbs[i].value
                    );
                    //   println!("remcell is \t{:?}", &mul_out.limbs[i].clone().cell.unwrap());
                    //println!("resultcell is \t {:?}", &mul_result.limbs[i].cell);
                    // region.constrain_equal(
                    //     mul_out.limbs[i].clone().cell.unwrap().cell(),
                    //     mul_result.limbs[i].clone().cell.unwrap().cell(),
                    // )?;
                    //     region.constrain_instance(mul_out.limbs[i].clone().cell.unwrap().cell(), se, row)
                    // println!("check_mod is \t{:?}", &check_mod.limbs[i].clone().cell.unwrap());
                    // println!("n_sqr is \t {:?}", &n_sqr.limbs[i].clone().cell.unwrap());
                    // region.constrain_equal(
                    //     check_mod.limbs[i].clone().cell.unwrap().cell(),
                    //     n_sqr.limbs[i].clone().cell.unwrap().cell(),
                    // )?;
                    println!("$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$");

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

    #[test]
    fn test_enc2_circuit() -> Result<(), CircuitError> {
        const NUM_TESTS: usize = 5;

        let mut bn_g_test_vectors: Vec<BigUint> = Vec::with_capacity(NUM_TESTS);
        let mut bn_r_test_vectors: Vec<BigUint> = Vec::with_capacity(NUM_TESTS);

        let mut bn_modulus_test_vectors: Vec<BigUint> = Vec::with_capacity(NUM_TESTS);
        let mut bn_m_test_vectors: Vec<BigUint> = Vec::with_capacity(NUM_TESTS);
        let mut bn_n_test_vectors: Vec<BigUint> = Vec::with_capacity(NUM_TESTS);

        let bit_len_g: [usize; NUM_TESTS] = [10, 14, 8, 250, 255];
        let bit_len_r: [usize; NUM_TESTS] = [10, 14, 8, 25, 254];
        let bit_len_n: [usize; NUM_TESTS] = [10, 16, 40, 50, 60];
        let bit_len_m: [usize; NUM_TESTS] = [10, 14, 8, 10, 15];
        //   let bit_len_n = bit_len_m.clone();

        for i in 0..NUM_TESTS {
            bn_g_test_vectors.push(get_random_x_bit_bn(bit_len_g[i]));
            bn_n_test_vectors.push(get_random_x_bit_bn(bit_len_n[i]));
            bn_modulus_test_vectors.push(
                bn_n_test_vectors[i]
                    .clone()
                    .mul(bn_n_test_vectors[i].clone()),
            );
            bn_m_test_vectors.push(get_random_x_bit_bn(bit_len_m[i]));
            bn_r_test_vectors.push(get_random_x_bit_bn(bit_len_r[i]));
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
            let one = BigUint::try_from(1).unwrap();
            let bn_test_mulout = temp.clone().modpow(&one, &modulus_testcase);
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
                bn_test_mulout.clone().to_str_radix(16)
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

            let prover = match MockProver::run(20, &test_circuit, vec![]) {
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

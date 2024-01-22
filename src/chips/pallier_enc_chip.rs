//! Chip that implements instructions to check: a * b + c == d (mod 2^256) where
//! a, b, c and d are all 256-bit words.
//!
//! The circuit layout is as follows:
#[rustfmt::skip]
// | col0   | col1      | col2      | col3      | instance      |
// |--------|-----------|-----------|-----------|-----------|
// | q_limb0| q_limb1   | q_limb2   | q_limb3   | q_limb0   |
// | m_limb0| m_limb1   | m_limb2   | m_limb3   | q_limb1   |
// | q_m0   | q_m1      | q_m2      | q_m3      | q_limb2   |
// | r_limb0| r_limb1   | r_limb2   | r_limb3   | q_limb3   |
// | n_limb0| n_limb1   | n_limb2   | n_limb3   | fin_out0  |
// | r_n0   | r_n1      | r_n2      | r_n3      | fin_out1  |
// | fin_out| fin_out1  | fin_out2  | fin_out3  | fin_out2  |
// | 0      | -         | -         | -         | -         |
// |--------|-----------|-----------|-----------|-----------|
// last row is padding to fit in 8 rows range_check_64 chip
use std::marker::PhantomData;
use crate::chips::helper::{HelperChip, HelperChipConfig};
use halo2_proofs::{
    arithmetic::{Field, FieldExt},
    circuit::{AssignedCell, Layouter, Region, SimpleFloorPlanner, Value},
    halo2curves::{bn256::Fr, group::ff::PrimeField},
    plonk::{
        Advice, Circuit, Column, ConstraintSystem, Error, Expression, Fixed, Instance, TableColumn,
        VirtualCells,
    },
    poly::Rotation,
};
use mylib::circuits::modexp::Number;
use mylib::circuits::Limb;
use mylib::circuits::{
    modexp::ModExpChip,
    range::{RangeCheckChip, RangeCheckConfig},
    CommonGateConfig,
};
use mylib::utils::{bn_to_field, field_to_bn};
use num_bigint::BigUint;
use std::ops::Div;

/// Config for the MulAddChip.
#[derive(Clone, Debug)]
pub struct PallEncConfig {
    pub col_i: [Column<Advice>; 4],
    pub instance: Column<Instance>,
    pub modexp_config: CommonGateConfig,
    pub helper_config: HelperChipConfig,
    pub range_check: RangeCheckConfig,
}
#[derive(Debug, Clone)]
pub struct PallEncChip<F: Field> {
    config: PallEncConfig,
    _marker: PhantomData<F>,
}

pub fn from_bn_to_value(bn: &BigUint) -> [Value<Fr>; 4] {
    let x: Number<Fr> = Number::from_bn(bn);
    [
        Value::known(x.limbs[0].value),
        Value::known(x.limbs[1].value),
        Value::known(x.limbs[2].value),
        Value::known(x.limbs[3].value),
    ]
}

impl PallEncChip<Fr> {
    pub fn construct(config: PallEncConfig) -> Self {
        Self {
            config,
            _marker: PhantomData,
        }
    }

    pub fn configure(
        meta: &mut ConstraintSystem<Fr>,
        advice: [Column<Advice>; 4],
        instance: Column<Instance>,
    ) -> PallEncConfig {
        let col_0 = advice[0];
        let col_1 = advice[1];
        let col_2 = advice[2];
        let col_3 = advice[3];

        meta.enable_equality(col_0);
        meta.enable_equality(col_1);
        meta.enable_equality(col_2);
        meta.enable_equality(col_3);
        meta.enable_equality(instance);

        let range_check = RangeCheckChip::<Fr>::configure(meta);

        PallEncConfig {
            col_i: [col_0, col_1, col_2, col_3],
            instance: instance,
            modexp_config: ModExpChip::<Fr>::configure(meta, &range_check),
            helper_config: HelperChip::configure(meta),
            range_check,
        }
    }

    pub fn load_private(
        &self,
        mut layouter: impl Layouter<Fr>,
        input: Value<Fr>,
        i: usize,
    ) -> Result<AssignedCell<Fr, Fr>, Error> {
        layouter.assign_region(
            || "load private",
            |mut region| {
                region.assign_advice(|| "private input", self.config.col_i[i], 0, || input)
            },
        )
    }
    pub fn load_from_instance(
        &self,
        mut layouter: impl Layouter<Fr>,
        row: usize,
        i: usize,
    ) -> Result<AssignedCell<Fr, Fr>, Error> {
        layouter.assign_region(
            || "load from instance to advice",
            |mut region| {
                region.assign_advice_from_instance(
                    || "from instance",
                    self.config.instance,
                    row,
                    self.config.col_i[i],
                    0,
                )
            },
        )
    }

    pub fn expose_public(
        &self,
        mut layouter: impl Layouter<Fr>,
        cell: &AssignedCell<Fr, Fr>,
        row: usize,
    ) -> Result<(), Error> {
        layouter.constrain_instance(cell.cell(), self.config.instance, row)
    }
}

#[derive(Default)]
struct PallEncCircuit {
    g: BigUint,
    m: BigUint,
    r: BigUint,
    n: BigUint,
    modulus: BigUint,
}

impl Circuit<Fr> for PallEncCircuit {
    type Config = PallEncConfig;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self::default()
    }

    fn configure(meta: &mut ConstraintSystem<Fr>) -> Self::Config {
        let col_0 = meta.advice_column();
        let col_1 = meta.advice_column();
        let col_2 = meta.advice_column();
        let col_3 = meta.advice_column();

        let instance = meta.instance_column();
        PallEncChip::configure(meta, [col_0, col_1, col_2, col_3], instance)
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<Fr>,
    ) -> Result<(), Error> {
        let chip = PallEncChip::construct(config.clone());
        let gm_chip = ModExpChip::<Fr>::new(chip.config.modexp_config.clone());
        let rn_chip = ModExpChip::<Fr>::new(chip.config.modexp_config.clone());

        let mul_chip = ModExpChip::<Fr>::new(chip.config.modexp_config.clone());

        let mut range_chip = RangeCheckChip::<Fr>::new(chip.config.range_check.clone());

        let g_num: Number<Fr> = Number::from_bn(&self.g);
        let m_num: Number<Fr> = Number::from_bn(&self.m);
        let r_num: Number<Fr> = Number::from_bn(&self.r);
        let n_num: Number<Fr> = Number::from_bn(&self.n);
        let mod_num: Number<Fr> = Number::from_bn(&self.modulus);
        let input_m = from_bn_to_value(&self.m);
        let mut g_cell: Vec<AssignedCell<Fr, Fr>> = vec![];
        let mut m_cell: Vec<AssignedCell<Fr, Fr>> = vec![];
        let mut final_out_cell: Vec<AssignedCell<Fr, Fr>> = vec![];

        layouter.assign_region(
            || "Matrix 2",
            |mut region| {
                range_chip.initialize(&mut region)?;
                let mut offset = 0;
                for i in 0..4 {
                    g_cell.push(region.assign_advice_from_instance(
                        || "Load g from instance to row0",
                        config.instance,
                        i,
                        config.col_i[i],
                        offset,
                    )?);
                    m_cell.push(region.assign_advice(
                        || "Load m into row1",
                        config.col_i[i],
                        offset + 1,
                        || input_m[i],
                    )?);
                }
                let gm = gm_chip.mod_exp(
                    &mut region,
                    &mut range_chip,
                    &mut offset,
                    &g_num,
                    &m_num,
                    &mod_num,
                )?;

                let input_r = from_bn_to_value(&self.r);
                let input_n = from_bn_to_value(&self.n);
                for i in 0..4 {
                    region
                        .assign_advice(
                            || "load g^m",
                            config.col_i[i],
                            offset + 2,
                            || Value::known(gm.limbs[i].clone().value),
                        )
                        .unwrap();
                }

                for i in 0..4 {
                    region.assign_advice(
                        || "load r",
                        config.col_i[i],
                        offset + 3,
                        || input_r[i],
                    )?;
                    region.assign_advice(
                        || "load n",
                        config.col_i[i],
                        offset + 4,
                        || input_n[i],
                    )?;
                }
                let rn = rn_chip.mod_exp(
                    &mut region,
                    &mut range_chip,
                    &mut offset,
                    &r_num,
                    &n_num,
                    &mod_num,
                )?;

                for i in 0..4 {
                    region.assign_advice(
                        || "load r^n",
                        config.col_i[i],
                        offset + 5,
                        || Value::known(rn.limbs[i].clone().value),
                    )?;
                }

                let mul_out = mul_chip.mod_mult(
                    &mut region,
                    &mut range_chip,
                    &mut offset,
                    &gm,
                    &rn,
                    &mod_num,
                )?;

                for i in 0..4 {
                    final_out_cell.push(region.assign_advice(
                        || "load final out",
                        config.col_i[i],
                        offset + 6,
                        || Value::known(mul_out.limbs[i].clone().value),
                    )?);
                }

                Ok(())
            },
        )?;
        for i in 0..4 {
            chip.expose_public(
                layouter.namespace(|| "expose final output"),
                &final_out_cell[i],
                4 + i,
            )?;
        }
        Ok(())
    }
}
mod tests {

    use std::ops::{Div, Mul};

    use super::{from_bn_to_value, PallEncCircuit};

    use crate::utils::{get_random_x_bit_bn, CircuitError};
    use halo2_proofs::{
        arithmetic::{Field, FieldExt},
        circuit::{AssignedCell, Layouter, Region, SimpleFloorPlanner},
        halo2curves::{bn256::Fr, group::ff::PrimeField},
        plonk::{
            Advice, Circuit, Column, ConstraintSystem, Error, Expression, Fixed, Instance,
            TableColumn, VirtualCells,
        },
        poly::Rotation,
    };
    use halo2_proofs::{circuit::Value, dev::MockProver};
    use mylib::circuits::modexp::Number;
    use mylib::utils::{bn_to_field, field_to_bn};
    use num_bigint::BigUint;

    fn from_bn_to_fr(bn: &BigUint) -> [Fr; 4] {
        let limb0 = bn.modpow(&BigUint::from(1u128), &BigUint::from(1u128 << 108));
        println!("0");

        let limb1 = (bn - limb0.clone()).div(
            BigUint::from(1u128 << 108).modpow(&BigUint::from(1u128), &BigUint::from(1u128 << 108)),
        );
        println!("1");
        let limb2 = bn
            .div(BigUint::from(1u128 << 108))
            .div(BigUint::from(1u128 << 108));
        let native = bn % (field_to_bn(&(-Fr::one())) + BigUint::from(1u128));

        let l0: Fr = bn_to_field(&limb0);
        let l1: Fr = bn_to_field(&limb1);
        let l2: Fr = bn_to_field(&limb2);
        let l3: Fr = bn_to_field(&native);

        [l0, l1, l2, l3]
    }

    #[test]
    fn test_enc_chip() {
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

            let g_fr: Number<Fr> = Number::from_bn(&g);
            let final_fr: Number<Fr> = Number::from_bn(&bn_test_mulout);

            let mut public_input: Vec<Fr> = vec![];
            public_input.extend(
                [
                    g_fr.limbs[0].value,
                    g_fr.limbs[1].value,
                    g_fr.limbs[2].value,
                    g_fr.limbs[3].value,
                ]
                .iter(),
            );
            public_input.extend(
                [
                    final_fr.limbs[0].value,
                    final_fr.limbs[1].value,
                    final_fr.limbs[2].value,
                    final_fr.limbs[3].value,
                ]
                .iter(),
            );

            println!("public inputs {:?}", public_input);
            //  print!("g vvalue {:?}",g_fr);
            //    print!("final_fr vvalue {:?}",final_fr);

            let test_circuit = PallEncCircuit {
                g,
                m,
                r,
                n,
                modulus,
            };

            let prover =
                MockProver::run(20, &test_circuit, vec![public_input.to_vec().clone()]).unwrap();
            prover.assert_satisfied();
        }
    }
}

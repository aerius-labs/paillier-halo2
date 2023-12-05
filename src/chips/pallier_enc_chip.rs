//! Chip that implements instructions to check: a * b + c == d (mod 2^256) where
//! a, b, c and d are all 256-bit words.
//!
//! The circuit layout is as follows:
#[rustfmt::skip]
// | q_step | col0      | col1      | col2      | col3      |
// |--------|-----------|-----------|-----------|-----------|
// | 1      | a_limb0   | a_limb1   | a_limb2   | a_limb3   |
// | 0      | b_limb0   | b_limb1   | b_limb2   | b_limb3   |
// | 0      | c_lo      | c_hi      | d_lo      | d_hi      |
// | 0      | carry_lo0 | carry_lo1 | carry_lo2 | carry_lo3 |
// | 0      | carry_lo4 | -         | -         | -         |
// | 0      | carry_hi0 | carry_hi1 | carry_hi2 | carry_hi3 |
// | 0      | carry_hi4 | -         | -         | -         |
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
    let limb0 = bn.modpow(&BigUint::from(1u128), &BigUint::from(1u128 << 108));
    let limb1 = (bn - limb0.clone()).div(
        BigUint::from(1u128 << 108).modpow(&BigUint::from(1u128), &BigUint::from(1u128 << 108)),
    );
    let limb2 = bn
        .div(BigUint::from(1u128 << 108))
        .div(BigUint::from(1u128 << 108));
    let native = bn % (field_to_bn(&(-Fr::one())) + BigUint::from(1u128));

    [
        Value::known(bn_to_field(&limb0)),
        Value::known(bn_to_field(&limb1)),
        Value::known(bn_to_field(&limb2)),
        Value::known(bn_to_field(&native)),
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

        // PallEncConfig {
        //     col_i:[ col_0,
        //      col_1,
        //      col_2,
        //      col_3],
        //     instance:instance,
        //     range_chech,
        //     modexp_config: ModExpChip::<Fr>::configure(meta, &range_check),
        //     helper_config: HelperChip::configure(meta),
        // }
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
        input: Value<Fr>,
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

//#[derive(Default)]
// struct PallEncCircuit<Fr> {
//     g: Vec<Value<Fr>>,
//     m: Vec<Value<Fr>>,
//     r: Vec<Value<Fr>>,
//     n: Vec<Value<Fr>>,
//     modulus: Vec<Value<Fr>>,
//     bn_test_res1: Vec<Value<Fr>>,
//     bn_test_res2: Vec<Value<Fr>>,
//     bn_test_mulout: Vec<Value<Fr>>,
// }
#[derive(Default)]
struct PallEncCircuit {
    g: BigUint,
    m: BigUint,
    r: BigUint,
    n: BigUint,
    modulus: BigUint,
    bn_test_res1: BigUint,
    bn_test_res2: BigUint,
    bn_test_mulout: BigUint,
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

        let helper_chip = HelperChip::new(chip.config.helper_config.clone());
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
                        0,
                        config.col_i[i],
                        0,
                    )?);
                    m_cell.push(region.assign_advice(
                        || "Load m into row1",
                        config.col_i[i],
                        0,
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
                            0,
                            || Value::known(gm.limbs[i].clone().value),
                        )
                        .unwrap();
                }

                for i in 0..4 {
                    region.assign_advice(|| "load r", config.col_i[i], 0, || input_r[i])?;
                    region.assign_advice(|| "load n", config.col_i[i], 0, || input_n[i])?;
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
                        offset,
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
                        offset,
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

        // for i in 0..4{
        //     g_val.push(chip.load_from_instance(layouter, 0, i, self.g[i].clone())?);
        // }
        // let mut m_val:Vec<AssignedCell<Fr,Fr>>=vec![];
        // for i in 0..4{
        //   m_val.push(chip.load_private(layouter, self.m[i].clone(), i)?);
        // }
        // let gm_chip = ModExpChip::<Fr>::new(config.clone().modexp_config);
        // // let n = Number {
        // //     limbs: [
        // //         Limb::new(g_val[0].clone(), self.g[1]),
        // //         Limb::new(g_val[1].clone(), self.g[2].clone()),
        // //         Limb::new(g_val[2].clone(), self.g[3].clone()),
        // //         Limb::new(g_val[3].clone(), self.g[4].clone()),
        // //     ],
        // // };
        // let mut r_val:Vec<AssignedCell<Fr,Fr>>=vec![];
        // for i in 0..4{
        //     r_val.push(chip.load_private(layouter, self.r[i].clone(), i)?);
        // }
        // let mut n_val:Vec<AssignedCell<Fr,Fr>>=vec![];
        // for i in 0..4{
        //   n_val.push(chip.load_private(layouter, self.n[i].clone(), i)?);
        // }
    }
}

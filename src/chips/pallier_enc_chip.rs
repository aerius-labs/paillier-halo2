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
use halo2_proofs::{
    arithmetic::{Field, FieldExt},
    circuit::{Region, Value,AssignedCell,SimpleFloorPlanner,Layouter},
    halo2curves::{bn256::Fr, group::ff::PrimeField},
    plonk::{Circuit,Advice, Column, ConstraintSystem, Error, Expression,TableColumn, VirtualCells,Fixed, Instance},
    poly::Rotation,

    
};
use num_bigint::BigUint;
use mylib::circuits::{
    modexp::ModExpChip,
    range::{RangeCheckChip, RangeCheckConfig},
    CommonGateConfig,
};
use crate::chips::helper::{HelperChip, HelperChipConfig};
use mylib::circuits::modexp::Number;
use mylib::circuits::Limb;



/// Config for the MulAddChip.
#[derive(Clone, Debug)]
pub struct PallEncConfig {
    pub col_i: [Column<Advice>;4],
    pub instance:Column<Instance>,
    pub range_check:RangeCheckConfig,
    pub modexp_config: CommonGateConfig,
  //  pub helper_config: HelperChipConfig,
}
#[derive(Debug, Clone)]
pub struct PallEncChip <F:Field>{
    config: PallEncConfig,
    _marker: PhantomData<F>,
}

impl PallEncChip<Fr> {
    pub fn construct(config: PallEncConfig) -> Self {
        Self { config,_marker: PhantomData }
    }

    pub fn configure(
        meta: &mut ConstraintSystem<Fr>,
        advice: [Column<Advice>; 4],
        instance: Column<Instance>,
    ) -> PallEncConfig {
        let col_0 = advice[0];
        let col_1 = advice[1];
        let col_2 = advice[2];
        let col_3= advice[3];
       
        meta.enable_equality(col_0);
        meta.enable_equality(col_1);
        meta.enable_equality(col_2);
        meta.enable_equality(col_3);
        meta.enable_equality(instance);

      
        let range_check=RangeCheckChip::<Fr>::configure(meta);

        PallEncConfig {
            col_i:[ col_0,
             col_1,
             col_2,
             col_3],
            instance:instance,
            range_check:range_check,
            modexp_config: ModExpChip::<Fr>::configure(meta, &range_check),
           // helper_config: HelperChip::configure(meta),
        }
    }

    pub fn load_private(
        &self,
        mut layouter: impl Layouter<Fr>,
        input: Value<Fr>,
        i:usize
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
        row:usize,
        i:usize,
        input: Value<Fr>,
    ) -> Result<AssignedCell<Fr, Fr>, Error> {
        layouter.assign_region(
            || "load from instance to advice",
            |mut region| {
                region.assign_advice_from_instance(||"from instance",self.config.instance, row, self.config.col_i[i], 0)
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
struct PallEncCircuit<Fr> {
    g: Vec<Value<Fr>>,
    m: Vec<Value<Fr>>,
    r: Vec<Value<Fr>>,
    n: Vec<Value<Fr>>,
    modulus: Vec<Value<Fr>>,
    bn_test_res1: Vec<Value<Fr>>,
    bn_test_res2: Vec<Value<Fr>>,
    bn_test_mulout: Vec<Value<Fr>>,
}

impl  Circuit<Fr> for PallEncCircuit<Fr> {
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
        PallEncChip::configure(meta, [col_0, col_1, col_2,col_3], instance)
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<Fr>,
    ) -> Result<(), Error> {
        let chip = PallEncChip::construct(config.clone());
        let mut g_val:Vec<AssignedCell<Fr,Fr>>=vec![];
        for i in 0..4{
            g_val.push(chip.load_from_instance(layouter, 0, i, self.g[i].clone())?);
        }
        let mut m_val:Vec<AssignedCell<Fr,Fr>>=vec![];
        for i in 0..4{
          m_val.push(chip.load_private(layouter, self.m[i].clone(), i)?);
        }
        let gm_chip = ModExpChip::<Fr>::new(config.clone().modexp_config);
        // let n = Number {
        //     limbs: [
        //         Limb::new(g_val[0].clone(), self.g[1]),
        //         Limb::new(g_val[1].clone(), self.g[2].clone()),
        //         Limb::new(g_val[2].clone(), self.g[3].clone()),
        //         Limb::new(g_val[3].clone(), self.g[4].clone()),
        //     ],
        // };
        let mut r_val:Vec<AssignedCell<Fr,Fr>>=vec![];
        for i in 0..4{
            r_val.push(chip.load_private(layouter, self.r[i].clone(), i)?);
        }
        let mut n_val:Vec<AssignedCell<Fr,Fr>>=vec![];
        for i in 0..4{
          n_val.push(chip.load_private(layouter, self.n[i].clone(), i)?);
        }
     
        Ok(())
    }
}


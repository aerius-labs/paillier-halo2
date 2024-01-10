use halo2_proofs::circuit::Region;
use halo2_proofs::halo2curves::bn256::Fr;
use halo2_proofs::plonk::{ConstraintSystem, Error};
use halo2_proofs::{
    circuit::Chip,
    plonk::{Advice, Column},
};
use mylib::circuits::modexp::Number;
use mylib::circuits::Limb;
use mylib::value_for_assign;
use num_bigint::BigUint;

#[derive(Clone, Debug)]
pub struct HelperChipConfig {
    limb: Column<Advice>,
}

#[derive(Clone, Debug)]
pub struct HelperChip {
    config: HelperChipConfig,
}

impl Chip<Fr> for HelperChip {
    type Config = HelperChipConfig;
    type Loaded = ();

    fn config(&self) -> &Self::Config {
        &self.config
    }

    fn loaded(&self) -> &Self::Loaded {
        &()
    }
}

impl HelperChip {
    pub fn new(config: HelperChipConfig) -> Self {
        HelperChip { config }
    }

    pub fn configure(cs: &mut ConstraintSystem<Fr>) -> HelperChipConfig {
        let limb = cs.advice_column();
        cs.enable_equality(limb);
        HelperChipConfig { limb }
    }

    pub fn assign_base(
        &self,
        _region: &mut Region<Fr>,
        _offset: &mut usize,
        base: &BigUint,
    ) -> Result<Number<Fr>, Error> {
        Ok(Number::from_bn(base))
    }

    pub fn assign_modulus(
        &self,
        _region: &mut Region<Fr>,
        _offset: &mut usize,
        modulus: &BigUint,
    ) -> Result<Number<Fr>, Error> {
        Ok(Number::from_bn(modulus))
    }

    pub fn assign_exp(
        &self,
        _region: &mut Region<Fr>,
        _offset: &mut usize,
        exponent: &BigUint,
    ) -> Result<Number<Fr>, Error> {
        Ok(Number::from_bn(exponent))
    }

    pub fn assign_results(
        &self,
        region: &mut Region<Fr>,
        offset: &mut usize,
        result: &BigUint,
    ) -> Result<Number<Fr>, Error> {
        let n = Number::from_bn(result);
        let mut cells = vec![];
        for i in 0..4 {
            let c = region.assign_advice(
                || "assign input".to_string(),
                self.config.limb,
                *offset + i,
                || value_for_assign!(n.limbs[i].value),
            )?;
            cells.push(Some(c));
            *offset += 1;
        }
        let n = Number {
            limbs: [
                Limb::new(cells[0].clone(), n.limbs[0].value),
                Limb::new(cells[1].clone(), n.limbs[1].value),
                Limb::new(cells[2].clone(), n.limbs[2].value),
                Limb::new(cells[3].clone(), n.limbs[3].value),
            ],
        };
        Ok(n)
    }
}

use halo2_base::{ utils::BigPrimeField, Context, halo2_proofs::{ plonk::Error, circuit::Value } };
use num_bigint::BigUint;

use crate::big_uint::{ chip::BigUintChip, AssignedBigUint, Fresh, RefreshAux };

#[derive(Debug, Clone)]
pub struct PaillierChip<'a, F: BigPrimeField> {
    pub biguint: &'a BigUintChip<'a, F>,
    pub n: &'a BigUint,
    pub g: &'a BigUint,
}

impl<'a, F: BigPrimeField> PaillierChip<'a, F> {
    pub fn construct(biguint: &'a BigUintChip<'a, F>, n: &'a BigUint, g: &'a BigUint) -> Self {
        Self {
            biguint,
            n,
            g,
        }
    }

    pub fn n_bits(&self) -> usize {
        self.n.bits() as usize
    }

    pub fn g_bits(&self) -> usize {
        self.g.bits() as usize
    }

    pub fn encrypt(
        &self,
        ctx: &mut Context<F>,
        m: &BigUint,
        r: &BigUint
    ) -> Result<AssignedBigUint<F, Fresh>, Error> {
        let n_assigned = self.biguint.assign_integer(
            ctx,
            Value::known(self.n.clone()),
            self.n_bits()
        )?;
        let g_assigned = self.biguint.assign_integer(
            ctx,
            Value::known(self.g.clone()),
            self.g_bits()
        )?;
        let r_assigned = self.biguint.assign_integer(
            ctx,
            Value::known(r.clone()),
            r.bits() as usize
        )?;

        let n2 = self.biguint.square(ctx, &n_assigned)?;
        let aux = RefreshAux::new(
            self.biguint.limb_bits,
            n_assigned.num_limbs(),
            n_assigned.num_limbs()
        );
        let n2 = self.biguint.refresh(ctx, &n2, &aux)?;

        let gm = self.biguint.pow_mod_fixed_exp(ctx, &g_assigned, &m, &n2)?;
        let rn = self.biguint.pow_mod_fixed_exp(ctx, &r_assigned, &self.n, &n2)?;

        let c = self.biguint.mul_mod(ctx, &gm, &rn, &n2)?;

        Ok(c)
    }
}

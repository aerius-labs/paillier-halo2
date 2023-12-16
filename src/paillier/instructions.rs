use halo2_base::{ utils::PrimeField, Context, halo2_proofs::plonk::Error };

use crate::big_uint::{ AssignedBigUint, Fresh };

pub trait PaillierInstructions<F: PrimeField> {
    fn paillier_encrypt<'v>(
        &self,
        ctx: &mut Context<'v, F>,
        n: &AssignedBigUint<'v, F, Fresh>,
        g: &AssignedBigUint<'v, F, Fresh>,
        m: &AssignedBigUint<'v, F, Fresh>,
        r: &AssignedBigUint<'v, F, Fresh>
    ) -> Result<AssignedBigUint<'v, F, Fresh>, Error>;
}

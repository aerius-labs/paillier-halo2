use std::marker::PhantomData;

use halo2_base::{
    utils::{ BigPrimeField, decompose_biguint, ScalarField },
    gates::{ GateChip, range::RangeConfig, flex_gate::FlexGateConfig },
    Context,
    halo2_proofs::{ plonk::Error, circuit::Value },
    QuantumCell,
    AssignedValue,
};
use halo2_ecc::bigint::mul_no_carry;
use num_bigint::BigUint;

use super::AssignedBigUint;

#[derive(Clone, Debug)]
pub struct BigUintConfig<F: BigPrimeField> {
    _marker: PhantomData<F>,
}

impl<F: BigPrimeField> BigUintConfig<F> {
    fn mul(
        &self,
        gate: &mut GateChip<F>,
        ctx: &mut Context<F>,
        a: &AssignedBigUint<F>,
        b: &AssignedBigUint<F>
    ) -> Result<AssignedBigUint<F>, Error> {
        let n1 = a.num_limbs();
        let n2 = b.num_limbs();
        let num_limbs = n1 + n2 - 1;
        let zero_value = ctx.load_zero();
        let a = a.extend_limbs(num_limbs - n1, zero_value.clone());
        let b = b.extend_limbs(num_limbs - n2, zero_value.clone());
        let num_limbs_log2_ceil = (num_limbs as f32).log2().ceil() as usize;
        let int = mul_no_carry::truncate(gate, ctx, a.int, b.int, num_limbs_log2_ceil);
        let value = a.value.zip(b.value).map(|(a, b)| a * b);
        Ok(AssignedBigUint::new(int, value))
    }
}

#[cfg(test)]
mod test {
    use std::marker::PhantomData;

    use halo2_base::{
        utils::BigPrimeField,
        halo2_proofs::{ plonk::{ Circuit, ConstraintSystem }, circuit::SimpleFloorPlanner },
    };
    use num_bigint::BigUint;

    use crate::biguint::chip::BigUintConfig;

    #[test]
    fn test_mul() {
        struct MulCircuit {
            a: BigUint,
            b: BigUint,
        }

        impl<F: BigPrimeField> Circuit<F> for MulCircuit {
            type Config = BigUintConfig<F>;
            type FloorPlanner = SimpleFloorPlanner;

            fn without_witnesses(&self) -> Self {
                unimplemented!()
            }

            fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
                BigUintConfig {
                    _marker: PhantomData,
                }
            }

            fn synthesize(
                &self,
                config: Self::Config,
                mut layouter: impl halo2_base::halo2_proofs::circuit::Layouter<F>
            ) -> Result<(), halo2_base::halo2_proofs::plonk::Error> {
                layouter.assign_region(
                    || "mul test",
                    |region| {}
                )
            }
        }
    }
}

use halo2_base::{
    gates::{flex_gate::threads::SinglePhaseCoreManager, RangeChip},
    halo2_proofs::{circuit::Value, plonk::Error},
    utils::BigPrimeField,
};
use num_bigint::BigUint;

use crate::{
    big_uint::{chip::BigUintChip, AssignedBigUint, Fresh, RefreshAux},
    paillier::PaillierChip,
};

#[derive(Debug, Clone)]
pub struct PaillierInputs {
    pub enc_bits: usize,
    pub limb_bits: usize,
    pub n: BigUint,
    pub g: BigUint,
    pub m: BigUint,
    pub r: BigUint,
    pub res: BigUint,
}
#[derive(Debug, Clone)]
pub struct PaillierInputsAdd {
    pub limb_bits: usize,
    pub enc_bits: usize,
    pub n: BigUint,
    pub g: BigUint,
    pub m1: BigUint,
    pub r1: BigUint,
    pub m2: BigUint,
    pub r2: BigUint,
    pub c1: BigUint,
    pub c2: BigUint,
    pub res: BigUint,
}

pub fn paillier_enc_test<F: BigPrimeField>(
    pool: &mut SinglePhaseCoreManager<F>,
    range: &RangeChip<F>,
    inputs: PaillierInputs,
) -> Result<AssignedBigUint<F, Fresh>, Error> {
    let ctx = pool.main();
    let biguint_chip = BigUintChip::construct(range, inputs.limb_bits);
    let n_b = inputs.n.clone();
    let n = biguint_chip
        .assign_integer(ctx, Value::known(inputs.n), inputs.enc_bits)
        .unwrap();
    let g_b = inputs.g.clone();
    let g = biguint_chip
        .assign_integer(ctx, Value::known(inputs.g), inputs.enc_bits)
        .unwrap();
    let r = biguint_chip
        .assign_integer(ctx, Value::known(inputs.r), inputs.enc_bits)
        .unwrap();
    let paillier_chip = PaillierChip::construct(&biguint_chip, inputs.enc_bits, &n, n_b, &g);

    let c_assigned = paillier_chip.encrypt(ctx, inputs.m, &r).unwrap();

    let res_assigned = biguint_chip
        .assign_integer(ctx, Value::known(inputs.res.clone()), inputs.enc_bits * 2)
        .unwrap();

    c_assigned.value().zip(res_assigned.value()).map(|(a, b)| {
        assert_eq!(a, b);
    });
    biguint_chip
        .assert_equal_fresh(ctx, &c_assigned, &res_assigned)
        .unwrap();
    Ok(c_assigned)
}

// pub fn paillier_enc_add_test<F: BigPrimeField>(
//     pool: &mut SinglePhaseCoreManager<F>,
//     range: &RangeChip<F>,
//     inputs: PaillierInputsAdd,
// ) {
//     let biguint_chip = BigUintChip::construct(range, inputs.limb_bits);
//     let ctx = pool.main();

//     let paillier_chip =
//     PaillierChip::construct(&biguint_chip, inputs.enc_bits, &inputs.n, &inputs.g);

//     let  c1_assigned = biguint_chip
//     .assign_integer(ctx, Value::known(inputs.c1.clone()), inputs.enc_bits*2)
//     .unwrap();
//     let  c2_assigned  = biguint_chip
//     .assign_integer(ctx, Value::known(inputs.c2.clone()), inputs.enc_bits*2)
//     .unwrap();
//     let  expected_res=paillier_chip.add(ctx, &c1_assigned, &c2_assigned).unwrap();
//     let res_assigned = biguint_chip
//     .assign_integer(ctx, Value::known(inputs.res.clone()), inputs.enc_bits*2)
//     .unwrap();
//     expected_res.value().zip(res_assigned.value()).map(|(a, b)| {
//         assert_eq!(a, b);
//     });
//     biguint_chip
//         .assert_equal_fresh(ctx, &expected_res, &res_assigned)
//         .unwrap();
// }

pub fn paillier_add(n: &BigUint, c1: &BigUint, c2: &BigUint) -> BigUint {
    let n2 = n * n;
    (c1 * c2) % n2
}

#[cfg(test)]
mod test {

    //  use halo2_base::halo2_proofs::halo2curves::grumpkin::Fr;
    use halo2_base::halo2_proofs::halo2curves::bn256::Fr;
    use halo2_base::{gates::RangeChip, halo2_proofs::circuit::Value, utils::testing::base_test};
    use num_bigint::BigUint;
    use num_bigint::RandBigInt;
    use num_traits::One;
    use rand::thread_rng;

    use crate::big_uint::{chip::BigUintChip, AssignedBigUint, Fresh, RefreshAux};
    use crate::{
        bench::{paillier_add, paillier_enc_test, PaillierInputs, PaillierInputsAdd},
        paillier::paillier_enc,
    };
    // paillier_enc_add_test
    use halo2_ecc::bigint::OverflowInteger;
    //BigPrimeField

    #[test]
    fn bench_paillier_enc() {
        const ENC_BIT_LEN: usize = 128;
        const LIMB_BIT_LEN: usize = 64;

        let mut rng = thread_rng();

        let n = rng.gen_biguint(ENC_BIT_LEN as u64);
        let g = rng.gen_biguint(ENC_BIT_LEN as u64);
        let m = rng.gen_biguint(ENC_BIT_LEN as u64);
        let r = rng.gen_biguint(ENC_BIT_LEN as u64);

        let expected_c = paillier_enc(&n, &g, &m, &r);

        let init_input = PaillierInputs {
            enc_bits: ENC_BIT_LEN,
            limb_bits: LIMB_BIT_LEN,
            n: n.clone(),
            g: g.clone(),
            m: m.clone(),
            r: r.clone(),
            res: expected_c.clone(),
        };

        let stats = base_test()
            .k(14)
            .lookup_bits(13)
            .expect_satisfied(true)
            .bench_builder(
                init_input.clone(),
                init_input.clone(),
                |pool, range, init_input: PaillierInputs| {
                    let _ = paillier_enc_test(pool, range, init_input).unwrap();
                },
            );

        println!("config params = {:?}", stats.config_params);
        println!("vk time = {:?}", stats.vk_time.time.elapsed());
        println!("pk time = {:?}", stats.pk_time.time.elapsed());
        println!("proof time = {:?}", stats.proof_time.time.elapsed());
        println!("proof size = {:?}", stats.proof_size);
        println!("verify time = {:?}", stats.verify_time.time.elapsed());
    }

    // #[test]
    // fn bench_paillier_enc_add() {
    //     const ENC_BIT_LEN: usize = 128;
    //     const LIMB_BIT_LEN: usize = 64;

    //     let mut rng = thread_rng();

    //     let n = rng.gen_biguint(ENC_BIT_LEN as u64);
    //     let g = rng.gen_biguint(ENC_BIT_LEN as u64);
    //     let m1 = rng.gen_biguint(ENC_BIT_LEN as u64);
    //     let r1 = rng.gen_biguint(ENC_BIT_LEN as u64);
    //     let m2 = rng.gen_biguint(ENC_BIT_LEN as u64);
    //     let r2 = rng.gen_biguint(ENC_BIT_LEN as u64);

    //     let expected_c1 = paillier_enc(&n, &g, &m1, &r1);
    //             let expected_c2 = paillier_enc(&n, &g, &m2, &r2);
    //     let res= paillier_add(&n, &expected_c1, &expected_c2);

    //     let init_input = PaillierInputsAdd {
    //         limb_bits: LIMB_BIT_LEN,
    //         enc_bits: ENC_BIT_LEN,
    //         n: n.clone(),
    //         g: g.clone(),
    //         m1:m1.clone(),
    //         r1:r1.clone(),
    //         m2:m2.clone(),
    //         r2:r2.clone(),
    //         c1: expected_c1.clone(),
    //         c2: expected_c2.clone(),
    //         res,
    //     };

    //     let stats = base_test()
    //         .k(14)
    //         .lookup_bits(13)
    //         .expect_satisfied(true)
    //         .bench_builder(
    //             init_input.clone(),
    //             init_input.clone(),
    //             |pool, range, init_input: PaillierInputsAdd| {
    //                 paillier_enc_add_test(pool, range, init_input);
    //             },
    //         );

    //     println!("config params2 = {:?}", stats.config_params);
    //     println!("vk time2 = {:?}", stats.vk_time.time.elapsed());
    //     println!("pk time 2= {:?}", stats.pk_time.time.elapsed());
    //     println!("proof time2 = {:?}", stats.proof_time.time.elapsed());
    //     println!("proof size2 = {:?}", stats.proof_size);
    //     println!("verify time 2= {:?}", stats.verify_time.time.elapsed());
    // }
}

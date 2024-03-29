use biguint_halo2::big_uint::chip::BigUintChip;
use halo2_base::{
    gates::{ flex_gate::threads::SinglePhaseCoreManager, RangeChip },
    halo2_proofs::circuit::Value,
    utils::BigPrimeField,
};
use num_bigint::BigUint;

use crate::paillier::{ EncryptionPublicKeyAssigned, PaillierChip };

#[derive(Debug, Clone)]
pub struct PaillierEncryptionInput {
    pub enc_bits: usize,
    pub limb_bits: usize,
    pub n: BigUint,
    pub g: BigUint,
    pub m: BigUint,
    pub r: BigUint,
    pub res: BigUint,
}

#[derive(Debug, Clone)]
pub struct PaillierAddCipherInput {
    pub limb_bits: usize,
    pub enc_bits: usize,
    pub n: BigUint,
    pub g: BigUint,
    pub c1: BigUint,
    pub c2: BigUint,
    pub res: BigUint,
}

pub fn paillier_enc_test<F: BigPrimeField>(
    pool: &mut SinglePhaseCoreManager<F>,
    range: &RangeChip<F>,
    input: PaillierEncryptionInput
) {
    let ctx = pool.main();

    let biguint_chip = BigUintChip::construct(range, input.limb_bits);

    let paillier_chip = PaillierChip::construct(&biguint_chip, input.enc_bits);

    let n_assigned = biguint_chip
        .assign_integer(ctx, Value::known(input.n.clone()), input.enc_bits)
        .unwrap();
    let g_assigned = biguint_chip
        .assign_integer(ctx, Value::known(input.g.clone()), input.enc_bits)
        .unwrap();
    let pk_enc = EncryptionPublicKeyAssigned {
        n: n_assigned,
        g: g_assigned,
    };

    let m_assigned = biguint_chip
        .assign_integer(ctx, Value::known(input.m.clone()), input.enc_bits)
        .unwrap();
    let r_assigned = biguint_chip
        .assign_integer(ctx, Value::known(input.r.clone()), input.enc_bits)
        .unwrap();

    let c_assigned = paillier_chip.encrypt(ctx, &pk_enc, &m_assigned, &r_assigned).unwrap();

    let res_assigned = biguint_chip
        .assign_integer(ctx, Value::known(input.res), input.enc_bits * 2)
        .unwrap();

    c_assigned
        .value()
        .zip(res_assigned.value())
        .map(|(a, b)| {
            assert_eq!(a, b);
        });
    biguint_chip.assert_equal_fresh(ctx, &c_assigned, &res_assigned).unwrap();
}

pub fn paillier_enc_add_test<F: BigPrimeField>(
    pool: &mut SinglePhaseCoreManager<F>,
    range: &RangeChip<F>,
    input: PaillierAddCipherInput
) {
    let biguint_chip = BigUintChip::construct(range, input.limb_bits);
    let ctx = pool.main();

    let paillier_chip = PaillierChip::construct(&biguint_chip, input.enc_bits);

    let n_assigned = biguint_chip
        .assign_integer(ctx, Value::known(input.n.clone()), input.enc_bits)
        .unwrap();
    let g_assigned = biguint_chip
        .assign_integer(ctx, Value::known(input.g.clone()), input.enc_bits)
        .unwrap();
    let pk_enc = EncryptionPublicKeyAssigned {
        n: n_assigned,
        g: g_assigned,
    };

    let c1_assigned = biguint_chip
        .assign_integer(ctx, Value::known(input.c1.clone()), input.enc_bits)
        .unwrap();
    let c2_assigned = biguint_chip
        .assign_integer(ctx, Value::known(input.c2.clone()), input.enc_bits)
        .unwrap();

    let _res = paillier_chip.add(ctx, &pk_enc, &c1_assigned, &c2_assigned).unwrap();

    let res_assigned = biguint_chip
        .assign_integer(ctx, Value::known(input.res.clone()), input.enc_bits * 2)
        .unwrap();

    _res.value()
        .zip(res_assigned.value())
        .map(|(a, b)| {
            assert_eq!(a, b);
        });
    biguint_chip.assert_equal_fresh(ctx, &_res, &res_assigned).unwrap();
}

#[cfg(test)]
mod test {
    use halo2_base::utils::testing::base_test;

    use num_bigint::RandBigInt;

    use rand::thread_rng;

    use crate::{
        bench::{
            paillier_enc_add_test,
            paillier_enc_test,
            PaillierAddCipherInput,
            PaillierEncryptionInput,
        },
        paillier::{ paillier_add_native, paillier_enc_native },
    };

    #[test]
    fn bench_paillier_enc() {
        const ENC_BIT_LEN: usize = 128;
        const LIMB_BIT_LEN: usize = 64;

        let mut rng = thread_rng();

        let n = rng.gen_biguint(ENC_BIT_LEN as u64);
        let g = rng.gen_biguint(ENC_BIT_LEN as u64);
        let m = rng.gen_biguint(ENC_BIT_LEN as u64);
        let r = rng.gen_biguint(ENC_BIT_LEN as u64);

        let expected_c = paillier_enc_native(&n, &g, &m, &r);

        let init_input = PaillierEncryptionInput {
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
                |pool, range, init_input: PaillierEncryptionInput| {
                    paillier_enc_test(pool, range, init_input)
                }
            );

        println!("config params = {:?}", stats.config_params);
        println!("vk time = {:?}", stats.vk_time.time.elapsed());
        println!("pk time = {:?}", stats.pk_time.time.elapsed());
        println!("proof time = {:?}", stats.proof_time.time.elapsed());
        println!("proof size = {:?}", stats.proof_size);
        println!("verify time = {:?}", stats.verify_time.time.elapsed());
    }

    #[test]
    fn bench_paillier_enc_add() {
        const ENC_BIT_LEN: usize = 128;
        const LIMB_BIT_LEN: usize = 64;

        let mut rng = thread_rng();

        let n = rng.gen_biguint(ENC_BIT_LEN as u64);
        let g = rng.gen_biguint(ENC_BIT_LEN as u64);
        let c1 = rng.gen_biguint(ENC_BIT_LEN as u64);
        let c2 = rng.gen_biguint(ENC_BIT_LEN as u64);
        let res = paillier_add_native(&n, &c1, &c2);

        let init_input = PaillierAddCipherInput {
            limb_bits: LIMB_BIT_LEN,
            enc_bits: ENC_BIT_LEN,
            n: n.clone(),
            g: g.clone(),
            c1: c1.clone(),
            c2: c2.clone(),
            res,
        };

        let stats = base_test()
            .k(14)
            .lookup_bits(13)
            .expect_satisfied(true)
            .bench_builder(
                init_input.clone(),
                init_input.clone(),
                |pool, range, init_input: PaillierAddCipherInput| {
                    paillier_enc_add_test(pool, range, init_input);
                }
            );

        println!("config params2 = {:?}", stats.config_params);
        println!("vk time2 = {:?}", stats.vk_time.time.elapsed());
        println!("pk time 2= {:?}", stats.pk_time.time.elapsed());
        println!("proof time2 = {:?}", stats.proof_time.time.elapsed());
        println!("proof size2 = {:?}", stats.proof_size);
        println!("verify time 2= {:?}", stats.verify_time.time.elapsed());
    }
}

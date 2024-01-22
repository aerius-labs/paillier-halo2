use halo2_base::{
    gates::{flex_gate::threads::SinglePhaseCoreManager, RangeChip},
    halo2_proofs::circuit::Value,
    utils::BigPrimeField,
};
use num_bigint::BigUint;

use crate::{big_uint::chip::BigUintChip, paillier::PaillierChip};

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

pub fn paillier_enc_test<F: BigPrimeField>(
    pool: &mut SinglePhaseCoreManager<F>,
    range: &RangeChip<F>,
    inputs: PaillierInputs,
) {
    let ctx = pool.main();
    let biguint_chip = BigUintChip::construct(range, inputs.limb_bits);
    let paillier_chip =
        PaillierChip::construct(&biguint_chip, inputs.enc_bits, &inputs.n, &inputs.g);

    let c_assigned = paillier_chip.encrypt(ctx, &inputs.m, &inputs.r).unwrap();

    let res_assigned = biguint_chip
        .assign_integer(ctx, Value::known(inputs.res.clone()), inputs.enc_bits * 2)
        .unwrap();

    c_assigned.value().zip(res_assigned.value()).map(|(a, b)| {
        assert_eq!(a, b);
    });
    biguint_chip
        .assert_equal_fresh(ctx, &c_assigned, &res_assigned)
        .unwrap();
}

#[cfg(test)]
mod test {
    use halo2_base::utils::testing::base_test;
    use num_bigint::RandBigInt;
    use rand::thread_rng;

    use crate::{
        bench::{paillier_enc_test, PaillierInputs},
        paillier::paillier_enc,
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
                    paillier_enc_test(pool, range, init_input);
                },
            );

        println!("config params = {:?}", stats.config_params);
        println!("vk time = {:?}", stats.vk_time.time.elapsed());
        println!("pk time = {:?}", stats.pk_time.time.elapsed());
        println!("proof time = {:?}", stats.proof_time.time.elapsed());
        println!("proof size = {:?}", stats.proof_size);
        println!("verify time = {:?}", stats.verify_time.time.elapsed());
    }
}

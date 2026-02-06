use crate::qs::constants::{MULT_LIST, NUM_TEST_PRIMES};
use crate::qs::state::{FBPrime, QsState};
use crate::qs::util::prime_sieve;

use rug::{Complete, Integer};
use std::cmp;

pub(crate) fn legendre(n: Integer, p: u32) -> i32 {
    let power = match n.pow_mod(&Integer::from((p - 1) / 2), &Integer::from(p)) {
        Ok(power) => power,
        Err(_) => unreachable!(),
    };
    if power > 1 {
        return (power - p).to_i32().unwrap();
    }
    power.to_i32().unwrap()
}

pub(crate) fn choose_multiplier(n: &Integer, b: u32, multiplier: &mut u32) -> Vec<u32> {
    let prime_list = prime_sieve(b);
    if *multiplier != 0 {
        println!("Using multiplier k = {multiplier}");
        return prime_list;
    }

    let ln2 = 2f64.ln();
    let num_primes = cmp::min(prime_list.len(), NUM_TEST_PRIMES as usize);

    let eight = Integer::from(8);
    let nmod8 = Integer::from(n % &eight).to_u32().unwrap();

    let mut scores: [f64; MULT_LIST.len()] = [0.0; MULT_LIST.len()];

    for (i, &m) in MULT_LIST.iter().enumerate() {
        let knmod8 = (nmod8 * m) % 8u32;

        let logmult = (m as f64).ln();
        scores[i] = 0.5 * logmult;

        // Adjust score based on knmod8
        match knmod8 {
            1 => scores[i] -= 2.0 * ln2,
            3 => scores[i] -= 0.5 * ln2,
            5 => scores[i] -= ln2,
            7 => scores[i] -= 0.5 * ln2,
            _ => {}
        };
    }

    for &prime in prime_list.iter().take(num_primes).skip(1) {
        let contrib = (prime as f64).ln() / ((prime as f64) - 1.0);

        let modp = n.mod_u(prime);

        for j in 0..MULT_LIST.len() {
            let knmodp = (modp * MULT_LIST[j]) % prime;

            if knmodp == 0 || legendre(Integer::from(knmodp), prime) == 1 {
                scores[j] -= if knmodp == 0 { contrib } else { 2.0 * contrib };
            }
        }
    }

    let mut mmap: Vec<(f64, u32)> = scores
        .iter()
        .copied()
        .zip(MULT_LIST.iter().copied())
        .collect();

    mmap.sort_by(|a, b| a.0.partial_cmp(&b.0).unwrap());

    for (score, multiplier) in mmap.iter().take(5) {
        println!("Score: {}, Multiplier: {}", score, multiplier);
    }

    *multiplier = mmap[0].1;
    println!("Using multiplier k = {multiplier}");

    prime_list
}

pub(crate) fn tonelli_shanks(a: &Integer, prime: &u32) -> (u32, u32) {
    let p_u32 = *prime;
    let p_big = Integer::from(p_u32);

    let mut a_mod = Integer::from(a);
    a_mod %= &p_big;

    let pmod8 = p_u32 % 8;

    if pmod8 == 3 || pmod8 == 7 {
        let exponent = (p_u32 + 1) / 4;
        let exponent_big = Integer::from(exponent);

        let x = a_mod
            .clone()
            .pow_mod(&exponent_big, &p_big)
            .unwrap()
            .to_u32()
            .unwrap();
        return (x, p_u32 - x);
    }
    if pmod8 == 5 {
        let exponent = (p_u32 + 3) / 8;
        let exponent_big = Integer::from(exponent);

        let x = match a_mod.clone().pow_mod(&exponent_big, &p_big) {
            Ok(x) => x,
            Err(_) => unreachable!(),
        };
        let mut mult: Integer = Integer::from(1);
        if (&x * &x).complete().modulo(&p_big) != a_mod {
            let exponent = (p_u32 - 1) / 4;
            let exponent_big = Integer::from(exponent);
            mult = Integer::from(2).pow_mod(&exponent_big, &p_big).unwrap()
        }
        let x = (&x * &mult).complete().modulo(&p_big).to_u32().unwrap();
        return (x, p_u32 - x);
    }

    let mut d = Integer::from(2);
    let mut symb = 0;
    while symb != -1 {
        symb = legendre(d.clone(), p_u32);
        d += 1;
    }
    d -= 1;
    let mut n = p_u32 - 1;
    let mut s = 0;
    while n % 2 == 0 {
        n >>= 1;
        s += 1;
    }

    let t = n;

    let a_b = a_mod.clone().pow_mod(&Integer::from(t), &p_big).unwrap();
    let d_b = d.pow_mod(&Integer::from(t), &p_big).unwrap();

    let mut m = Integer::from(0);

    for i in 0..s {
        let i1 = 2u32.pow(s - 1 - i);
        let mut i2 = d_b.clone().pow_mod(&m, &p_big).unwrap();
        i2 *= &a_b;
        i2 %= &p_big;
        let i3 = i2.pow_mod(&Integer::from(i1), &p_big).unwrap();
        if i3 == p_u32 - 1 {
            m += 2u32.pow(i);
        }
    }
    let x_1 = a_mod.pow_mod(&Integer::from((t + 1) / 2), &p_big).unwrap();
    let x_2 = d_b.pow_mod(&(m / 2), &p_big).unwrap();
    let mut x = x_1;
    x *= x_2;
    x %= p_big;
    let x = x.to_u32().unwrap();
    (x, p_u32 - x)
}

pub(crate) fn build_factor_base(
    qs_state: &mut QsState,
    prime_list: Vec<u32>,
) -> (Vec<i32>, Vec<u32>, Vec<u64>, Vec<u128>) {
    let mut factor_base: Vec<i32> = vec![-1, 2];

    for prime in &prime_list[1..] {
        if legendre(qs_state.n.clone(), *prime) == 1 {
            factor_base.push(*prime as i32);
            qs_state.root_map[*prime as usize] = tonelli_shanks(&qs_state.n, prime);
            if *prime >= qs_state.prime_limit as u32 {
                let fbp = FBPrime {
                    prime: *prime,
                    root1: 0,
                    root2: 0,
                    logprime: prime.ilog2() as u8,
                };
                qs_state.fb_primes.push(fbp);
            }
        }
    }
    let factor_base_u128: Vec<u128> = factor_base.iter().skip(1).map(|&e| e as u128).collect();
    let factor_base_u64: Vec<u64> = factor_base.iter().skip(1).map(|&e| e as u64).collect();
    let factor_base_u32: Vec<u32> = factor_base.iter().skip(1).map(|&e| e as u32).collect();

    println!("Factor base size: {}", factor_base.len());
    (
        factor_base,
        factor_base_u32,
        factor_base_u64,
        factor_base_u128,
    )
}

#[inline(never)]
pub(crate) fn modinv(n: &Integer, mut p: i32) -> i32 {
    let mut n = n.mod_u(p as u32) as i32;
    let mut x = 0;
    let mut u = 1;
    while n != 0 {
        let q = p / n;
        let r = p % n;
        let temp = x;
        x = u;
        u = temp - q * u;
        p = n;
        n = r;
    }
    x
}

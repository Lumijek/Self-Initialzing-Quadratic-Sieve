use crate::qs::constants::{ERROR_MUL, LOWER_BOUND_SIQS, SMALL_B, UPPER_BOUND_SIQS};
use crate::qs::factor_base::modinv;
use crate::qs::state::{PolyState, Polynomial, QsState};

use rand::{self, Rng};
use rug::{Assign, Complete, Float, Integer};
use rustc_hash::FxHashSet;
use std::process;

#[inline(never)]
pub(crate) fn generate_a(
    qs_state: &mut QsState,
    factor_base: &[i32],
) -> (Integer, Vec<usize>, FxHashSet<i32>) {
    let poly_a_list = &mut qs_state.poly_a_list;
    let mut rng = rand::rng();
    let mut lower_polypool_index: usize = 2;
    let mut upper_polypool_index: usize = (SMALL_B as usize) - 1;
    let mut poly_low_found = false;
    for (i, fb_prime) in factor_base.iter().enumerate().take(SMALL_B as usize) {
        if *fb_prime > LOWER_BOUND_SIQS && !poly_low_found {
            lower_polypool_index = i as usize;
            poly_low_found = true;
        }
        if *fb_prime > UPPER_BOUND_SIQS {
            upper_polypool_index = i as usize;
            break;
        }
    }

    let target_a: Integer = (Float::with_val(53, 2 * qs_state.n.clone()).sqrt() / qs_state.m)
        .to_integer()
        .unwrap();
    let mut target_bits: u32 = ((target_a.significant_bits() as f64) * ERROR_MUL).round() as u32;
    let too_close = 10;
    let close_range = 5;
    let min_ratio = LOWER_BOUND_SIQS;

    let mut poly_a;
    let mut afact: FxHashSet<i32> = FxHashSet::default();
    let mut qli: Vec<usize> = Vec::new();

    let mut a1 = Integer::new();
    loop {
        poly_a = Integer::from(1);
        afact.clear();
        qli.clear();
        loop {
            let mut found_a_factor = false;
            let mut potential_a_factor: i32 = 1;
            let mut randindex: usize = 1;
            while !found_a_factor {
                randindex = rng.random_range(lower_polypool_index..upper_polypool_index) as usize;
                potential_a_factor = factor_base[randindex];
                found_a_factor = true;
                if afact.contains(&potential_a_factor) {
                    found_a_factor = false;
                }
            }
            poly_a *= potential_a_factor;
            afact.insert(potential_a_factor);
            qli.push(randindex);

            let j = target_a.significant_bits() - poly_a.significant_bits();
            if j < too_close {
                poly_a = Integer::from(1);
                afact.clear();
                qli.clear();
                continue;
            } else if j < (too_close + close_range) {
                break;
            }
        }

        a1.assign(&target_a / &poly_a);
        if a1 < min_ratio {
            continue;
        }

        let mut mindiff = Integer::from(u64::MAX);
        let mut randindex = 0;
        let mut a1_min_fb_prime = Integer::new();

        for (i, fb_prime) in factor_base.iter().enumerate().take(SMALL_B as usize) {
            a1_min_fb_prime.assign(&a1 - fb_prime);
            a1_min_fb_prime.abs_mut();
            if a1_min_fb_prime < mindiff {
                mindiff.assign(&a1_min_fb_prime);
                randindex = i;
            }
        }

        let mut found_a_factor = false;
        let mut potential_a_factor: i32 = 1;
        while !found_a_factor {
            potential_a_factor = factor_base[randindex];
            found_a_factor = true;
            if afact.contains(&potential_a_factor) {
                found_a_factor = false;
            }
            if !found_a_factor {
                randindex += 1;
            }
        }

        if randindex > (SMALL_B as usize) {
            continue;
        }

        poly_a *= potential_a_factor;
        afact.insert(potential_a_factor);
        qli.push(randindex);

        let diff_bits = (&target_a - &poly_a).complete().significant_bits();
        if diff_bits < target_bits {
            if poly_a_list.contains(&poly_a) {
                if target_bits > 1000 {
                    println!("SOMETHING WENT WRONG");
                    process::exit(1);
                }
                target_bits += 1;
                continue;
            } else {
                break;
            }
        }
    }
    poly_a_list.insert(poly_a.clone());
    qli.sort();
    (poly_a, qli, afact)
}

#[inline(never)]
pub(crate) fn generate_first_polynomial(qs_state: &mut QsState, factor_base: &[i32]) -> PolyState {
    let (a, qli, afact) = generate_a(qs_state, factor_base);
    let bainv = &mut qs_state.bainv;
    let s = qli.len();
    let mut b_list: Vec<Integer> = vec![Integer::new(); s];
    for i in 0..s {
        let p = factor_base[qli[i]] as u32;
        let r1 = qs_state.root_map[p as usize].0 as i32;
        let aq = (&a / p).complete();
        let invaq = modinv(&aq, p as i32);
        let mut gamma = (r1 * invaq).rem_euclid(p as i32) as u32;
        if gamma > p / 2 {
            gamma = p - gamma;
        }
        b_list[i] = aq * gamma;
    }

    let b: Integer = b_list.iter().sum::<Integer>().modulo(&a);
    let c = (&b * &b - &qs_state.n).complete() / &a;

    let mut res = Integer::new();
    for fbp in &mut qs_state.fb_primes {
        let p = fbp.prime as i32;
        res.assign(&a % p);
        if res.is_zero() {
            continue;
        }
        let p_u32 = p as u32;
        let ainv = modinv(&a, p);
        let ainv2 = ((2 * ainv).rem_euclid(p)) as u64;

        for (j, b_val) in b_list.iter().enumerate().take(s) {
            let mut value = b_val.mod_u(p_u32) as u64;
            value = (value * ainv2) % (p as u64);
            bainv[p as usize][j] = value as i32;
        }

        let (r1_val, r2_val) = qs_state.root_map[p_u32 as usize];
        let b_modp = b.mod_u(p_u32);
        let ainv_modp = (ainv.rem_euclid(p)) as u64;

        let r1_modp = r1_val % (p_u32);
        let diff_u64 = if r1_modp >= b_modp {
            r1_modp - b_modp
        } else {
            (p_u32) - (b_modp - r1_modp)
        } as u64;
        let mut r1 = ((diff_u64 * ainv_modp) % (p as u64)) as u32;
        r1 = (r1 + qs_state.m) % (p as u32);

        let r2_modp = r2_val % (p_u32);
        let diff_u64 = if r2_modp >= b_modp {
            r2_modp - b_modp
        } else {
            (p_u32) - (b_modp - r2_modp)
        } as u64;
        let mut r2 = ((diff_u64 * ainv_modp) % (p as u64)) as u32;
        r2 = (r2 + qs_state.m) % (p as u32);

        if r1 > r2 {
            std::mem::swap(&mut r1, &mut r2);
        }
        fbp.root1 = r1 as i32;
        fbp.root2 = r2 as i32;
    }

    PolyState {
        a,
        b,
        c,
        b_list,
        s: s as u32,
        afact,
    }
}

#[inline(never)]
pub(crate) fn generate_polynomials(
    qs_state: &mut QsState,
    polynomials: &mut Vec<Polynomial>,
    factor_base: &[i32],
    grays: &[(usize, i32)],
) -> PolyState {
    qs_state.current_fb_primes.clear();
    polynomials.clear();
    let poly_state = generate_first_polynomial(qs_state, factor_base);
    let end = 1 << (poly_state.s - 1);

    let mut found = false;
    for fbp in &qs_state.fb_primes {
        if poly_state.a.mod_u(fbp.prime) != 0 {
            qs_state.current_fb_primes.push(fbp.clone());
        }
        if !found && fbp.prime > (qs_state.m * 2 + 1) {
            found = true;
            qs_state.b1 = qs_state.current_fb_primes.len() - 1;
        }
    }

    if !found {
        qs_state.b1 = qs_state.current_fb_primes.len();
    }

    let (v, e) = grays[1];
    let base_poly = Polynomial {
        a: poly_state.a.clone(),
        b: poly_state.b.clone(),
        c: poly_state.c.clone(),
        v,
        e,
    };

    polynomials.push(base_poly);
    for i in 1..end {
        let (v, e) = grays[i + 1];
        let mut poly_curr = Polynomial {
            a: poly_state.a.clone(),
            b: polynomials[i - 1].b.clone(),
            c: Integer::new(),
            v,
            e,
        };
        let (v, e) = grays[i];
        poly_curr.b += 2 * e * &poly_state.b_list[v];
        poly_curr.c = (&poly_curr.b * &poly_curr.b - &qs_state.n).complete() / &poly_curr.a;
        polynomials.push(poly_curr);
    }
    poly_state
}

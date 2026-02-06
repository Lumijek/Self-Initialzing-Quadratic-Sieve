use crate::qs::poly::generate_polynomials;
use crate::qs::state::{PolyState, Polynomial, QsState};
use crate::qs::util::{get_gray_code, print_stats};

use rug::{Assign, Float, Integer};
use rustc_hash::{FxHashMap, FxHashSet};
use std::mem;
use std::time::Instant;

#[inline(never)]
pub(crate) fn factorise_fast(
    mut value: Integer,
    factor_base_u32: &[u32],
    factor_base_u64: &[u64],
    factor_base_u128: &[u128],
) -> (FxHashSet<i32>, Integer) {
    let mut factors: FxHashSet<i32> = FxHashSet::default();

    if value < 0 {
        factors.insert(-1);
        value = -value;
    }

    let mut i = 0;
    let comp = Integer::from(u128::MAX);

    while i < factor_base_u32.len() {
        let factor = factor_base_u32[i];

        while value.is_divisible_u(factor) {
            if !factors.contains(&(factor as i32)) {
                factors.insert(factor as i32);
            } else {
                factors.remove(&(factor as i32));
            }
            value /= factor;
        }

        i += 1;
        if value < comp {
            break;
        }
    }

    if i == factor_base_u128.len() {
        return (factors, value);
    }

    let mut val_u128 = value.to_u128().unwrap();

    while i < factor_base_u128.len() {
        let factor = factor_base_u128[i];

        while val_u128 % (factor) == 0 {
            if !factors.contains(&(factor as i32)) {
                factors.insert(factor as i32);
            } else {
                factors.remove(&(factor as i32));
            }
            val_u128 /= factor;
        }

        i += 1;
        if val_u128 < u64::MAX as u128 {
            break;
        }
    }

    if i == factor_base_u128.len() {
        return (factors, Integer::from(val_u128));
    }

    let mut val_u64 = val_u128 as u64;

    while i < factor_base_u64.len() {
        let factor = factor_base_u64[i];

        while val_u64 % (factor) == 0 {
            if !factors.contains(&(factor as i32)) {
                factors.insert(factor as i32);
            } else {
                factors.remove(&(factor as i32));
            }
            val_u64 /= factor;
        }

        i += 1;
    }

    (factors, Integer::from(val_u64))
}

#[inline(never)]
pub(crate) fn find_relations(
    qs_state: &mut QsState,
    fb_map: &FxHashMap<i32, usize>,
    interval_size: usize,
    poly_state: &PolyState,
    ppoly: &Polynomial,
    factor_base_u32: &[u32],
    factor_base_u64: &[u64],
    factor_base_u128: &[u128],
) {
    let sieve_values = &qs_state.sieve_values;
    let mut axval = Integer::new();
    let mut relation = Integer::new();
    let mut poly_val = Integer::new();
    let mut pva = Integer::new();
    let mut x: usize = 0;
    let mut i = 0;
    let slice: &[u64] = unsafe {
        assert!(
            (sieve_values.as_ptr() as usize) % mem::align_of::<u64>() == 0,
            "sieve_values is not properly aligned for u64"
        );

        std::slice::from_raw_parts(
            sieve_values.as_ptr() as *const u64,
            sieve_values.len() / mem::size_of::<u64>(),
        )
    };

    let sieve_mask: u64 = 0x8080808080808080;

    while x < interval_size {
        if i + 7 >= slice.len() {
            break;
        }

        let to_mask = slice[i]
            | slice[i + 1]
            | slice[i + 2]
            | slice[i + 3]
            | slice[i + 4]
            | slice[i + 5]
            | slice[i + 6]
            | slice[i + 7];
        if to_mask & sieve_mask == 0 {
            x += 64;
            i += 8;
            continue;
        }
        i += 8;
        for xv in x..(x + 64) {
            if xv >= sieve_values.len() {
                break;
            }
            if sieve_values[xv] < 0x80 {
                continue;
            }

            let xval = (xv as i32) - (qs_state.m as i32);

            axval.assign(&ppoly.a * xval);
            relation.assign(&axval + &ppoly.b);

            poly_val.assign(2 * &ppoly.b);
            poly_val += &axval;
            poly_val *= xval;
            poly_val += &ppoly.c;

            pva.assign(&poly_val);
            pva *= &ppoly.a;

            let (mut local_factors, finval) = factorise_fast(
                poly_val.clone(),
                factor_base_u32,
                factor_base_u64,
                factor_base_u128,
            );
            local_factors = &local_factors ^ &poly_state.afact;

            if finval != 1 {
                if finval < qs_state.large_prime_bound {
                    let value = finval.to_u64().unwrap();
                    if qs_state.partials.contains_key(&value) {
                        let (rel, lf, pv) = &qs_state.partials[&value];
                        relation *= rel;
                        local_factors = &local_factors ^ lf;
                        pva *= pv;
                        qs_state.lp_found += 1;
                    } else {
                        qs_state.partials.insert(
                            value,
                            (relation.clone(), local_factors.clone(), pva.clone()),
                        );
                        continue;
                    }
                } else {
                    continue;
                }
            }

            for fac in local_factors {
                let idx = fb_map[&fac];
                qs_state.matrix[idx] |= &qs_state.ind;
            }

            qs_state.ind <<= 1;
            qs_state.relations.push(relation.clone());
            qs_state.roots.push(pva.clone());

            if qs_state.relations.len() >= qs_state.b as usize + qs_state.t as usize {
                break;
            }
        }
        x += 64;
    }
}

#[inline(never)]
pub(crate) fn interval_sieve(qs_state: &mut QsState, v: usize, e: i32, interval_size: usize) {
    let sieve_values = &mut qs_state.sieve_values;
    let bainv = &qs_state.bainv;

    let (cur_fb1, cur_fb2) = qs_state.current_fb_primes.split_at_mut(qs_state.b1);

    unsafe {
        for fbp in cur_fb1 {
            let p = fbp.prime;
            let p_ind = p as usize;
            let p_i32 = p as i32;

            let r1 = fbp.root1;
            let r2 = fbp.root2;
            let log_p = fbp.logprime;
            let bainv_ptr = bainv.get_unchecked(p_ind).as_ptr();
            let ebainv = *bainv_ptr.add(v) * e;
            fbp.root1 = (r1 - ebainv).rem_euclid(p_i32);
            fbp.root2 = (r2 - ebainv).rem_euclid(p_i32);
            let mut r1 = r1 as usize;
            let mut r2 = r2 as usize;

            if r1 > r2 {
                std::mem::swap(&mut r1, &mut r2);
            }
            while r2 < interval_size {
                *sieve_values.get_unchecked_mut(r1) += log_p;
                *sieve_values.get_unchecked_mut(r2) += log_p;
                r1 += p_ind;
                r2 += p_ind;
            }
            if r1 < interval_size {
                *sieve_values.get_unchecked_mut(r1) += log_p;
            }
        }

        for fbp in cur_fb2 {
            let p = fbp.prime;
            let p_ind = p as usize;
            let p_i32 = p as i32;

            let r1 = fbp.root1;
            let r2 = fbp.root2;
            let log_p = fbp.logprime;
            let bainv_ptr = bainv.get_unchecked(p_ind).as_ptr();
            let ebainv = *bainv_ptr.add(v) * e;
            fbp.root1 = (r1 - ebainv).rem_euclid(p_i32);
            fbp.root2 = (r2 - ebainv).rem_euclid(p_i32);
            let mut r1 = r1 as usize;
            let mut r2 = r2 as usize;

            if r1 > r2 {
                std::mem::swap(&mut r1, &mut r2);
            }
            if r1 < interval_size {
                *sieve_values.get_unchecked_mut(r1) += log_p;
                if r2 < interval_size {
                    *sieve_values.get_unchecked_mut(r2) += log_p;
                }
            }
        }
    }
}

#[inline(never)]
pub(crate) fn sieve(
    qs_state: &mut QsState,
    factor_base: Vec<i32>,
    factor_base_u32: Vec<u32>,
    factor_base_u64: Vec<u64>,
    factor_base_u128: Vec<u128>,
) {
    let start = Instant::now();

    let fb_len = factor_base.len() as u32;
    let fb_map: FxHashMap<_, _> = factor_base
        .iter()
        .enumerate()
        .map(|(i, val)| (*val, i))
        .collect();
    let target_relations = (fb_len + qs_state.t) as usize;
    qs_state.large_prime_bound = qs_state.b * qs_state.lp_multiplier;

    let threshold = ((Float::with_val(53, &qs_state.n).sqrt() * qs_state.m).log2() - qs_state.eps)
        .to_f64()
        .floor() as u8;
    let bound = 0x80 - threshold;

    qs_state.matrix = vec![Integer::new(); fb_len as usize];

    let mut num_poly = 0;
    let interval_size: usize = (2 * qs_state.m + 1) as usize;
    let grays = get_gray_code(20);

    qs_state.sieve_values = vec![0x80 - threshold; interval_size];

    let mut ft = true;

    let mut polynomials: Vec<Polynomial> = Vec::new();

    while qs_state.relations.len() < target_relations {
        if num_poly % 10 == 0 {
            print_stats(
                &qs_state.relations,
                target_relations,
                num_poly,
                start,
                ft,
                qs_state.lp_found,
            );
        }
        ft = false;

        let poly_state = generate_polynomials(qs_state, &mut polynomials, &factor_base, &grays);

        for ppoly in &polynomials {
            interval_sieve(qs_state, ppoly.v, ppoly.e, interval_size);

            find_relations(
                qs_state,
                &fb_map,
                interval_size,
                &poly_state,
                ppoly,
                &factor_base_u32,
                &factor_base_u64,
                &factor_base_u128,
            );
            num_poly += 1;
            qs_state.sieve_values.fill(bound);
        }
    }
    println!("Large Primes Found: {}", qs_state.lp_found);
    println!(
        "Normal Relations Found: {}",
        qs_state.relations.len() - qs_state.lp_found
    )
}

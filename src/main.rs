#[global_allocator]
static GLOBAL: mimalloc::MiMalloc = mimalloc::MiMalloc;
use rand::{self, Rng};
use rug::{Assign, Complete, Float, Integer};
use rustc_hash::{FxHashMap, FxHashSet};
use std::cmp;
use std::io::{self, Write};
use std::mem;
use std::process;
use std::time::Instant;

static LOWER_BOUND_SIQS: i32 = 1000;
static UPPER_BOUND_SIQS: i32 = 4000;
static SMALL_B: i32 = 1024;
static ERROR_MUL: f64 = 0.9;
const NUM_TEST_PRIMES: i32 = 300;

struct QsState {
    n: Integer,
    b: u32,
    m: u32,
    t: u32,
    prime_limit: i32,
    eps: u32,
    lp_multiplier: u32,
    multiplier: u32,
    root_map: Vec<(u32, u32)>,
    lp_found: usize,
    large_prime_bound: u32,
    matrix: Vec<Integer>,
    relations: Vec<Integer>,
    roots: Vec<Integer>,
    partials: FxHashMap<u64, (Integer, FxHashSet<i32>, Integer)>,
    ind: Integer,
    sieve_values: Vec<u8>,
    bainv: Vec<Vec<i32>>,
    poly_a_list: FxHashSet<Integer>,
    fb_primes: Vec<FBPrime>,
    current_fb_primes: Vec<FBPrime>,

    b1: usize,
}

struct Polynomial {
    a: Integer,
    b: Integer,
    c: Integer,
    v: usize,
    e: i32,
}
struct PolyState {
    a: Integer,
    b: Integer,
    c: Integer,
    b_list: Vec<Integer>,
    s: u32,
    afact: FxHashSet<i32>,
}

#[derive(Clone)]
struct FBPrime {
    prime: u32,
    root1: i32,
    root2: i32,
    logprime: u8,
}
const MULT_LIST: [u32; 114] = [
    1, 2, 3, 5, 7, 9, 10, 11, 13, 14, 15, 17, 19, 21, 23, 25, 29, 31, 33, 35, 37, 39, 41, 43, 45,
    47, 49, 51, 53, 55, 57, 59, 61, 63, 65, 67, 69, 71, 73, 75, 77, 79, 83, 85, 87, 89, 91, 93, 95,
    97, 101, 103, 105, 107, 109, 111, 113, 115, 119, 121, 123, 127, 129, 131, 133, 137, 139, 141,
    143, 145, 147, 149, 151, 155, 157, 159, 161, 163, 165, 167, 173, 177, 179, 181, 183, 185, 187,
    191, 193, 195, 197, 199, 201, 203, 205, 209, 211, 213, 215, 217, 219, 223, 227, 229, 231, 233,
    235, 237, 239, 241, 249, 251, 253, 255,
];

fn get_gray_code(n: usize) -> Vec<(usize, i32)> {
    let size = 1 << (n - 1);
    let mut grays = vec![(0, 0); size];
    grays[0] = (0, 0);
    for (i, gray) in grays.iter_mut().enumerate().take(size).skip(1) {
        let mut v = 1;
        let mut j = i;
        while (j & 1) == 0 {
            v += 1;
            j >>= 1;
        }
        let mut tmp = i + ((1 << v) - 1);
        tmp >>= v;
        if (tmp & 1) == 1 {
            *gray = (v - 1, -1);
        } else {
            *gray = (v - 1, 1);
        }
    }
    grays
}

pub fn print_stats(
    relations: &[Integer],
    target_relations: usize,
    num_poly: u32,
    start_time: Instant,
    first_time: bool,
    lp_found: usize,
) {
    const LINES_TO_MOVE_UP: usize = 12;

    if !first_time {
        print!("\x1B[{}A\x1B[J", LINES_TO_MOVE_UP);
        io::stdout().flush().unwrap();
    }

    let rel_len = relations.len() as f64;
    let num_poly_f64 = num_poly as f64;
    let elapsed = start_time.elapsed().as_secs_f64();

    let relations_per_polynomial = rel_len / num_poly_f64;
    let relations_per_second = rel_len / elapsed;
    let poly_per_second = num_poly_f64 / elapsed;
    let percent = (rel_len / target_relations as f64) * 100.0;
    let percent_per_second = percent / elapsed;
    let total_remaining_secs = ((100.0 - percent) / percent_per_second) as u64;
    let hours = total_remaining_secs / 3600;
    let minutes = (total_remaining_secs % 3600) / 60;
    let seconds = total_remaining_secs % 60;
    println!(
        "\
Processing Status
----------------------------------------------
Total Relations          : {}    
Total Partial Relations  : {}    
Total Polynomials Used   : {}    
Relations per polynomial : {:.5} 
Relations per second     : {:.2} 
Poly per second          : {:.2} 
Percent                  : {:.5}%
Percent per second       : {:.5}%
Estimated Time           : {}:{:02}:{:02}
----------------------------------------------",
        relations.len(),
        lp_found,
        num_poly,
        relations_per_polynomial,
        relations_per_second,
        poly_per_second,
        percent,
        percent_per_second,
        hours,
        minutes,
        seconds
    );
    io::stdout().flush().unwrap();
}

fn prime_sieve(b: u32) -> Vec<u32> {
    let mut is_prime = vec![true; (b + 1) as usize];
    is_prime[0] = false;
    is_prime[1] = false;

    let sqrt_limit = (b as f64).sqrt() as usize;
    for i in 2..=sqrt_limit {
        if is_prime[i] {
            for multiple in (i * i..=b as usize).step_by(i) {
                is_prime[multiple] = false;
            }
        }
    }

    let mut prime_list: Vec<u32> = Vec::new();
    for (i, &ip) in is_prime.iter().enumerate() {
        if ip {
            prime_list.push(i as u32);
        }
    }
    prime_list
}

fn legendre(n: Integer, p: u32) -> i32 {
    let power = match n.pow_mod(&Integer::from((p - 1) / 2), &Integer::from(p)) {
        Ok(power) => power,
        Err(_) => unreachable!(),
    };
    if power > 1 {
        return (power - p).to_i32().unwrap();
    }
    power.to_i32().unwrap()
}

fn choose_multiplier(n: &Integer, b: u32, multiplier: &mut u32) -> Vec<u32> {
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

fn tonelli_shanks(a: &Integer, prime: &u32) -> (u32, u32) {
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

fn build_factor_base(qs_state: &mut QsState, prime_list: Vec<u32>) -> Vec<i32> {
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

    println!("Factor base size: {}", factor_base.len());
    factor_base
}

#[inline(never)]
fn modinv(n: &Integer, mut p: i32) -> i32 {
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

#[inline(never)]
fn generate_a(
    qs_state: &mut QsState,
    factor_base: &[i32],
) -> (Integer, Vec<usize>, FxHashSet<i32>) {
    let poly_a_list = &mut qs_state.poly_a_list;
    let mut rng = rand::thread_rng();
    let mut lower_polypool_index: isize = 2;
    let mut upper_polypool_index: isize = (SMALL_B as isize) - 1;
    let mut poly_low_found = false;
    for (i, fb_prime) in factor_base.iter().enumerate().take(SMALL_B as usize) {
        if *fb_prime > LOWER_BOUND_SIQS && !poly_low_found {
            lower_polypool_index = i as isize;
            poly_low_found = true;
        }
        if *fb_prime > UPPER_BOUND_SIQS {
            upper_polypool_index = i as isize;
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
                randindex = rng.gen_range(lower_polypool_index..upper_polypool_index) as usize;
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
fn generate_first_polynomial(qs_state: &mut QsState, factor_base: &[i32]) -> PolyState {
    let (a, qli, afact) = generate_a(qs_state, factor_base);
    let bainv = &mut qs_state.bainv;
    let s = qli.len();
    let mut b_list: Vec<Integer> = vec![Integer::new(); s];
    for i in 0..s {
        let p = factor_base[qli[i]] as u32;
        let r1 = qs_state.root_map[p as usize].0 as i32;
        let aq = (&a / p).complete();
        let invaq = modinv(&aq, p as i32);
        let mut gamma = (r1 * invaq).rem_euclid(p as i32) as u32; // if code doesn't work, ensure overflow isn't happening here
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

        // store bainv

        for (j, b_val) in b_list.iter().enumerate().take(s) {
            let mut value = b_val.mod_u(p_u32) as u64;
            value = (value * ainv2) % (p as u64);
            bainv[p as usize][j] = value as i32;
        }

        // store roots

        let (r1_val, r2_val) = qs_state.root_map[p_u32 as usize];
        let b_modp = b.mod_u(p_u32);
        let ainv_modp = (ainv.rem_euclid(p)) as u64;

        // r1

        let r1_modp = r1_val % (p_u32);
        let diff_u64 = if r1_modp >= b_modp {
            r1_modp - b_modp
        } else {
            (p_u32) - (b_modp - r1_modp)
        } as u64;
        let mut r1 = ((diff_u64 * ainv_modp) % (p as u64)) as u32;
        r1 = (r1 + qs_state.m) % (p as u32);

        // r2
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

    let pstate: PolyState = PolyState {
        a,
        b,
        c,
        b_list,
        s: s as u32,
        afact,
    };

    pstate
}

#[inline(never)]
fn factorise_fast(mut value: Integer, factor_base: &[i32]) -> (FxHashSet<i32>, Integer) {
    let mut factors: FxHashSet<i32> = FxHashSet::default();
    if value < 0 {
        factors.insert(-1);
        value = -value;
    }

    for factor in factor_base.iter().skip(1) {
        while value.is_divisible_u(*factor as u32) {
            if !factors.contains(factor) {
                factors.insert(*factor);
            } else {
                factors.remove(factor);
            }
            value /= factor;
        }
    }

    (factors, value)
}

#[inline(never)]
fn generate_polynomials(
    qs_state: &mut QsState,
    polynomials: &mut Vec<Polynomial>,
    factor_base: &[i32],
    grays: &[(usize, i32)],
) -> PolyState {
    let mut pa = Integer::new();
    qs_state.current_fb_primes.clear();
    polynomials.clear();
    let poly_state = generate_first_polynomial(qs_state, factor_base);
    let end = 1 << (poly_state.s - 1);

    let mut found = false;
    for fbp in &qs_state.fb_primes {
        pa.assign(&poly_state.a & fbp.prime);
        if !pa.is_zero() {
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

#[inline(never)]
fn find_relations(
    qs_state: &mut QsState,
    fb_map: &FxHashMap<i32, usize>,
    interval_size: usize,
    poly_state: &PolyState,
    ppoly: &Polynomial,
    factor_base_list: &[i32],
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

    let sieve_mask: u64 = 0x8080808080808080; // possibly change this to a u128. sometimes faster sometimes slower

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

            // Compute the polynomial value
            poly_val.assign(2 * &ppoly.b);
            poly_val += &axval;
            poly_val *= xval;
            poly_val += &ppoly.c;

            // Compute pva
            pva.assign(&poly_val);
            pva *= &ppoly.a;

            // Factorize the polynomial value
            let (mut local_factors, finval) = factorise_fast(poly_val.clone(), factor_base_list);
            local_factors = &local_factors ^ &poly_state.afact;

            // Handle large primes and partial relations

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
fn interval_sieve(qs_state: &mut QsState, v: usize, e: i32, interval_size: usize) {
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
            let ebainv = e * bainv[p_ind][v];
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
            let ebainv = e * bainv[p_ind][v];
            let log_p = fbp.logprime;
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
fn sieve(qs_state: &mut QsState, factor_base: Vec<i32>) {
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
                &factor_base,
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

#[inline(never)]
fn null_space_extraction(qs_state: &mut QsState) -> Vec<Integer> {
    let n = qs_state.relations.len();
    let m = qs_state.matrix.len();
    let t = qs_state.t as usize;

    let matrix = &mut qs_state.matrix;
    let mut marks = Vec::new();
    let mut mark_mask = Integer::from(0);
    let mut cur: isize = -1;

    for i in 0..m {
        if cur % 10 == 0 {
            print!("{cur}, {m}\r");
        }
        cur += 1;
        let lsb: isize = (matrix[i].clone() & -matrix[i].clone()).significant_bits() as isize - 1;
        if lsb == -1 {
            continue;
        }
        marks.push(n - lsb as usize - 1);
        mark_mask |= Integer::from(1) << lsb;

        let pivot_row = matrix[i].clone();
        for j in 0..m {
            if matrix[j].get_bit(lsb as u32) && j as isize != cur {
                matrix[j] ^= &pivot_row;
            }
        }
    }

    marks.sort();
    let mut nulls: Vec<Integer> = Vec::new();
    let mut free_cols = Vec::new();
    for val in 0..n {
        if !marks.contains(&val) {
            free_cols.push(val);
        }
    }
    let mut k = 0;
    for col in free_cols {
        let shift = n - col - 1;
        let val = Integer::from(1) << shift;
        let mut fin = val.clone();
        for i in 0..m {
            if matrix[i].get_bit(shift as u32) {
                fin |= (&matrix[i] & &mark_mask).complete();
            }
        }
        nulls.push(fin.clone());
        k += 1;
        if k == t {
            break;
        }
    }
    nulls
}

#[inline(never)]
fn extract_factors(
    qs_state: &mut QsState,
    nulls: Vec<Integer>,
    original_n: Integer,
) -> (Integer, Integer) {
    let n = qs_state.relations.len();
    let mut bit = Integer::new();
    for mut vector in nulls {
        let mut prod_right = Integer::from(1);
        let mut prod_left = Integer::from(1);
        for idx in 0..n {
            bit.assign(&vector & 1);
            vector >>= 1;
            if bit == 1 {
                prod_left *= &qs_state.relations[idx];
                prod_right *= &qs_state.roots[idx];
            }
        }
        let mut sqrt_right = prod_right.sqrt();
        prod_left %= &qs_state.n;
        sqrt_right %= &qs_state.n;
        let gcd_input = prod_left - sqrt_right;
        let factor_candidate = original_n.clone().gcd(&gcd_input);
        if factor_candidate != 1 && factor_candidate != original_n {
            let other_factor = (&original_n / &factor_candidate).complete();
            return (factor_candidate, other_factor);
        }
    }
    (Integer::new(), Integer::new())
}

#[inline(never)]
fn factor(qs_state: &mut QsState) {
    let original_n = qs_state.n.clone();
    let overall_start = Instant::now();
    println!("========== Self Initializing Quadratic Sieve Start ==========");
    println!(
        "Factoring N           = {} ({} digits) ({} bits)",
        qs_state.n,
        qs_state.n.to_string_radix(10).len(),
        qs_state.n.significant_bits()
    );
    println!("Using B               = {}", qs_state.b);
    println!("Using M               = {}", qs_state.m);
    println!("Using prime_limit     = {}", qs_state.prime_limit);
    println!("Using eps             = {}", qs_state.eps);
    println!("Using lp_multiplier   = {}", qs_state.lp_multiplier);

    let step_start = Instant::now();
    let prime_list = choose_multiplier(&qs_state.n, qs_state.b, &mut qs_state.multiplier);
    let step_end = step_start.elapsed().as_secs_f64();
    println!("Step 2 (Choose Multiplier) took {} seconds", step_end);
    qs_state.n = (&qs_state.n * qs_state.multiplier).complete();

    let step_start = Instant::now();
    let factor_base = build_factor_base(qs_state, prime_list);
    let step_end = step_start.elapsed().as_secs_f64();
    println!("Step 3 (Build Factor Base) took {} seconds", step_end);

    let step_start = Instant::now();
    sieve(qs_state, factor_base);
    let step_end = step_start.elapsed().as_secs_f64();
    println!("Step 3 (Sieving) took {} seconds", step_end);

    let step_start = Instant::now();
    let nulls = null_space_extraction(qs_state);
    let step_end = step_start.elapsed().as_secs_f64();
    println!("Step 4 (Null Space Extraction) took {} seconds", step_end);

    let step_start = Instant::now();
    let (a, b) = extract_factors(qs_state, nulls, original_n.clone());
    let step_end = step_start.elapsed().as_secs_f64();
    println!("Step 5 (Extract Factors) took {} seconds", step_end);
    let end = overall_start.elapsed().as_secs_f64();

    if a != 0 {
        println!("Non-trivial factors found: {} = {} x {}", original_n, a, b);
    } else {
        println!("No non-trivial factors found");
    }

    println!("Total time: {end}");
}

fn main() {
    let n = "4378791344783772102948750080621515168437665623852974929593741854971148718933";
    let n = n.parse::<Integer>().unwrap();
    let b: u32 = 270000;
    let m: u32 = 65536;
    let t: u32 = 64;
    let prime_limit: i32 = 220;
    let eps: u32 = 49;
    let lp_multiplier: u32 = 150;
    /*
    let n = "373784758862055327503642974151754627650123768832847679663987";
    let n = n.parse::<Integer>().unwrap();
    let b: u32 = 60000;
    let m: u32 = 65536;
    let t: u32 = 64;
    let prime_limit: i32 = 127;
    let eps: u32 = 39;
    let lp_multiplier: u32 = 80;

    let n = "7706819914707514618527375117609426832912695932717613757187193542710534314360539";
    let n = n.parse::<Integer>().unwrap();
    let b: u32 = 450_000;
    let m: u32 = 65536 * 3;
    let t: u32 = 64;
    let prime_limit: i32 = 220;
    let eps: u32 = 50;
    let lp_multiplier: u32 = 150;
    */

    let multiplier = 0; // leave at zero for automatic multiplier selection

    let root_map = vec![(0, 0); (b + 1) as usize];
    let lp_found = 0;
    let large_prime_bound = 0;
    let matrix: Vec<Integer> = Vec::new();
    let relations: Vec<Integer> = Vec::new();
    let roots: Vec<Integer> = Vec::new();
    let partials: FxHashMap<u64, (Integer, FxHashSet<i32>, Integer)> = FxHashMap::default();
    let ind = Integer::from(1);
    let sieve_values: Vec<u8> = Vec::new();
    let bainv: Vec<Vec<i32>> = vec![vec![0; 40]; (b + 1) as usize]; // 40 works for non huge numbers
    let poly_a_list: FxHashSet<Integer> = FxHashSet::default();
    let fb_primes: Vec<FBPrime> = Vec::new();
    let current_fb_primes: Vec<FBPrime> = Vec::new();

    let mut qs_state = QsState {
        n,
        b,
        m,
        t,
        prime_limit,
        eps,
        lp_multiplier,
        multiplier,
        root_map,
        lp_found,
        large_prime_bound,
        matrix,
        relations,
        roots,
        partials,
        ind,
        sieve_values,
        bainv,
        poly_a_list,
        fb_primes,
        current_fb_primes,

        b1: 0,
    };
    factor(&mut qs_state);
}

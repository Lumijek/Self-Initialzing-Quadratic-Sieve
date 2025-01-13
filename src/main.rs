#![allow(unused)]
#[global_allocator]
static GLOBAL: mimalloc::MiMalloc = mimalloc::MiMalloc;
use rand::{self, Rng};
use rug::{Assign, Complete, Float, Integer};
use rustc_hash::{FxHashMap, FxHashSet};
use std::cmp;
use std::io::{stdout, Write};
use std::process;
use std::time::Instant;

static LOWER_BOUND_SIQS: i32 = 2000;
static UPPER_BOUND_SIQS: i32 = 4000;
static SMALL_B: i32 = 1024;
static ERROR_MUL: f64 = 0.9;
const NUM_TEST_PRIMES: i32 = 300;

fn print_type_of<T>(_: &T) {
    println!("{}", std::any::type_name::<T>());
}

struct QsState {
    n: Integer,
    b: u32,
    m: u32,
    t: u32,
    prime_limit: i32,
    eps: u32,
    lp_multiplier: u32,
    multiplier: u32,

    prime_log_map: FxHashMap<u32, u32>,
    root_map: FxHashMap<u32, (u32, u32)>,
}
struct PolyState {
    a: Integer,
    b: Integer,
    c: Integer,
    b_list: Vec<Integer>,
    s: u32,
    afact: FxHashSet<u32>,
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
) {
    // If this is not the first time we're printing, move the cursor up
    // and clear those lines so we can overwrite them.
    const LINES_TO_MOVE_UP: usize = 8; // number of lines in the "table" below

    if !first_time {
        // Move cursor up by N lines
        print!("\x1B[{}A", LINES_TO_MOVE_UP);
        // Clear all lines below cursor
        print!("\x1B[J");
        stdout().flush().unwrap();
    }

    let elapsed = start_time.elapsed().as_secs_f64();

    let relations_per_second = if elapsed > 0.0 {
        relations.len() as f64 / elapsed
    } else {
        0.0
    };
    let poly_per_second = if elapsed > 0.0 {
        num_poly as f64 / elapsed
    } else {
        0.0
    };
    let percent = if target_relations > 0 {
        (relations.len() as f64 / target_relations as f64) * 100.0
    } else {
        0.0
    };
    let percent_per_second = if elapsed > 0.0 {
        percent / elapsed
    } else {
        0.0
    };

    let remaining_percent = 100.0 - percent;
    let total_remaining_secs = if percent_per_second > 0.0 {
        (remaining_percent / percent_per_second) as u64
    } else {
        0
    };

    let hours = total_remaining_secs / 3600;
    let minutes = (total_remaining_secs % 3600) / 60;
    let seconds = total_remaining_secs % 60;

    println!("Processing Status");
    println!("----------------------------------------------");
    println!("Relations per second   : {:.2}", relations_per_second);
    println!("Poly per second        : {:.2}", poly_per_second);
    println!("Percent                : {:.5}%", percent);
    println!("Percent per second     : {:.5}%", percent_per_second);
    println!(
        "Estimated Time         : {}:{:02}:{:02}",
        hours, minutes, seconds
    );
    println!("----------------------------------------------");
    stdout().flush().unwrap();
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
    // a^( (p-1)/2 ) mod p
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
    let mut num_multipliers = 0;

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

        num_multipliers += 1;
    }

    for &prime in prime_list.iter().take(num_primes).skip(1) {
        let contrib = (prime as f64).ln() / ((prime as f64) - 1.0);

        let modp = n.mod_u(prime);

        for j in 0..num_multipliers {
            let knmodp = (modp * MULT_LIST[j]) % prime;

            if knmodp == 0 || legendre(Integer::from(knmodp), prime) == 1 {
                scores[j] -= if knmodp == 0 { contrib } else { 2.0 * contrib };
            }
        }
    }

    let mut mmap: Vec<(f64, u32)> = scores[..num_multipliers]
        .iter()
        .copied()
        .zip(MULT_LIST[..num_multipliers].iter().copied())
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
    qs_state.prime_log_map.insert(2, 1);

    for prime in &prime_list[1..] {
        if legendre(qs_state.n.clone(), *prime) == 1 {
            factor_base.push(*prime as i32);
            qs_state.prime_log_map.insert(*prime, prime.ilog2());
            qs_state
                .root_map
                .insert(*prime, tonelli_shanks(&qs_state.n, prime));
        }
    }
    println!("Factor base size: {}", factor_base.len());
    factor_base
}

fn modinv(n: &Integer, mut p: i32) -> i32 {
    let mut n = n.mod_u(p as u32) as i32;
    let mut x = 0;
    let mut u = 1;
    while n != 0 {
        let mut temp = x;
        x = u;
        u = temp - (p / n) * u;
        temp = p;
        p = n;
        n = temp % n;
    }
    x
}

fn generate_a(
    n: &Integer,
    m: u32,
    factor_base: &[i32],
    poly_a_list: &mut FxHashSet<Integer>,
) -> (Integer, Vec<usize>, FxHashSet<u32>) {
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

    let target_a: Integer = (Float::with_val(53, 2 * n.clone()).sqrt() / m)
        .to_integer()
        .unwrap();
    let mut target_bits: u32 = ((target_a.significant_bits() as f64) * ERROR_MUL).round() as u32;
    let too_close = 10;
    let close_range = 5;
    let min_ratio = LOWER_BOUND_SIQS;

    let mut poly_a;
    let mut afact: FxHashSet<u32> = FxHashSet::default();
    let mut qli: Vec<usize> = Vec::new();

    loop {
        poly_a = Integer::from(1);
        afact.clear();
        qli.clear();
        loop {
            let mut found_a_factor = false;
            let mut potential_a_factor: u32 = 1;
            let mut randindex: usize = 1;
            while !found_a_factor {
                randindex = rng.gen_range(lower_polypool_index..upper_polypool_index) as usize;
                potential_a_factor = factor_base[randindex] as u32;
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

        let a1 = (&target_a / &poly_a).complete();
        if a1 < min_ratio {
            continue;
        }

        let mut mindiff = Integer::from(u64::MAX);
        let mut randindex = 0;

        for (i, fb_prime) in factor_base.iter().enumerate().take(SMALL_B as usize) {
            if (&a1 - fb_prime).complete().abs() < mindiff {
                mindiff = (&a1 - fb_prime).complete().abs();
                randindex = i;
            }
        }

        let mut found_a_factor = false;
        let mut potential_a_factor = 1;
        while !found_a_factor {
            potential_a_factor = factor_base[randindex] as u32;
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

fn generate_first_polynomial(
    qs_state: &mut QsState,
    n: &Integer,
    m: u32,
    bainv: &mut Vec<Vec<u32>>,
    soln_map: &mut [(u32, u32)],
    factor_base: &Vec<i32>,
    poly_a_list: &mut FxHashSet<Integer>,
) -> PolyState {
    let (a, qli, afact) = generate_a(n, m, factor_base, poly_a_list);
    let s = qli.len();
    let mut b_list: Vec<Integer> = vec![Integer::new(); s];
    for i in 0..s {
        let p = factor_base[qli[i]] as u32;
        let r1 = qs_state.root_map[&p].0 as i32;
        let aq = (&a / p).complete();
        let invaq = modinv(&aq, p as i32);
        let mut gamma = (r1 * invaq).rem_euclid(p as i32) as u32; // if code doesn't work, ensure overflow isn't happening here
        if gamma > p / 2 {
            gamma = p - gamma;
        }
        b_list[i] = aq * gamma;
    }

    let b: Integer = b_list.iter().sum::<Integer>().modulo(&a);
    let c = (&b * &b - n).complete() / &a;

    let mut res = Integer::new();
    let mut value = 0;

    factor_base.iter()
        .for_each(|p| {
        res.assign(&a % *p);
        if res == 0 || *p < 3 {
            return;
        }
        let ainv = modinv(&a, *p);
        let ainv2 = ((2 * ainv).rem_euclid(*p)) as u64;

        // store bainv
        
        for j in 0..s {
            value = b_list[j].mod_u(*p as u32) as u64;
            value = (value * ainv2) % (*p as u64);
            bainv[*p as usize][j] = value as u32;
        }

        // store roots
        
        /*
        let (r1_val, r2_val) = qs_state.root_map.get(&(*p as u32)).unwrap();
        r1.assign(r1_val - &b);
        r2.assign(r2_val - &b);
        r1 *= &ainv;
        r2 *= &ainv;
        soln_map[*p as usize].0 = r1.mod_u(*p as u32);
        soln_map[*p as usize].1 = r2.mod_u(*p as u32);
        */
        
        let (r1_val, r2_val) = qs_state.root_map.get(&(*p as u32)).unwrap();

        // r1
        let r1_modp = r1_val % (*p as u32);
        let b_modp = b.mod_u(*p as u32);
        let diff_u64 = if r1_modp >= b_modp {
            r1_modp - b_modp
        } else {
            (*p as u32) - (b_modp - r1_modp)
        } as u64;
        let ainv_modp = (ainv.rem_euclid(*p)) as u64;
        let value = (diff_u64 * ainv_modp) %  (*p as u64);

        // r2
        let r2_modp = r2_val % (*p as u32);
        let diff_u64 = if r2_modp >= b_modp {
            r2_modp - b_modp
        } else {
            (*p as u32) - (b_modp - r2_modp)
        } as u64;
        let value = (diff_u64 * ainv_modp) %  (*p as u64);
        
    });

    PolyState {
        a,
        b,
        c,
        b_list,
        s: s as u32,
        afact,
    }
}

fn sieve(qs_state: &mut QsState, factor_base: Vec<i32>)
/* -> (Vec<Integer>, Vec<Integer>, Vec<Integer>)*/
{
    let start = Instant::now();

    let n = qs_state.n.clone();
    let b = qs_state.b;
    let m = qs_state.m;
    let eps = qs_state.eps;

    // Factor base stuff
    let fb_len = factor_base.len() as u32;
    let fb_map: FxHashMap<_, _> = factor_base
        .iter()
        .enumerate()
        .map(|(i, val)| (*val, i))
        .collect();
    let target_relations = (fb_len + qs_state.t) as usize;
    let large_prime_bound: u64 = (b * qs_state.lp_multiplier).into();

    // threshold and misc.

    let threshold = ((Float::with_val(53, &n).sqrt() * m).log2() - eps)
        .to_f64()
        .floor();
    let mut lp_found = 0;
    let mut ind = Integer::from(1);

    // storage for results and partials
    let mut matrix = vec![Integer::new(); fb_len as usize];
    let mut relations: Vec<Integer> = Vec::new();
    let mut roots: Vec<Integer> = Vec::new();
    let mut partials: FxHashMap<u64, (Integer, Vec<i32>, Integer)> = FxHashMap::default();

    // polynomial controls
    let mut num_poly = 0;
    let interval_size = 2 * m + 1;
    let grays = get_gray_code(20);
    let mut poly_a_list: FxHashSet<Integer> = FxHashSet::default();
    let mut poly_ind = 0;

    let mut sieve_values = vec![0; interval_size as usize];
    let mut r1 = 0;
    let mut r2 = 0;

    let mut ft = true;

    let mut poly_state = PolyState {
        a: Integer::new(),
        b: Integer::new(),
        c: Integer::new(),
        b_list: Vec::new(),
        s: 0,
        afact: FxHashSet::default(),
    };
    let mut end = 0;

    let mut bainv: Vec<Vec<u32>> = vec![vec![0; 30]; (b + 1) as usize];
    let mut soln_map: Vec<(u32, u32)> = vec![(0, 0); (b + 1) as usize];

    let filtered_factor_base: Vec<u32> = factor_base
        .iter()
        .filter(|&&p| p >= qs_state.prime_limit)
        .map(|&p| p as u32)
        .collect();

    let mut pa = Integer::new();
    let mut cur_fb: Vec<u32> = Vec::new();

    while relations.len() < target_relations {
        if num_poly % 10000 == 0 {
            print_stats(&relations, target_relations, num_poly, start, ft);
        }
        ft = false;

        // Poly Stuff
        if poly_ind == 0 {
            cur_fb.clear();
            poly_state = generate_first_polynomial(qs_state, &n, m, &mut bainv, &mut soln_map, &factor_base, &mut poly_a_list);
            end = 1 << (poly_state.s - 1);
            poly_ind += 1;
            for p in &filtered_factor_base {
                pa.assign(&poly_state.a % p);
                if !pa.is_zero() {
                    cur_fb.push(*p);
                }
            }
        } else {
            let (v, e) = grays[poly_ind];
            poly_state.b += 2 * e * &poly_state.b_list[v];
            poly_state.c = (&poly_state.b * &poly_state.b - &n).complete() / &poly_state.a;
            poly_ind += 1;
            if poly_ind == end {
                poly_ind = 0;
            }
        }
        num_poly += 1;

        // Sieving stuff
    }
}
fn factor(qs_state: &mut QsState) -> (Integer, Integer) {
    let original_n = qs_state.n.clone();
    let overall_start = Instant::now();
    println!("========== Self Initializing Quadratic Sieve Start ==========");
    println!("Factoring N = {}", qs_state.n);
    println!("Using B = {}", qs_state.b);

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

    let end = overall_start.elapsed().as_secs_f64();
    println!("Elapsed: {}", end);

    (
        "1000".parse::<Integer>().unwrap(),
        "1000".parse::<Integer>().unwrap(),
    )
}

fn main() {
    let n = "373784758862055327503642974151754627650123768832847679663987";
    let n = n.parse::<Integer>().unwrap();
    let b: u32 = 68000;
    let m: u32 = 270000;
    let t: u32 = 10;
    let prime_limit: i32 = 45;
    let eps: u32 = 39;
    let lp_multiplier: u32 = 512;
    let multiplier = 0;
    let mut qs_state = QsState {
        n,
        b,
        m,
        t,
        prime_limit,
        eps,
        lp_multiplier,
        multiplier,
        prime_log_map: FxHashMap::default(),
        root_map: FxHashMap::default(),
    };
    factor(&mut qs_state);
}

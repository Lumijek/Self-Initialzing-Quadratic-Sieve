use rug::Integer;
use std::io::{self, Write};
use std::time::Instant;

pub(crate) fn get_gray_code(n: usize) -> Vec<(usize, i32)> {
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

pub(crate) fn print_stats(
    relations: &[Integer],
    target_relations: usize,
    num_poly: u32,
    start_time: Instant,
    first_time: bool,
    lp_found: usize,
) {
    const LINES_TO_MOVE_UP: usize = 13;

    if !first_time {
        print!("\x1B[{}A\x1B[J", LINES_TO_MOVE_UP);
        io::stdout().flush().unwrap();
    }

    let rel_len = relations.len() as f64;
    let non_lp_rel_len = (relations.len() - lp_found) as f64;
    let num_poly_f64 = num_poly as f64;
    let elapsed = start_time.elapsed().as_secs_f64();

    let relations_per_polynomial = rel_len / num_poly_f64;
    let relations_per_second = rel_len / elapsed;
    let poly_per_second = num_poly_f64 / elapsed;
    let percent = (rel_len / target_relations as f64) * 100.0;
    let non_lp_percent = (non_lp_rel_len / target_relations as f64) * 100.0;
    let percent_per_second = percent / elapsed;
    let non_lp_percent_per_second = non_lp_percent / elapsed;
    let total_remaining_secs = ((100.0 - percent) / percent_per_second) as u64;
    let hours = total_remaining_secs / 3600;
    let minutes = (total_remaining_secs % 3600) / 60;
    let seconds = total_remaining_secs % 60;
    println!(
        "\
Processing Status
----------------------------------------------
Total Relations            : {}
Total Partial Relations    : {}
Total Polynomials Used     : {}
Relations per polynomial   : {:.5}
Relations per second       : {:.2}
Poly per second            : {:.2}
Percent                    : {:.5}%
Percent per second         : {:.5}%
Percent per second (no LP) : {:.5}%
Estimated Time             : {}:{:02}:{:02}
----------------------------------------------",
        relations.len(),
        lp_found,
        num_poly,
        relations_per_polynomial,
        relations_per_second,
        poly_per_second,
        percent,
        percent_per_second,
        non_lp_percent_per_second,
        hours,
        minutes,
        seconds
    );
    io::stdout().flush().unwrap();
}

pub(crate) fn prime_sieve(b: u32) -> Vec<u32> {
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

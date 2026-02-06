pub(crate) mod constants;
pub(crate) mod factor_base;
pub(crate) mod linalg;
pub(crate) mod poly;
pub(crate) mod sieve;
pub(crate) mod state;
pub(crate) mod util;

use crate::qs::state::QsState;
use rug::Complete;
use std::time::Instant;

pub(crate) fn factor(qs_state: &mut QsState) {
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
    let prime_list =
        factor_base::choose_multiplier(&qs_state.n, qs_state.b, &mut qs_state.multiplier);
    let step_end = step_start.elapsed().as_secs_f64();
    println!("Step 2 (Choose Multiplier) took {} seconds", step_end);
    qs_state.n = (&qs_state.n * qs_state.multiplier).complete();

    let step_start = Instant::now();
    let (factor_base, factor_base_u32, factor_base_u64, factor_base_u128) =
        factor_base::build_factor_base(qs_state, prime_list);
    let step_end = step_start.elapsed().as_secs_f64();
    println!("Step 3 (Build Factor Base) took {} seconds", step_end);

    let step_start = Instant::now();
    sieve::sieve(
        qs_state,
        factor_base,
        factor_base_u32,
        factor_base_u64,
        factor_base_u128,
    );
    let step_end = step_start.elapsed().as_secs_f64();
    println!("Step 3 (Sieving) took {} seconds", step_end);

    let step_start = Instant::now();
    let nulls = linalg::null_space_extraction(qs_state);
    let step_end = step_start.elapsed().as_secs_f64();
    println!("Step 4 (Null Space Extraction) took {} seconds", step_end);

    let step_start = Instant::now();
    let (a, b) = linalg::extract_factors(qs_state, nulls, original_n.clone());
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

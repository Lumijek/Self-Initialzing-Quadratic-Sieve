#[global_allocator]
static GLOBAL: mimalloc::MiMalloc = mimalloc::MiMalloc;

mod qs;

use qs::state::{FBPrime, QsState};
use rug::Integer;
use rustc_hash::{FxHashMap, FxHashSet};

fn main() {
    let n = "4378791344783772102948750080621515168437665623852974929593741854971148718933";
    let n = n.parse::<Integer>().unwrap();
    let b: u32 = 270000;
    let m: u32 = 65536;
    let t: u32 = 64;
    let prime_limit: i32 = 220;
    let eps: u32 = 51;
    let lp_multiplier: u32 = 150;

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

    qs::factor(&mut qs_state);
}

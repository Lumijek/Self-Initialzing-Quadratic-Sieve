use rug::Integer;
use rustc_hash::{FxHashMap, FxHashSet};

pub(crate) struct QsState {
    pub(crate) n: Integer,
    pub(crate) b: u32,
    pub(crate) m: u32,
    pub(crate) t: u32,
    pub(crate) prime_limit: i32,
    pub(crate) eps: u32,
    pub(crate) lp_multiplier: u32,
    pub(crate) multiplier: u32,
    pub(crate) root_map: Vec<(u32, u32)>,
    pub(crate) lp_found: usize,
    pub(crate) large_prime_bound: u32,
    pub(crate) matrix: Vec<Integer>,
    pub(crate) relations: Vec<Integer>,
    pub(crate) roots: Vec<Integer>,
    pub(crate) partials: FxHashMap<u64, (Integer, FxHashSet<i32>, Integer)>,
    pub(crate) ind: Integer,
    pub(crate) sieve_values: Vec<u8>,
    pub(crate) bainv: Vec<Vec<i32>>,
    pub(crate) poly_a_list: FxHashSet<Integer>,
    pub(crate) fb_primes: Vec<FBPrime>,
    pub(crate) current_fb_primes: Vec<FBPrime>,
    pub(crate) b1: usize,
}

pub(crate) struct Polynomial {
    pub(crate) a: Integer,
    pub(crate) b: Integer,
    pub(crate) c: Integer,
    pub(crate) v: usize,
    pub(crate) e: i32,
}

pub(crate) struct PolyState {
    pub(crate) a: Integer,
    pub(crate) b: Integer,
    pub(crate) c: Integer,
    pub(crate) b_list: Vec<Integer>,
    pub(crate) s: u32,
    pub(crate) afact: FxHashSet<i32>,
}

#[derive(Clone)]
pub(crate) struct FBPrime {
    pub(crate) prime: u32,
    pub(crate) root1: i32,
    pub(crate) root2: i32,
    pub(crate) logprime: u8,
}


# Self-Initializing Quadratic Sieve (SIQS)

A high-performance implementation of the Self-Initializing Quadratic Sieve algorithm in Rust for integer factorization. 

## Description

Implementation of the Quadratic Sieve includes :
- Single Large Prime Variation
- Null Space Extraction using Gaussian Elimination over GF(2)
- Self Initialization For Polynomials
- Automatic Multiplier Selection
- Logarithms for sieving alongside the `0x80` trick

## Examples
Currently don't have automatic parameter adjustment however I have found that carefully tuning parameters should get you to about 80% as fast as msieve for the sieving portion (for numbers < 85 digits[No Double Prime Variation :( ]) however lack of Block Lanczos implementation causes overall factorizations to be slower for numbers over 50ish digits.

```rust
let n = "7706819914707514618527375117609426832912695932717613757187193542710534314360539";
let n = n.parse::<Integer>().unwrap(); //number to factor
let b: u32 = 450_000; // factor base bound
let m: u32 = 65536 * 3; // sieve interval
let t: u32 = 64; // "extra" relations to collect
let prime_limit: i32 = 220; // minimum prime to be sieved
let eps: u32 = 50; // offset to take into account prime powers and skipped primes
let lp_multiplier: u32 = 150; // large prime multiplier (lp_multiplier * b)
```
Ugly interface which will be fixed later!

## Technical Specifications

- Language: Rust
- Memory Allocator: mimalloc
- Integer Arithmetic: rug (GMP wrapper)

## TODO

- Automatic parameter adjustments
- Double (and possibly triple) large prime variation
- Block Sieving for better cache utilization
- Bucket Sieving for better cache utilization
- Implement Block Lanczos over GF(2) instead of Gaussian Elimination
- Micro-optimizations to speed up factor extraction
- Clean up code as it is a bit messy and also add comments
- Parallel Processing for sieving

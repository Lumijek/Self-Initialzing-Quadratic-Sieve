use crate::qs::state::QsState;

use rug::{Assign, Complete, Integer};

#[inline(never)]
pub(crate) fn null_space_extraction(qs_state: &mut QsState) -> Vec<Integer> {
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
pub(crate) fn extract_factors(
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

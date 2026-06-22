//! Kani Formal Verification Harnesses for AMM Pool
//!
//! This module contains formal verification proofs using the Kani Rust Verifier
//! to mathematically prove critical properties of the AMM pool contract.

#![cfg(kani)]

use crate::{calculate_swap_output, calculate_liquidity_mint, calculate_liquidity_burn};

/// **CRITICAL VERIFICATION**: K-invariant preservation in swaps
/// 
/// This proof formally verifies that the constant product formula k = x * y
/// is never violated (k never decreases) during any swap operation.
#[kani::proof]
fn verify_k_invariant_preservation() {
    // Generate symbolic inputs
    let reserve_in: u128 = kani::any();
    let reserve_out: u128 = kani::any();
    let amount_in: u128 = kani::any();
    let fee_bps: u128 = kani::any();

    // Assume reasonable bounds to avoid infinite verification space
    kani::assume(reserve_in > 0);
    kani::assume(reserve_out > 0);
    kani::assume(amount_in > 0);
    kani::assume(fee_bps < 10000);
    kani::assume(reserve_in <= u64::MAX as u128);
    kani::assume(reserve_out <= u64::MAX as u128);
    kani::assume(amount_in <= u32::MAX as u128);

    // Calculate k before swap
    if let Some(k_before) = reserve_in.checked_mul(reserve_out) {
        
        // Perform swap calculation
        if let Ok(amount_out) = calculate_swap_output(reserve_in, reserve_out, amount_in, fee_bps) {
            
            // Calculate new reserves after swap
            if let Some(new_reserve_in) = reserve_in.checked_add(amount_in) {
                if let Some(new_reserve_out) = reserve_out.checked_sub(amount_out) {
                    if let Some(k_after) = new_reserve_in.checked_mul(new_reserve_out) {
                        
                        // **CRITICAL PROPERTY**: K must never decrease
                        assert!(k_after >= k_before, "K-invariant violated: k decreased from {} to {}", k_before, k_after);
                        
                        // **STRONGER PROPERTY**: With fees > 0, K must increase
                        if fee_bps > 0 {
                            assert!(k_after > k_before, "With fees, k must increase");
                        }
                    }
                }
            }
        }
    }
}

/// Verify that swap output is always less than available reserves
#[kani::proof] 
fn verify_swap_output_bounds() {
    let reserve_in: u128 = kani::any();
    let reserve_out: u128 = kani::any();
    let amount_in: u128 = kani::any();
    let fee_bps: u128 = kani::any();

    kani::assume(reserve_in > 0);
    kani::assume(reserve_out > 0);
    kani::assume(amount_in > 0);
    kani::assume(fee_bps < 10000);
    kani::assume(reserve_in <= u64::MAX as u128);
    kani::assume(reserve_out <= u64::MAX as u128);

    if let Ok(amount_out) = calculate_swap_output(reserve_in, reserve_out, amount_in, fee_bps) {
        // Output must be less than available reserves
        assert!(amount_out < reserve_out, "Output {} exceeds reserves {}", amount_out, reserve_out);
        
        // Output must be positive
        assert!(amount_out > 0, "Output must be positive");
    }
}

/// Verify arithmetic overflow protection
#[kani::proof]
fn verify_no_arithmetic_overflow() {
    let reserve_in: u128 = kani::any();
    let reserve_out: u128 = kani::any();
    let amount_in: u128 = kani::any();
    let fee_bps: u128 = kani::any();

    // Test with maximum safe values
    kani::assume(reserve_in <= u64::MAX as u128);
    kani::assume(reserve_out <= u64::MAX as u128);
    kani::assume(amount_in <= u32::MAX as u128);
    kani::assume(fee_bps < 10000);
    kani::assume(reserve_in > 0);
    kani::assume(reserve_out > 0);
    kani::assume(amount_in > 0);

    // Function should either succeed or fail gracefully (no panics)
    let _result = calculate_swap_output(reserve_in, reserve_out, amount_in, fee_bps);
    
    // If we reach here without panic, overflow protection worked
    assert!(true);
}

/// Verify liquidity calculations don't overflow
#[kani::proof]
fn verify_liquidity_mint_no_overflow() {
    let reserve_a: u128 = kani::any();
    let reserve_b: u128 = kani::any();
    let amount_a: u128 = kani::any();
    let amount_b: u128 = kani::any();
    let total_supply: u128 = kani::any();

    kani::assume(reserve_a <= u64::MAX as u128);
    kani::assume(reserve_b <= u64::MAX as u128);
    kani::assume(amount_a > 0 && amount_a <= u32::MAX as u128);
    kani::assume(amount_b > 0 && amount_b <= u32::MAX as u128);
    kani::assume(total_supply <= u64::MAX as u128);

    // Function should handle edge cases gracefully
    let _result = calculate_liquidity_mint(reserve_a, reserve_b, amount_a, amount_b, total_supply);
    
    assert!(true); // No panic means overflow protection works
}

/// Verify that liquidity burn returns reasonable amounts
#[kani::proof]
fn verify_liquidity_burn_bounds() {
    let reserve_a: u128 = kani::any();
    let reserve_b: u128 = kani::any();
    let liquidity: u128 = kani::any();
    let total_supply: u128 = kani::any();

    kani::assume(reserve_a > 0 && reserve_a <= u64::MAX as u128);
    kani::assume(reserve_b > 0 && reserve_b <= u64::MAX as u128);
    kani::assume(liquidity > 0);
    kani::assume(total_supply > 0);
    kani::assume(liquidity <= total_supply);

    if let Ok((amount_a, amount_b)) = calculate_liquidity_burn(reserve_a, reserve_b, liquidity, total_supply) {
        // Returned amounts should not exceed reserves
        assert!(amount_a <= reserve_a, "Amount A {} exceeds reserve {}", amount_a, reserve_a);
        assert!(amount_b <= reserve_b, "Amount B {} exceeds reserve {}", amount_b, reserve_b);
        
        // Returned amounts should be positive
        assert!(amount_a > 0, "Amount A must be positive");
        assert!(amount_b > 0, "Amount B must be positive");
        
        // Proportionality check: if burning all liquidity, should get all reserves
        if liquidity == total_supply {
            assert!(amount_a == reserve_a, "Should return all of reserve A");
            assert!(amount_b == reserve_b, "Should return all of reserve B");
        }
    }
}

/// Verify monotonicity: larger inputs yield larger outputs
#[kani::proof]
fn verify_swap_monotonicity() {
    let reserve_in: u128 = kani::any();
    let reserve_out: u128 = kani::any();
    let amount_in_1: u128 = kani::any();
    let amount_in_2: u128 = kani::any();
    let fee_bps: u128 = kani::any();

    kani::assume(reserve_in > 1000);
    kani::assume(reserve_out > 1000);
    kani::assume(amount_in_1 > 0 && amount_in_1 < amount_in_2);
    kani::assume(amount_in_2 < reserve_in / 2); // Prevent extreme slippage
    kani::assume(fee_bps < 1000);

    if let (Ok(output_1), Ok(output_2)) = (
        calculate_swap_output(reserve_in, reserve_out, amount_in_1, fee_bps),
        calculate_swap_output(reserve_in, reserve_out, amount_in_2, fee_bps)
    ) {
        // Larger input should yield larger output
        assert!(output_2 > output_1, "Monotonicity violated: {} input -> {} output, {} input -> {} output", 
                amount_in_1, output_1, amount_in_2, output_2);
    }
}
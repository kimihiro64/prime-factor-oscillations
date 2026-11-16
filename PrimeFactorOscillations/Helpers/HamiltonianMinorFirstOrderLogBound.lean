/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianMinorUniformExpansion

/-! # A common finite logarithmic envelope for the actual first minor correction

The signed correction is retained in the sharper two-power theorem.
This magnitude estimate is used only for its weaker ratio corollary.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

theorem hamiltonian_minor_first_order_log_numerator
    (n r a delta K : Real) (hn : Real.exp 1 <= n) (hr : 0 <= r)
    (hR : r <= Real.log (2 * n) ^ 3) (ha : 1 <= a)
    (hA : a <= Real.log n ^ K) (hDelta : 0 < delta)
    (hDelta1 : delta <= 1) (hK : 0 <= K) :
    100 * (1 + r) ^ 2 * (a / delta) ^ 2 <=
      hamiltonianMinorUniformConstant delta *
        Real.log (2 * n) ^ hamiltonianMinorUniformExponent K := by
  let k := Nat.ceil K
  let d := 1 + 1 / delta
  let L := Real.log (2 * n)
  let M := hamiltonianMinorUniformExponent K
  have hn0 : 0 < n := (Real.exp_pos 1).trans_le hn
  have hLog1 : 1 <= Real.log n := by
    have h := Real.log_le_log (Real.exp_pos 1) hn
    simpa only [Real.log_exp] using h
  have hLog0 : 0 <= Real.log n := by linarith only [hLog1]
  have hLogB : Real.log n <= L := Real.log_le_log hn0 (by linarith only [hn0])
  have hL1 : 1 <= L := hLog1.trans hLogB
  have hL0 : 0 <= L := by linarith only [hL1]
  have hACeil : a <= Real.log n ^ k := by
    calc
      _ <= Real.log n ^ K := hA
      _ <= Real.log n ^ (k : Real) :=
        Real.rpow_le_rpow_of_exponent_le hLog1 (Nat.le_ceil K)
      _ = _ := Real.rpow_natCast _ k
  have hAL : a <= L ^ k :=
    hACeil.trans (wick_nonnegative_power_le _ _ hLog0 hLogB k)
  have hOneLK : 1 <= L ^ k := by
    simpa only [one_pow] using wick_nonnegative_power_le (1 : Real) L (by norm_num) hL1 k
  have hOneL3 : 1 <= L ^ 3 := by
    simpa only [one_pow] using wick_nonnegative_power_le (1 : Real) L (by norm_num) hL1 3
  have hRank : 1 + r <= 2 * L ^ 3 := by linarith only [hR, hOneL3]
  have hEntry : 1 + a / delta <= d * L ^ k := by
    calc
      _ <= L ^ k + L ^ k / delta :=
        add_le_add hOneLK (div_le_div_of_nonneg_right hAL hDelta.le)
      _ = _ := by dsimp [d]; ring
  have hWeight : (1 + r) ^ 4 * (1 + a / delta) ^ 24 <=
      16 * d ^ 24 * L ^ M := by
    calc
      _ <= (2 * L ^ 3) ^ 4 * (d * L ^ k) ^ 24 :=
        mul_le_mul
          (wick_nonnegative_power_le _ _ (by positivity) hRank 4)
          (wick_nonnegative_power_le _ _ (by positivity) hEntry 24)
          (pow_nonneg (by positivity) 24) (pow_nonneg (by positivity) 4)
      _ = 16 * d ^ 24 * ((L ^ 3) ^ 4 * (L ^ k) ^ 24) := by
        rw [mul_pow, mul_pow]
        ring
      _ = _ := by
        rw [<- pow_mul, <- pow_mul, <- pow_add]
        simp only [M, hamiltonianMinorUniformExponent, k, Nat.reduceMul, Nat.mul_comm]
  have hPoly := hamiltonian_minor_polynomial_budget delta r a hDelta hDelta1 hr ha
  have hNumerator : 100 * (1 + r) ^ 2 * (a / delta) ^ 2 <=
      hamiltonianMinorPolynomialConstant delta * (1 + r) ^ 4 *
        (1 + a / delta) ^ 24 := by
    have hError := hPoly.2.2.1
    have hNonneg := hPoly.2.1
    linarith only [hError, hNonneg]
  calc
    _ <= _ := hNumerator
    _ = hamiltonianMinorPolynomialConstant delta * ((1 + r) ^ 4 *
        (1 + a / delta) ^ 24) := by ring
    _ <= hamiltonianMinorPolynomialConstant delta * (16 * d ^ 24 * L ^ M) :=
      mul_le_mul_of_nonneg_left hWeight hPoly.1.le
    _ = _ := by dsimp [hamiltonianMinorUniformConstant, d, L, M]; ring

end PrimeFactorOscillations

/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianMinorLogError

/-! # Exponential transfer after full signed first-order compensation

The signed main term stays in the expansion. Only its square and the
already bounded logarithmic remainder contribute to the error.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

theorem hamiltonian_minor_exponential_transfer (t alpha eps : Real)
    (ht : 0 < t) (hEps0 : 0 <= eps) (hEps1 : eps <= 1)
    (hLog : abs (2 * Real.log t - alpha) <= eps)
    (hRange : abs alpha + eps <= 1) :
    abs (t ^ 2 - (1 + alpha)) <= 2 * alpha ^ 2 + 3 * eps := by
  let x := 2 * Real.log t
  let d := x - alpha
  have hD : abs d <= eps := hLog
  have hXIdentity : x = alpha + d := by dsimp only [d]; ring
  have hX : abs x <= 1 := by
    calc
      _ = abs (alpha + d) := congrArg abs hXIdentity
      _ <= abs alpha + abs d := abs_add_le _ _
      _ <= abs alpha + eps := add_le_add (le_refl _) hD
      _ <= 1 := hRange
  have hTaylor : abs (Real.exp x - 1 - x) <= x ^ 2 := by
    have h := Real.norm_exp_sub_one_sub_id_le (show norm x <= 1 by
      simpa only [Real.norm_eq_abs] using hX)
    simpa only [Real.norm_eq_abs, sq_abs] using h
  have hDSquare : d ^ 2 <= eps ^ 2 := by
    have h := mul_le_mul hD hD (abs_nonneg d) hEps0
    simpa only [<- pow_two, sq_abs] using h
  have hEpsSquare : eps ^ 2 <= eps := by
    have h := mul_nonneg hEps0 (sub_nonneg.mpr hEps1)
    nlinarith only [h]
  have hXSquare : x ^ 2 <= 2 * alpha ^ 2 + 2 * eps := by
    have hFirst : x ^ 2 <= 2 * alpha ^ 2 + 2 * d ^ 2 := by
      rw [hXIdentity]
      nlinarith only [sq_nonneg (alpha - d)]
    nlinarith only [hFirst, hDSquare, hEpsSquare]
  have hExp : Real.exp x = t ^ 2 := by
    dsimp only [x]
    rw [two_mul, Real.exp_add]
    simp only [Real.exp_log ht, pow_two]
  calc
    _ = abs ((Real.exp x - 1 - x) + d) := by
      rw [hExp]
      dsimp only [d]
      congr 1
      ring
    _ <= abs (Real.exp x - 1 - x) + abs d := abs_add_le _ _
    _ <= x ^ 2 + eps := add_le_add hTaylor hD
    _ <= _ := by linarith only [hXSquare]

end PrimeFactorOscillations

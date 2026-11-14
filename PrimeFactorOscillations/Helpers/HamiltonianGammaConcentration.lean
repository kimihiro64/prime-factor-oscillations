/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import PrimeFactorOscillations.Helpers.HamiltonianGammaChernoff

/-! # Explicit central Gamma concentration

Quadratic logarithm bounds give explicit constants in both Gamma tails.
The shape is n+1 throughout. The inverse variable n/T is handled by the
subsequent cutoff transfer; no centering at n is silently substituted.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

theorem log_one_add_quadratic_upper (x : Real) (hx0 : 0 <= x) (hx1 : x <= 1) :
    Real.log (1 + x) <= x - x ^ 2 / 9 := by
  let u := Real.sqrt (1 + x)
  have hu0 : 0 <= u := Real.sqrt_nonneg _
  have hSq : u ^ 2 = 1 + x := Real.sq_sqrt (by linarith only [hx0])
  have huPos : 0 < u := Real.sqrt_pos.mpr (by linarith only [hx0])
  have hu2 : u <= 2 := by nlinarith only [hu0, hSq, hx1]
  have hLogEq : Real.log (1 + x) = 2 * Real.log u := by
    simpa only [Real.log_pow, Nat.cast_ofNat] using congrArg Real.log hSq.symm
  have hLog : Real.log (1 + x) <= 2 * (u - 1) := by
    rw [hLogEq]
    exact mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos huPos) (by norm_num)
  have hFactor : x = (u - 1) * (u + 1) := by nlinarith only [hSq]
  have hBound : (u + 1) ^ 2 <= 9 := by nlinarith only [hSq, hx1, hu2]
  have hQuad : x ^ 2 <= 9 * (u - 1) ^ 2 := by
    calc
      _ = (u - 1) ^ 2 * (u + 1) ^ 2 := by rw [hFactor]; ring
      _ <= (u - 1) ^ 2 * 9 :=
        mul_le_mul_of_nonneg_left hBound (sq_nonneg (u - 1))
      _ = _ := by ring
  have hIdentity : x - 2 * (u - 1) = (u - 1) ^ 2 := by nlinarith only [hSq]
  nlinarith only [hLog, hQuad, hIdentity]

theorem log_one_sub_quadratic_upper (x : Real) (hx0 : 0 <= x) (hx1 : x < 1) :
    Real.log (1 - x) <= -x - x ^ 2 / 4 := by
  let u := Real.sqrt (1 - x)
  have hu0 : 0 <= u := Real.sqrt_nonneg _
  have hSq : u ^ 2 = 1 - x := Real.sq_sqrt (le_of_lt (sub_pos.mpr hx1))
  have huPos : 0 < u := Real.sqrt_pos.mpr (sub_pos.mpr hx1)
  have hu1 : u <= 1 := by nlinarith only [hu0, hSq, hx0]
  have hLogEq : Real.log (1 - x) = 2 * Real.log u := by
    simpa only [Real.log_pow, Nat.cast_ofNat] using congrArg Real.log hSq.symm
  have hLog : Real.log (1 - x) <= 2 * (u - 1) := by
    rw [hLogEq]
    exact mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos huPos) (by norm_num)
  have hFactor : x = (1 - u) * (1 + u) := by nlinarith only [hSq]
  have hBound : (1 + u) ^ 2 <= 4 := by nlinarith only [hSq, hx0, hu1]
  have hQuad : x ^ 2 <= 4 * (u - 1) ^ 2 := by
    calc
      _ = (1 - u) ^ 2 * (1 + u) ^ 2 := by rw [hFactor]; ring
      _ <= (1 - u) ^ 2 * 4 :=
        mul_le_mul_of_nonneg_left hBound (sq_nonneg (1 - u))
      _ = _ := by ring
  have hIdentity : -x - 2 * (u - 1) = (u - 1) ^ 2 := by nlinarith only [hSq]
  nlinarith only [hLog, hQuad, hIdentity]

theorem gammaDirectAverage_upper_central
    (n : Nat) (x : Real) (hx0 : 0 <= x) (hx1 : x <= 1) :
    gammaDirectAverage n
      (Set.indicator (Set.Ici (((n : Real) + 1) * (1 + x))) (fun _ => (1 : Real))) <=
      Real.exp (-((n : Real) + 1) * x ^ 2 / 9) := by
  let M : Real := (n : Real) + 1
  let lambda : Real := x / (1 + x)
  have hPos : 0 < 1 + x := by linarith only [hx0]
  have hLambda0 : 0 <= lambda := div_nonneg hx0 (le_of_lt hPos)
  have hOne : 1 - lambda = 1 / (1 + x) := by
    dsimp [lambda]
    field_simp [ne_of_gt hPos]
    ring
  have hLambda1 : lambda < 1 := by
    apply sub_pos.mp
    rw [hOne]
    exact one_div_pos.mpr hPos
  have hCost :
      Real.exp (-lambda * (M * (1 + x))) * (1 - lambda) ^ (-M) =
        Real.exp (M * (Real.log (1 + x) - x)) := by
    rw [hOne, Real.rpow_def_of_pos (one_div_pos.mpr hPos)]
    simp only [one_div, Real.log_inv]
    rw [<- Real.exp_add]
    congr 1
    dsimp [lambda, M]
    field_simp [ne_of_gt hPos]
    ring
  have hM0 : 0 <= M := add_nonneg (Nat.cast_nonneg n) (by norm_num)
  calc
    _ <= Real.exp (-lambda * (M * (1 + x))) * (1 - lambda) ^ (-M) :=
      gammaDirectAverage_upper_tail n (M * (1 + x)) lambda hLambda0 hLambda1
    _ = Real.exp (M * (Real.log (1 + x) - x)) := hCost
    _ <= Real.exp (-M * x ^ 2 / 9) := by
      apply Real.exp_le_exp.mpr
      have h := mul_le_mul_of_nonneg_left (log_one_add_quadratic_upper x hx0 hx1) hM0
      nlinarith only [h]

theorem gammaDirectAverage_lower_central
    (n : Nat) (x : Real) (hx0 : 0 <= x) (hx1 : x < 1) :
    gammaDirectAverage n
      (Set.indicator (Set.Iic (((n : Real) + 1) * (1 - x))) (fun _ => (1 : Real))) <=
      Real.exp (-((n : Real) + 1) * x ^ 2 / 4) := by
  let M : Real := (n : Real) + 1
  let lambda : Real := -x / (1 - x)
  have hPos : 0 < 1 - x := sub_pos.mpr hx1
  have hLambda0 : lambda <= 0 :=
    div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hx0) (le_of_lt hPos)
  have hOne : 1 - lambda = 1 / (1 - x) := by
    dsimp [lambda]
    field_simp [ne_of_gt hPos]
    ring
  have hCost :
      Real.exp (-lambda * (M * (1 - x))) * (1 - lambda) ^ (-M) =
        Real.exp (M * (Real.log (1 - x) + x)) := by
    rw [hOne, Real.rpow_def_of_pos (one_div_pos.mpr hPos)]
    simp only [one_div, Real.log_inv]
    rw [<- Real.exp_add]
    congr 1
    dsimp [lambda, M]
    field_simp [ne_of_gt hPos]
    ring
  have hM0 : 0 <= M := add_nonneg (Nat.cast_nonneg n) (by norm_num)
  calc
    _ <= Real.exp (-lambda * (M * (1 - x))) * (1 - lambda) ^ (-M) :=
      gammaDirectAverage_lower_tail n (M * (1 - x)) lambda hLambda0
    _ = Real.exp (M * (Real.log (1 - x) + x)) := hCost
    _ <= Real.exp (-M * x ^ 2 / 4) := by
      apply Real.exp_le_exp.mpr
      have h := mul_le_mul_of_nonneg_left (log_one_sub_quadratic_upper x hx0 hx1) hM0
      nlinarith only [h]

end PrimeFactorOscillations

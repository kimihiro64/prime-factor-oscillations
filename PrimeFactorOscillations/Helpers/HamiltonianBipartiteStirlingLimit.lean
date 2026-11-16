/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianPrimeCircleAsymptotic
import PrimeFactorOscillations.Helpers.HamiltonianSublogBipartiteCount

/-! # Exact unoriented Stirling normalization for arbitrary bipartite kernels -/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations

open LPF

theorem hamiltonian_bipartite_pi_ratio_identity
    {J : Type*} [Fintype J] [DecidableEq J]
    (T : Matrix J J Real) (hn : 1 <= Fintype.card J) :
    hamiltonianBipartiteCountRatio T *
        (Stirling.stirlingSeq (Fintype.card J) ^ 2 / Real.pi) =
      (hamiltonianCycleSum (bipartiteLift T) / 2) /
        (Real.pi * Real.exp (-2 * (Fintype.card J : Real))) := by
  let n := Fintype.card J
  have hnR : 0 < (n : Real) := Nat.cast_pos.mpr (by dsimp [n]; omega)
  have hFact : 0 < (n.factorial : Real) := Nat.cast_pos.mpr (Nat.factorial_pos n)
  have hE : Real.exp (n : Real) = (Real.exp 1) ^ n := by
    simpa only [mul_one] using hamiltonian_exp_nat_scalar 1 n
  have hE2 : Real.exp (2 * (n : Real)) = ((Real.exp 1) ^ n) ^ 2 := by
    rw [show 2 * (n : Real) = (n : Real) + (n : Real) by ring, Real.exp_add, hE]
    ring
  have hNeg : Real.exp (-2 * (n : Real)) = 1 / Real.exp (2 * (n : Real)) := by
    rw [show -2 * (n : Real) = -(2 * (n : Real)) by ring, Real.exp_neg, one_div]
  unfold hamiltonianBipartiteCountRatio
  change (((n : Real) ^ n / (n.factorial : Real)) ^ 2 *
      ((n : Real) * hamiltonianCycleSum (bipartiteLift T))) *
        (Stirling.stirlingSeq n ^ 2 / Real.pi) = _
  simp only [Stirling.stirlingSeq, div_pow, mul_pow,
    Real.sq_sqrt (mul_nonneg (by norm_num : (0 : Real) <= 2) hnR.le)]
  rw [hNeg, hE2]
  field_simp [ne_of_gt hnR, ne_of_gt hFact, Real.pi_ne_zero, Real.exp_ne_zero]
  <;> ring

theorem hamiltonian_bipartite_pi_error_from_factorial
    {J : Type*} [Fintype J] [DecidableEq J]
    (T : Matrix J J Real) (hn : 1 <= Fintype.card J)
    (hCount : abs (hamiltonianBipartiteCountRatio T - 1) <=
      (Fintype.card J : Real) ^ (-1 / 2 : Real)) :
    abs ((hamiltonianCycleSum (bipartiteLift T) / 2) /
      (Real.pi * Real.exp (-2 * (Fintype.card J : Real))) - 1) <=
        2 * (Fintype.card J : Real) ^ (-1 / 2 : Real) := by
  have hnR : (1 : Real) <= (Fintype.card J : Real) := by exact_mod_cast hn
  have hE : 0 <= (Fintype.card J : Real) ^ (-1 / 2 : Real) :=
    Real.rpow_nonneg (by positivity) _
  have hE1 : (Fintype.card J : Real) ^ (-1 / 2 : Real) <= 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hnR (by norm_num)
  have hD : 0 <= 1 / (3 * (Fintype.card J : Real)) := by positivity
  have hProduct := hamiltonian_relative_product_error (hamiltonianBipartiteCountRatio T)
    (Stirling.stirlingSeq (Fintype.card J) ^ 2 / Real.pi)
    ((Fintype.card J : Real) ^ (-1 / 2 : Real)) (1 / (3 * (Fintype.card J : Real)))
    hE hE1 hD hCount (hamiltonian_stirling_square_relative (Fintype.card J) hn)
  rw [hamiltonian_bipartite_pi_ratio_identity T hn] at hProduct
  have hPower : 1 / (Fintype.card J : Real) <=
      (Fintype.card J : Real) ^ (-1 / 2 : Real) := by
    have h := Real.rpow_le_rpow_of_exponent_le hnR (by norm_num : (-1 : Real) <= -1 / 2)
    simpa only [Real.rpow_neg_one, one_div] using h
  have hSmall : 2 * (1 / (3 * (Fintype.card J : Real))) <=
      (Fintype.card J : Real) ^ (-1 / 2 : Real) := by
    calc
      _ = (2 / 3 : Real) * (1 / (Fintype.card J : Real)) := by ring
      _ <= 1 / (Fintype.card J : Real) := by
        nlinarith only [show (0 : Real) <= 1 / (Fintype.card J : Real) by positivity]
      _ <= _ := hPower
  exact hProduct.trans (by linarith only [hSmall])

end PrimeFactorOscillations

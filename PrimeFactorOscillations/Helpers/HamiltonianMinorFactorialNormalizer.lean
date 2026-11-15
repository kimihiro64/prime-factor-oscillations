/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Analysis.SpecialFunctions.Stirling
import PrimeFactorOscillations.Helpers.HamiltonianScalingLogRemainder

/-! # The full factorial rank shift with a two-power error

Robbins' stepwise bound is summed only over the actual deleted rank.
The universal Stirling constant cancels exactly.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

def hamiltonianLogPermanentNormalizer (n : Nat) : Real :=
  Real.log (n.factorial : Real) - (n : Real) * Real.log (n : Real)

theorem hamiltonian_stirling_log_rank_budget (m r : Nat) (hm : 1 <= m) :
    0 <= Real.log (Stirling.stirlingSeq m) - Real.log (Stirling.stirlingSeq (m + r)) /\
    Real.log (Stirling.stirlingSeq m) - Real.log (Stirling.stirlingSeq (m + r)) <=
      (r : Real) / (12 * (m : Real) ^ 2) := by
  have hm0 : 0 < (m : Real) := Nat.cast_pos.mpr (by omega)
  have hDen0 : 0 < 12 * (m : Real) ^ 2 := mul_pos (by norm_num) (sq_pos_of_pos hm0)
  induction r with
  | zero => simp
  | succ r ih =>
    let k := m + r
    have hk : 1 <= k := by dsimp only [k]; omega
    have hk0 : (m : Real) <= (k : Real) := by dsimp only [k]; exact_mod_cast Nat.le_add_right m r
    have hStep0 : 0 <= Real.log (Stirling.stirlingSeq k) -
        Real.log (Stirling.stirlingSeq (k + 1)) := by
      have h := Stirling.log_stirlingSeq'_antitone (show k - 1 <= k by omega)
      change Real.log (Stirling.stirlingSeq (k + 1)) <=
        Real.log (Stirling.stirlingSeq (k - 1 + 1)) at h
      rw [Nat.sub_add_cancel hk] at h
      exact sub_nonneg.mpr h
    have hDen : 12 * (m : Real) ^ 2 <= 12 * (k : Real) * ((k : Real) + 1) := by
      have hK0 : 0 <= (k : Real) := Nat.cast_nonneg _
      nlinarith only [hk0, hm0, hK0]
    have hStep := (Stirling.log_stirlingSeq_sdiff_le k).trans
      (one_div_le_one_div_of_le hDen0 hDen)
    have hTel : Real.log (Stirling.stirlingSeq m) -
        Real.log (Stirling.stirlingSeq (m + (r + 1))) =
        (Real.log (Stirling.stirlingSeq m) - Real.log (Stirling.stirlingSeq (m + r))) +
        (Real.log (Stirling.stirlingSeq k) - Real.log (Stirling.stirlingSeq (k + 1))) := by
      dsimp only [k]
      rw [Nat.add_assoc]
      ring
    rw [hTel]
    refine And.intro (add_nonneg ih.1 hStep0) ?_
    have hUpper := add_le_add ih.2 hStep
    simpa only [Nat.cast_add, Nat.cast_one, add_div] using hUpper

theorem hamiltonian_log_permanent_normalizer_stirling (n : Nat) (hn : 1 <= n) :
    hamiltonianLogPermanentNormalizer n =
      Real.log (Stirling.stirlingSeq n) + Real.log 2 / 2 +
        Real.log (n : Real) / 2 - (n : Real) := by
  have hn0 : 0 < (n : Real) := Nat.cast_pos.mpr (by omega)
  have h := Stirling.log_stirlingSeq_formula n
  rw [Real.log_div (ne_of_gt hn0) (Real.exp_ne_zero 1), Real.log_exp,
    Real.log_mul (by norm_num : Not ((2 : Real) = 0)) (ne_of_gt hn0)] at h
  unfold hamiltonianLogPermanentNormalizer
  nlinarith only [h]

theorem hamiltonian_log_one_sub_linear_budget (u : Real) (hu0 : 0 <= u) (hu : u <= 1 / 2) :
    abs (Real.log (1 - u) + u) <= 2 * u ^ 2 := by
  have hCubic := hamiltonian_log_one_add_cubic_small (-u)
    (by simpa only [abs_neg, abs_of_nonneg hu0] using hu)
  have hC : abs (Real.log (1 - u) + u + u ^ 2 / 2) <= 2 * u ^ 3 := by
    simpa only [sub_neg_eq_add, neg_sq, abs_neg, abs_of_nonneg hu0, sub_eq_add_neg, neg_neg] using hCubic
  have hSquare : abs (u ^ 2 / 2) = u ^ 2 / 2 := abs_of_nonneg (div_nonneg (sq_nonneg u) (by norm_num))
  calc
    _ = abs ((Real.log (1 - u) + u + u ^ 2 / 2) + -(u ^ 2 / 2)) := by congr 1; ring
    _ <= abs (Real.log (1 - u) + u + u ^ 2 / 2) + abs (-(u ^ 2 / 2)) := abs_add_le _ _
    _ = abs (Real.log (1 - u) + u + u ^ 2 / 2) + u ^ 2 / 2 := by rw [abs_neg, hSquare]
    _ <= 2 * u ^ 3 + u ^ 2 / 2 := add_le_add hC (le_refl _)
    _ <= _ := by
      have h := mul_le_mul_of_nonneg_left hu (sq_nonneg u)
      nlinarith only [h, sq_nonneg u]


theorem hamiltonian_log_permanent_normalizer_exact (n : Nat) (hn : 1 <= n) :
    hamiltonianLogPermanentNormalizer n =
      Real.log ((n.factorial : Real) / (n : Real) ^ n) := by
  have hn0 : Not ((n : Real) = 0) := ne_of_gt (Nat.cast_pos.mpr (show 0 < n by omega))
  have hFactorial : Not ((n.factorial : Real) = 0) := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  rw [Real.log_div hFactorial (pow_ne_zero n hn0), Real.log_pow]
  rfl

theorem hamiltonian_log_permanent_normalizer_rank_shift (n r : Nat)
    (hn : 4 <= n) (hr : (r : Real) <= (n : Real) / 2) :
    abs (2 * (hamiltonianLogPermanentNormalizer (n - r) -
      hamiltonianLogPermanentNormalizer n) -
        (2 * (r : Real) - (r : Real) / (n : Real))) <=
      2 * (r : Real) * ((r : Real) + 1) / (n : Real) ^ 2 := by
  let m := n - r
  let u := (r : Real) / (n : Real)
  have hN4 : (4 : Real) <= (n : Real) := by exact_mod_cast hn
  have hN0 : 0 < (n : Real) := by linarith only [hN4]
  have hNne : Not ((n : Real) = 0) := ne_of_gt hN0
  have hr0 : 0 <= (r : Real) := Nat.cast_nonneg _
  have hrn : r <= n := by
    have h : (r : Real) <= (n : Real) := by linarith only [hr, hN0]
    exact_mod_cast h
  have hMVal : (m : Real) = (n : Real) - (r : Real) := by
    dsimp only [m]
    rw [Nat.cast_sub hrn]
  have hMHalf : (n : Real) / 2 <= (m : Real) := by rw [hMVal]; linarith only [hr]
  have hM0 : 0 < (m : Real) := by linarith only [hMHalf, hN0]
  have hm : 1 <= m := by
    have h : (1 : Real) <= (m : Real) := by linarith only [hMHalf, hN4]
    exact_mod_cast h
  have hu0 : 0 <= u := div_nonneg hr0 (le_of_lt hN0)
  have hUClear : u * (n : Real) = (r : Real) := by dsimp only [u]; field_simp [hNne]
  have hu : u <= 1 / 2 := by
    apply le_of_mul_le_mul_right _ hN0
    rw [hUClear]
    linarith only [hr]
  have hMR : m + r = n := Nat.sub_add_cancel hrn
  have hV := hamiltonian_stirling_log_rank_budget m r hm
  rw [hMR] at hV
  have hSquare := mul_le_mul hMHalf hMHalf
    (show (0 : Real) <= (n : Real) / 2 by linarith only [hN0]) (le_of_lt hM0)
  have hDen : (n : Real) ^ 2 <= 12 * (m : Real) ^ 2 := by
    nlinarith only [hSquare, sq_nonneg (m : Real)]
  have hDivide : (r : Real) / (12 * (m : Real) ^ 2) <=
      (r : Real) / (n : Real) ^ 2 :=
    div_le_div_of_nonneg_left hr0 (sq_pos_of_pos hN0) hDen
  have hVAbs : abs (Real.log (Stirling.stirlingSeq m) - Real.log (Stirling.stirlingSeq n)) <=
      (r : Real) / (n : Real) ^ 2 := by
    rw [abs_of_nonneg hV.1]
    exact hV.2.trans hDivide
  have hRatio : 1 - u = (m : Real) / (n : Real) := by
    rw [hMVal]
    dsimp only [u]
    field_simp [hNne]
    <;> ring
  have hLogRatio : Real.log (1 - u) = Real.log (m : Real) - Real.log (n : Real) := by
    rw [hRatio, Real.log_div (ne_of_gt hM0) hNne]
  have hExact : 2 * (hamiltonianLogPermanentNormalizer m - hamiltonianLogPermanentNormalizer n) -
      (2 * (r : Real) - (r : Real) / (n : Real)) =
      (Real.log (1 - u) + u) +
        2 * (Real.log (Stirling.stirlingSeq m) - Real.log (Stirling.stirlingSeq n)) := by
    rw [hamiltonian_log_permanent_normalizer_stirling m hm,
      hamiltonian_log_permanent_normalizer_stirling n (by omega), hLogRatio, hMVal]
    dsimp only [u]
    ring
  change abs (2 * (hamiltonianLogPermanentNormalizer m - hamiltonianLogPermanentNormalizer n) -
    (2 * (r : Real) - (r : Real) / (n : Real))) <= _
  rw [hExact]
  calc
    _ <= abs (Real.log (1 - u) + u) +
        abs (2 * (Real.log (Stirling.stirlingSeq m) - Real.log (Stirling.stirlingSeq n))) :=
      abs_add_le _ _
    _ = abs (Real.log (1 - u) + u) +
        2 * abs (Real.log (Stirling.stirlingSeq m) - Real.log (Stirling.stirlingSeq n)) := by
      rw [abs_mul, abs_of_pos (by norm_num : (0 : Real) < 2)]
    _ <= 2 * u ^ 2 + 2 * ((r : Real) / (n : Real) ^ 2) :=
      add_le_add (hamiltonian_log_one_sub_linear_budget u hu0 hu)
        (mul_le_mul_of_nonneg_left hVAbs (by norm_num))
    _ = _ := by
      dsimp only [u]
      field_simp [hNne]
      <;> ring

end PrimeFactorOscillations

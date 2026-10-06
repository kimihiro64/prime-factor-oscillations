/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.NumberTheory.Harmonic.Bounds
import PrimeFactorOscillations.Helpers.ModifiedLcmDefect

/-!
# An unconditional explicit bound for the full local remainder

All prime-power defects satisfy u_p < 1/N. The harmonic sum and the
finite prime count give R_N <= (36 + 4 log N)/N, without a PNT input for U_N.
-/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace PrimeFactorOscillations
open Filter Asymptotics

theorem modifiedLcm_prime_reciprocal_sum_le (N : Nat) :
    (Nat.primesLE N).sum (fun p => 1 / (p : Real)) <= 1 + Real.log (N : Real) := by
  have hSubset : Nat.primesLE N <= Finset.Icc 1 N := by
    intro p hp
    exact Finset.mem_Icc.mpr (And.intro (Nat.prime_of_mem_primesLE hp).one_le
      (Nat.le_of_mem_primesLE hp))
  have hSum : (Finset.Icc 1 N).sum (fun p => 1 / (p : Real)) = (harmonic N : Real) := by
    rw [harmonic_eq_sum_Icc, Rat.cast_sum]
    simp only [one_div, Rat.cast_inv, Rat.cast_natCast]
  calc
    _ <= (Finset.Icc 1 N).sum (fun p => 1 / (p : Real)) :=
      Finset.sum_le_sum_of_subset_of_nonneg hSubset (fun p _ _ => by positivity)
    _ = (harmonic N : Real) := hSum
    _ <= _ := harmonic_le_one_add_log N

theorem modifiedLcm_prime_card_le (N : Nat) : (Nat.primesLE N).card <= N := by
  have hSubset : Nat.primesLE N <= Finset.Icc 1 N := by
    intro p hp
    exact Finset.mem_Icc.mpr (And.intro (Nat.prime_of_mem_primesLE hp).one_le
      (Nat.le_of_mem_primesLE hp))
  simpa using Finset.card_le_card hSubset

theorem modifiedLcm_defect_weighted_sum_le (N : Nat) (hN : 0 < N) :
    (Nat.primesLE N).sum (fun p => lcmExponentDefect (modifiedLcm N) p / (p : Real)) <=
      (1 + Real.log (N : Real)) / (N : Real) := by
  have hNPos : (0 : Real) < N := by exact_mod_cast hN
  calc
    _ <= (Nat.primesLE N).sum (fun p => (1 / (N : Real)) / (p : Real)) :=
      Finset.sum_le_sum (fun p hp => div_le_div_of_nonneg_right
        (modifiedLcm_exponentDefect_lt N hN (Nat.prime_of_mem_primesLE hp)).le
        (Nat.cast_nonneg p))
    _ = (1 / (N : Real)) * (Nat.primesLE N).sum (fun p => 1 / (p : Real)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      ring
    _ <= (1 / (N : Real)) * (1 + Real.log (N : Real)) :=
      mul_le_mul_of_nonneg_left (modifiedLcm_prime_reciprocal_sum_le N) (by positivity)
    _ = _ := by ring

theorem modifiedLcm_defect_square_sum_le (N : Nat) (hN : 0 < N) :
    (Nat.primesLE N).sum (fun p => (lcmExponentDefect (modifiedLcm N) p) ^ 2) <=
      1 / (N : Real) := by
  have hNPos : (0 : Real) < N := by exact_mod_cast hN
  have hCard : ((Nat.primesLE N).card : Real) <= N := by
    exact_mod_cast modifiedLcm_prime_card_le N
  calc
    _ <= (Nat.primesLE N).sum (fun _ => (1 / (N : Real)) ^ 2) := by
      apply Finset.sum_le_sum
      intro p hp
      have hU := (modifiedLcm_exponentDefect_lt N hN (Nat.prime_of_mem_primesLE hp)).le
      have hNonneg : 0 <= lcmExponentDefect (modifiedLcm N) p :=
        Real.rpow_nonneg (Nat.cast_nonneg p) _
      nlinarith only [hU, hNonneg]
    _ = ((Nat.primesLE N).card : Real) * (1 / (N : Real)) ^ 2 := by simp
    _ <= (N : Real) * (1 / (N : Real)) ^ 2 :=
      mul_le_mul_of_nonneg_right hCard (sq_nonneg _)
    _ = _ := by field_simp

theorem modifiedLcm_remainder_bound (N : Nat) (hN : 0 < N) :
    0 <= lcmDefectRemainder (modifiedLcm N) /\
      lcmDefectRemainder (modifiedLcm N) <= (36 + 4 * Real.log (N : Real)) / (N : Real) := by
  unfold lcmDefectRemainder
  rw [modifiedLcm_primeFactors]
  refine And.intro ?_ ?_
  . apply add_nonneg
    . apply mul_nonneg (by norm_num)
      apply Finset.sum_nonneg
      intro p hp
      exact div_nonneg (Real.rpow_nonneg (Nat.cast_nonneg p) _) (Nat.cast_nonneg p)
    . apply mul_nonneg (by norm_num)
      exact Finset.sum_nonneg (fun p _ => sq_nonneg _)
  . calc
      _ <= 4 * ((1 + Real.log (N : Real)) / (N : Real)) +
          32 * (1 / (N : Real)) := add_le_add
        (mul_le_mul_of_nonneg_left (modifiedLcm_defect_weighted_sum_le N hN) (by norm_num))
        (mul_le_mul_of_nonneg_left (modifiedLcm_defect_square_sum_le N hN) (by norm_num))
      _ = _ := by ring

theorem tendsto_modifiedLcm_remainder_scaled :
    Tendsto (fun N : Nat => lcmDefectRemainder (modifiedLcm N) *
      Real.sqrt (N : Real) * Real.log (N : Real)) atTop (nhds (0 : Real)) := by
  have hn : Tendsto (fun N : Nat => (N : Real)) atTop atTop := tendsto_natCast_atTop_atTop
  have hOne : Tendsto (fun N : Nat => Real.log (N : Real) / Real.sqrt (N : Real))
      atTop (nhds (0 : Real)) := by
    have h := (isLittleO_log_rpow_rpow_atTop (1 : Real)
      (by norm_num : (0 : Real) < 1 / 2)).tendsto_div_nhds_zero
    simpa only [Function.comp_def, Real.rpow_one, Real.sqrt_eq_rpow] using h.comp hn
  have hTwo : Tendsto (fun N : Nat => Real.log (N : Real) ^ (2 : Nat) /
      Real.sqrt (N : Real)) atTop (nhds (0 : Real)) := by
    have h := (isLittleO_log_rpow_rpow_atTop (2 : Real)
      (by norm_num : (0 : Real) < 1 / 2)).tendsto_div_nhds_zero
    simpa only [Function.comp_def, Real.rpow_two, Real.sqrt_eq_rpow] using h.comp hn
  have hUpper := (hOne.const_mul 36).add (hTwo.const_mul 4)
  simp only [mul_zero, add_zero] at hUpper
  apply squeeze_zero'
    (by
      filter_upwards [eventually_ge_atTop (1 : Nat)] with N hN
      exact mul_nonneg
        (mul_nonneg (modifiedLcm_remainder_bound N (by omega)).1 (Real.sqrt_nonneg _))
        (Real.log_nonneg (by exact_mod_cast hN))) ?_ hUpper
  filter_upwards [eventually_ge_atTop (1 : Nat)] with N hN
  have hNPos : (0 : Real) < N := by exact_mod_cast (show 0 < N by omega)
  have hLog : 0 <= Real.log (N : Real) := Real.log_nonneg (by exact_mod_cast hN)
  have h := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (modifiedLcm_remainder_bound N (by omega)).2
      (Real.sqrt_nonneg (N : Real))) hLog
  have hRatio : Real.sqrt (N : Real) / (N : Real) = 1 / Real.sqrt (N : Real) := by
    field_simp [hNPos.ne', (Real.sqrt_pos.mpr hNPos).ne']
    <;> nlinarith only [Real.sq_sqrt hNPos.le]
  apply h.trans_eq
  calc
    _ = (36 + 4 * Real.log (N : Real)) *
        (Real.sqrt (N : Real) / (N : Real)) * Real.log (N : Real) := by ring
    _ = _ := by rw [hRatio]; ring

end PrimeFactorOscillations

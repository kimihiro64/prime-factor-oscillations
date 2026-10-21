/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Proof.PrimeClassDeletion.GreedyPrimeAsymptotics

/-!
# Prime-count density of the actual capped greedy class

The existing Chebyshev count remainder proves the all-prime normalization.
The retained theta mass is a lower bound for the normalized retained count,
and the actual all-prime count is an upper bound. Both limits are one.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.PrimeClassDeletion

open Filter
open PrimeFactorUnimodality
open PrimeFactorOscillations.PrimeClassSampling

theorem primeClassPrefix_univ_card_eq_primeCounting (X : Nat) :
    (primeClassPrefix Set.univ X).card = Nat.primeCounting X := by
  classical
  have heq : classPrimeIndices Set.univ = fun _ : Nat => True := rfl
  rw [primeClassPrefix_card_eq_selectionCount, heq, selectionCount_eq_card_selectionPrefix]
  simp only [selectionPrefix, Finset.filter_true, Finset.card_range]
  rfl

theorem primeClassPrefix_univ_count_normalized_tendsto_one :
    Tendsto (fun X : Nat =>
      ((primeClassPrefix Set.univ X).card : Real) * Real.log (X : Real) / (X : Real))
      atTop (nhds 1) := by
  choose C hC using Asymptotics.isBigO_iff'.mp
    Chebyshev.primeCounting_sub_theta_div_log_isBigO
  have hn : Tendsto (fun X : Nat => (X : Real)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hl : Tendsto (fun X : Nat => Real.log (X : Real)) atTop atTop :=
    Real.tendsto_log_atTop.comp hn
  have he : Tendsto (fun X : Nat =>
      (Nat.primeCounting X : Real) * Real.log (X : Real) / (X : Real) -
        primeClassTheta Set.univ X / (X : Real)) atTop (nhds 0) := by
    apply squeeze_zero_norm' (a := fun X : Nat => C / Real.log (X : Real))
      ?_ (hl.const_div_atTop C)
    filter_upwards [hn.eventually hC.2, eventually_ge_atTop (2 : Nat)] with X hb hX
    have hx : (2 : Real) <= (X : Real) := by exact_mod_cast hX
    have hx0 : (0 : Real) < (X : Real) := by linarith only [hx]
    have hlx : 0 < Real.log (X : Real) := Real.log_pos (by linarith only [hx])
    simp only [Nat.floor_natCast, Real.norm_eq_abs, abs_div, abs_of_pos hx0,
      abs_pow, abs_of_pos hlx, mul_div] at hb
    have hid :
        (Nat.primeCounting X : Real) * Real.log (X : Real) / (X : Real) -
          primeClassTheta Set.univ X / (X : Real) =
        ((Nat.primeCounting X : Real) - Chebyshev.theta (X : Real) / Real.log (X : Real)) *
          (Real.log (X : Real) / (X : Real)) := by
      rw [primeClassTheta_univ_eq_chebyshev]
      field_simp [hx0.ne', hlx.ne']
    rw [Real.norm_eq_abs, hid, abs_mul, abs_of_pos (div_pos hlx hx0)]
    calc
      abs ((Nat.primeCounting X : Real) -
          Chebyshev.theta (X : Real) / Real.log (X : Real)) *
          (Real.log (X : Real) / (X : Real)) <=
        (C * (X : Real) / Real.log (X : Real) ^ 2) *
          (Real.log (X : Real) / (X : Real)) :=
        mul_le_mul_of_nonneg_right hb (div_nonneg hlx.le hx0.le)
      _ = _ := by field_simp [hx0.ne', hlx.ne']
  have ht := he.add primeClassTheta_univ_div_tendsto_one
  simpa only [primeClassPrefix_univ_card_eq_primeCounting, sub_add_cancel, zero_add] using ht

theorem primeClassTheta_le_card_mul_log (P : Set Nat) (X : Nat) :
    primeClassTheta P X <= ((primeClassPrefix P X).card : Real) * Real.log (X : Real) := by
  classical
  calc
    primeClassTheta P X <= (primeClassPrefix P X).sum (fun _ => Real.log (X : Real)) := by
      apply Finset.sum_le_sum
      intro p hp
      have hm := Finset.mem_filter.mp hp
      have hb := Finset.mem_Icc.mp hm.1
      exact Real.log_le_log (Nat.cast_pos.mpr hm.2.1.pos) (Nat.cast_le.mpr hb.2)
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]

theorem primeClassPrefix_card_le_univ (P : Set Nat) (X : Nat) :
    (primeClassPrefix P X).card <= (primeClassPrefix Set.univ X).card := by
  classical
  apply Finset.card_le_card
  intro p hp
  simp only [primeClassPrefix, Finset.mem_filter, Finset.mem_Icc] at hp
  simpa only [primeClassPrefix, Finset.mem_filter, Finset.mem_Icc, Set.mem_univ, and_true]
    using And.intro hp.1 hp.2.1

theorem greedyPrimeClass_count_normalized_tendsto_one :
    Tendsto (fun X : Nat =>
      ((primeClassPrefix greedyPrimeClass X).card : Real) *
        Real.log (X : Real) / (X : Real)) atTop (nhds 1) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    greedyPrimeClass_theta_div_tendsto_one
    primeClassPrefix_univ_count_normalized_tendsto_one
  case hgf =>
    apply Filter.Eventually.of_forall
    intro X
    exact div_le_div_of_nonneg_right (primeClassTheta_le_card_mul_log greedyPrimeClass X)
      (Nat.cast_nonneg X)
  case hfh =>
    filter_upwards [eventually_ge_atTop (2 : Nat)] with X hX
    have hx : (2 : Real) <= (X : Real) := by exact_mod_cast hX
    have hl : 0 <= Real.log (X : Real) := Real.log_nonneg (by linarith only [hx])
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg X)
    exact mul_le_mul_of_nonneg_right
      (Nat.cast_le.mpr (primeClassPrefix_card_le_univ greedyPrimeClass X)) hl

theorem greedyPrimeClass_count_ratio_tendsto_one :
    Tendsto (fun X : Nat =>
      ((primeClassPrefix greedyPrimeClass X).card : Real) /
        ((X : Real) / Real.log (X : Real))) atTop (nhds 1) := by
  apply greedyPrimeClass_count_normalized_tendsto_one.congr'
  filter_upwards [eventually_ge_atTop (2 : Nat)] with X hX
  have hx : (2 : Real) <= (X : Real) := by exact_mod_cast hX
  have hx0 : (0 : Real) < (X : Real) := by linarith only [hx]
  have hlx : 0 < Real.log (X : Real) := Real.log_pos (by linarith only [hx])
  field_simp [hx0.ne', hlx.ne']

theorem greedyDeletedPrimeClass_count_normalized_tendsto_zero :
    Tendsto (fun X : Nat =>
      ((primeClassPrefix greedyDeletedPrimeClass X).card : Real) *
        Real.log (X : Real) / (X : Real)) atTop (nhds 0) := by
  have h : Tendsto (fun X : Nat =>
      ((primeClassPrefix Set.univ X).card : Real) * Real.log (X : Real) / (X : Real) -
        ((primeClassPrefix greedyPrimeClass X).card : Real) *
          Real.log (X : Real) / (X : Real)) atTop (nhds 0) := by
    simpa only [sub_self] using
      primeClassPrefix_univ_count_normalized_tendsto_one.sub
        greedyPrimeClass_count_normalized_tendsto_one
  apply h.congr'
  apply Filter.Eventually.of_forall
  intro X
  have hle : (primeClassPrefix greedyPrimeClass X).card <= primeCutoffLength X := by
    rw [greedyPrimeClass_count_eq]
    exact selectionCount_le_length _ _
  have hpart : (primeClassPrefix greedyPrimeClass X).card +
      (primeClassPrefix greedyDeletedPrimeClass X).card = primeCutoffLength X := by
    rw [greedyDeletedPrimeClass_count_eq_sub]
    omega
  have hreal : ((primeClassPrefix greedyPrimeClass X).card : Real) +
      ((primeClassPrefix greedyDeletedPrimeClass X).card : Real) =
        ((primeClassPrefix Set.univ X).card : Real) := by
    rw [primeClassPrefix_univ_card_eq_primeCounting]
    exact_mod_cast hpart
  have heq : ((primeClassPrefix greedyDeletedPrimeClass X).card : Real) =
      ((primeClassPrefix Set.univ X).card : Real) -
        ((primeClassPrefix greedyPrimeClass X).card : Real) := by linarith only [hreal]
  dsimp only
  rw [heq, sub_mul, sub_div]

end PrimeFactorOscillations.PrimeClassDeletion

/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.PrimeClassSamplingLimit

/-!
# Normalization of the limiting count-profile law

Every sample uses exactly the integers one through N. Its complete count
distribution has mass one. The infinite coefficient error estimate gives
coefficient convergence, positivity, summability and mass one for the limit.
No normalization or probability law is assumed.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.PrimeClassSampling

open Filter
open PrimeFactorOscillations.PrimeClassDecoder

theorem primeDivisorCount_le (P : Set Nat) (m : Nat) :
    primeDivisorCount P m <= m := by
  classical
  unfold primeDivisorCount
  apply (Finset.card_filter_le _ _).trans
  simp only [Nat.card_Icc]
  omega

theorem sampleCount_eq_zero_of_lt (P : Set Nat) (N k : Nat) (hk : N < k) :
    sampleCount P N k = 0 := by
  classical
  unfold sampleCount
  apply Finset.card_eq_zero.mpr
  apply Finset.ext
  intro m
  constructor
  case mp =>
    intro hm
    have hd := Finset.mem_filter.mp hm
    have hmN := (Finset.mem_Icc.mp hd.1).2
    have hcnt := primeDivisorCount_le P m
    have hfalse : False := by omega
    exact hfalse.elim
  case mpr =>
    intro hm
    simp at hm

theorem sampleCount_sum (P : Set Nat) (N : Nat) :
    (Finset.range (N + 1)).sum (sampleCount P N) = N := by
  classical
  calc
    (Finset.range (N + 1)).sum (sampleCount P N) =
        (Finset.range (N + 1)).sum (fun k =>
          (Finset.Icc 1 N).sum (fun m =>
            if primeDivisorCount P m = k then 1 else 0)) := by
      apply Finset.sum_congr rfl
      intro k hk
      exact (Finset.sum_boole (fun m => primeDivisorCount P m = k)
        (Finset.Icc 1 N)).symm
    _ = (Finset.Icc 1 N).sum (fun m =>
        (Finset.range (N + 1)).sum (fun k =>
          if primeDivisorCount P m = k then 1 else 0)) := Finset.sum_comm
    _ = (Finset.Icc 1 N).sum (fun m => 1) := by
      apply Finset.sum_congr rfl
      intro m hm
      have hmN := (Finset.mem_Icc.mp hm).2
      have hcnt : primeDivisorCount P m < N + 1 :=
        Nat.lt_succ_of_le ((primeDivisorCount_le P m).trans hmN)
      simp [Finset.mem_range, hcnt]
    _ = N := by simp

theorem actualSample_probability_summable (P : Set Nat) (N : Nat) :
    Summable (fun k => (sampleCount P N k : Real) / (N : Real)) := by
  apply summable_of_ne_finset_zero (s := Finset.range (N + 1))
  intro k hk
  have hNk : N < k := by
    have hnot : Not (k < N + 1) := fun h => hk (Finset.mem_range.mpr h)
    omega
  rw [sampleCount_eq_zero_of_lt P N k hNk, Nat.cast_zero, zero_div]

theorem actualSample_hasSum_one (P : Set Nat) (N : Nat) (hN : 0 < N) :
    HasSum (fun k => (sampleCount P N k : Real) / (N : Real)) 1 := by
  have hfinite : HasSum (fun k => (sampleCount P N k : Real) / (N : Real))
      ((Finset.range (N + 1)).sum (fun k =>
        (sampleCount P N k : Real) / (N : Real))) := hasSum_sum_of_ne_finset_zero
    (f := fun k => (sampleCount P N k : Real) / (N : Real))
    (s := Finset.range (N + 1)) (by
      intro k hk
      have hNk : N < k := by
        have hnot : Not (k < N + 1) := fun h => hk (Finset.mem_range.mpr h)
        omega
      rw [sampleCount_eq_zero_of_lt P N k hNk, Nat.cast_zero, zero_div])
  have hmass :
      (Finset.range (N + 1)).sum (fun k =>
        (sampleCount P N k : Real) / (N : Real)) = 1 := by
    simp only [div_eq_mul_inv]
    rw [<- Finset.sum_mul, <- Nat.cast_sum, sampleCount_sum]
    change (N : Real) / (N : Real) = 1
    exact div_self (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hN))
  rw [hmass] at hfinite
  exact hfinite

theorem actualSample_coefficient_tendsto
    (P : Set Nat) (sigma : Real) (hs0 : 0 <= sigma) (hs1 : sigma < 1)
    (hsum : Summable (classPowerWeight P sigma)) (k : Nat) :
    Tendsto (fun N : Nat => (sampleCount P N k : Real) / (N : Real))
      atTop (nhds (limitingCoefficient P k)) := by
  apply tendsto_iff_dist_tendsto_zero.mpr
  have hbound : Filter.Eventually (fun N : Nat =>
      abs ((sampleCount P N k : Real) / (N : Real) - limitingCoefficient P k) <=
        (N : Real) ^ (sigma - 1) * Real.exp (2 * tsum (classPowerWeight P sigma)))
      atTop := by
    filter_upwards [eventually_ge_atTop 1] with N hN
    apply le_trans (Finset.single_le_sum (fun j hj => abs_nonneg _)
      (Finset.mem_range.mpr (Nat.lt_succ_self k)))
    exact actualSample_limiting_partial_error_le P N (k + 1) (by omega)
      sigma hs0 hs1 hsum
  simpa only [Real.dist_eq] using squeeze_zero'
    (Filter.Eventually.of_forall (fun N => abs_nonneg _)) hbound
    (samplingBudget_tendsto_zero P sigma hs1)

theorem limitingCoefficient_nonneg
    (P : Set Nat) (sigma : Real) (hs0 : 0 <= sigma) (hs1 : sigma < 1)
    (hsum : Summable (classPowerWeight P sigma)) (k : Nat) :
    0 <= limitingCoefficient P k := by
  apply ge_of_tendsto (actualSample_coefficient_tendsto P sigma hs0 hs1 hsum k)
  exact Filter.Eventually.of_forall
    (fun N => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))

theorem limitingCoefficient_summable
    (P : Set Nat) (sigma : Real) (hs0 : 0 <= sigma) (hs1 : sigma < 1)
    (hsum : Summable (classPowerWeight P sigma)) :
    Summable (limitingCoefficient P) := by
  have hactual := actualSample_probability_summable P 1
  have hdiff := (actualSample_limiting_error_summable
    P 1 (by norm_num) sigma hs0 hs1 hsum).of_abs
  have h := hactual.sub hdiff
  simpa only [sub_sub_cancel] using h

theorem limitingCoefficient_hasSum_one
    (P : Set Nat) (sigma : Real) (hs0 : 0 <= sigma) (hs1 : sigma < 1)
    (hsum : Summable (classPowerWeight P sigma)) :
    HasSum (limitingCoefficient P) 1 := by
  have hbeta := limitingCoefficient_summable P sigma hs0 hs1 hsum
  have hbound : Filter.Eventually (fun N : Nat =>
      abs (1 - tsum (limitingCoefficient P)) <=
        (N : Real) ^ (sigma - 1) * Real.exp (2 * tsum (classPowerWeight P sigma)))
      atTop := by
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hNpos : 0 < N := by omega
    have hsample := actualSample_hasSum_one P N hNpos
    have hdiff := actualSample_limiting_error_summable P N hNpos sigma hs0 hs1 hsum
    have hnorm := norm_tsum_le_tsum_norm
      (f := fun k => (sampleCount P N k : Real) / (N : Real) - limitingCoefficient P k)
      (by simpa only [Real.norm_eq_abs] using hdiff)
    have hsub := hsample.summable.tsum_sub hbeta
    rw [hsub, hsample.tsum_eq] at hnorm
    apply le_trans (by simpa only [Real.norm_eq_abs] using hnorm)
    exact actualSample_limiting_coefficient_l1_error_le P N hNpos sigma hs0 hs1 hsum
  have hzero := ge_of_tendsto (samplingBudget_tendsto_zero P sigma hs1) hbound
  have heq : tsum (limitingCoefficient P) = 1 := by
    have habs : abs (1 - tsum (limitingCoefficient P)) = 0 :=
      le_antisymm hzero (abs_nonneg _)
    exact (sub_eq_zero.mp (abs_eq_zero.mp habs)).symm
  rw [<- heq]
  exact hbeta.hasSum

end PrimeFactorOscillations.PrimeClassSampling

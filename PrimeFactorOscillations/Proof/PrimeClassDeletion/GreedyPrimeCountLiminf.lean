/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.PrimeClassCountingExponent
import PrimeFactorOscillations.Proof.PrimeClassDeletion.GreedyPrimeRHCriterion

/-!
# Logarithmic lower-limit criterion for the actual greedy deleted class

The bounded logarithmic count and the vanishing log(2)/log(n) allowance
identify cofinal power bounds with the literal real-valued lower limit.
The already maintained cofinal RH theorem supplies the RH specialization.
-/

set_option autoImplicit false
set_option Elab.async false

open Filter
open PrimeFactorOscillations.PrimeClassSampling

namespace PrimeFactorOscillations.PrimeClassDeletion

private theorem primeClassLogCount_bounds (P : Set Nat) (n : Nat) :
    And (0 <= primeClassLogCount P n) (primeClassLogCount P n <= 2) := by
  classical
  by_cases hn : 2 <= n
  case pos =>
    have hnR : (2 : Real) <= (n : Real) := by exact_mod_cast hn
    have hnPos : (0 : Real) < (n : Real) := by linarith only [hnR]
    have hLog : 0 < Real.log (n : Real) := Real.log_pos (by linarith only [hnR])
    have hCard : (primeClassPrefix P n).card <= n + 1 := by
      apply le_trans (Finset.card_le_card (show
        primeClassPrefix P n <= Finset.range (n + 1) from by
          intro p hp
          exact Finset.mem_range.mpr
            (Nat.lt_succ_of_le (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).2)))
      exact (Finset.card_range (n + 1)).le
    have hCardR : ((primeClassPrefix P n).card : Real) <= (n : Real) + 1 := by
      exact_mod_cast hCard
    have hPlus : ((primeClassPrefix P n).card : Real) + 1 <= (n : Real) ^ 2 := by
      nlinarith only [hCardR, hnR, sq_nonneg ((n : Real) - 2)]
    have hLogPlus := Real.log_le_log
      (by positivity : (0 : Real) < ((primeClassPrefix P n).card : Real) + 1) hPlus
    rw [Real.log_pow] at hLogPlus
    constructor
    case left =>
      exact div_nonneg (Real.log_nonneg (by
        have h : (0 : Real) <= ((primeClassPrefix P n).card : Real) :=
          Nat.cast_nonneg _
        linarith only [h])) hLog.le
    case right =>
      change Real.log (((primeClassPrefix P n).card : Real) + 1) /
        Real.log (n : Real) <= 2
      calc
        _ <= (2 * Real.log (n : Real)) / Real.log (n : Real) :=
          div_le_div_of_nonneg_right hLogPlus hLog.le
        _ = 2 := by field_simp [hLog.ne']
  case neg =>
    have hCases : Or (n = 0) (n = 1) := by omega
    cases hCases with
    | inl h =>
        subst n
        simp only [primeClassLogCount, Nat.cast_zero, Real.log_zero, div_zero]
        exact And.intro (le_refl 0) (by norm_num)
    | inr h =>
        subst n
        simp only [primeClassLogCount, Nat.cast_one, Real.log_one, div_zero]
        exact And.intro (le_refl 0) (by norm_num)

private theorem primeClassLogCount_liminf_iff_cofinal
    (P : Set Nat) (eta : Real) (hEta : 0 <= eta) :
    Filter.liminf (primeClassLogCount P) atTop <= eta <->
      (forall epsilon : Real, 0 < epsilon -> forall N : Nat,
        Exists fun n : Nat => And (max N 2 <= n)
          (((primeClassPrefix P n).card : Real) <=
            (n : Real) ^ (eta + epsilon))) := by
  have hBound : Filter.IsBoundedUnder (fun a b : Real => b <= a)
      atTop (primeClassLogCount P) :=
    Filter.isBoundedUnder_of_eventually_ge
      (Filter.Eventually.of_forall (fun n => (primeClassLogCount_bounds P n).1))
  have hCobound : Filter.IsCoboundedUnder (fun a b : Real => b <= a)
      atTop (primeClassLogCount P) :=
    Filter.isCoboundedUnder_ge_of_le atTop (fun n => (primeClassLogCount_bounds P n).2)
  constructor
  case mp =>
    intro hLim epsilon he N
    have hFreq : Filter.Frequently (fun n : Nat =>
        primeClassLogCount P n < eta + epsilon) atTop :=
      Filter.frequently_lt_of_liminf_lt hCobound (by linarith only [hLim, he])
    choose n hn using Filter.frequently_atTop.mp hFreq (max N 2)
    apply Exists.intro n
    apply And.intro hn.1
    have hnR : (2 : Real) <= (n : Real) := by
      exact_mod_cast (le_trans (le_max_right N 2) hn.1)
    have hnPos : (0 : Real) < (n : Real) := by linarith only [hnR]
    have hLog : 0 < Real.log (n : Real) := Real.log_pos (by linarith only [hnR])
    have hm := mul_lt_mul_of_pos_right hn.2 hLog
    change (Real.log (((primeClassPrefix P n).card : Real) + 1) /
      Real.log (n : Real)) * Real.log (n : Real) <
        (eta + epsilon) * Real.log (n : Real) at hm
    have hCancel : (Real.log (((primeClassPrefix P n).card : Real) + 1) /
        Real.log (n : Real)) * Real.log (n : Real) =
          Real.log (((primeClassPrefix P n).card : Real) + 1) := by
      field_simp [hLog.ne']
    rw [hCancel] at hm
    have hExp := Real.exp_lt_exp.mpr hm
    rw [Real.exp_log (by positivity :
      (0 : Real) < ((primeClassPrefix P n).card : Real) + 1)] at hExp
    rw [Real.rpow_def_of_pos hnPos]
    have hComm : (eta + epsilon) * Real.log (n : Real) =
      Real.log (n : Real) * (eta + epsilon) := mul_comm _ _
    rw [hComm] at hExp
    linarith only [hExp]
  case mpr =>
    intro hSparse
    apply (Filter.liminf_le_iff hCobound hBound).2
    intro y hy
    let delta : Real := (y - eta) / 2
    let a : Real := eta + delta
    have hd : 0 < delta := by dsimp only [delta]; linarith only [hy]
    have ha : 0 <= a := by dsimp only [a]; linarith only [hEta, hd]
    have hLogTop : Tendsto (fun n : Nat => Real.log (n : Real)) atTop atTop :=
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    have hSmall : Filter.Eventually (fun n : Nat =>
        Real.log (2 : Real) / Real.log (n : Real) < delta) atTop :=
      (hLogTop.const_div_atTop (Real.log (2 : Real))).eventually
        (eventually_lt_nhds hd)
    choose M hM using Filter.eventually_atTop.mp hSmall
    apply Filter.frequently_atTop.mpr
    intro N
    choose n hn using hSparse delta hd (max N M)
    have hN : N <= n := by omega
    have hTwo : 2 <= n := by omega
    have hMn : M <= n := by omega
    have hnR : (2 : Real) <= (n : Real) := by exact_mod_cast hTwo
    have hnPos : (0 : Real) < (n : Real) := by linarith only [hnR]
    have hLog : 0 < Real.log (n : Real) := Real.log_pos (by linarith only [hnR])
    have hPower : 1 <= (n : Real) ^ a :=
      Real.one_le_rpow (by linarith only [hnR]) ha
    have hPlus : ((primeClassPrefix P n).card : Real) + 1 <= 2 * (n : Real) ^ a := by
      have hCount : ((primeClassPrefix P n).card : Real) <= (n : Real) ^ a := hn.2
      linarith only [hCount, hPower]
    have hLogPlus := Real.log_le_log
      (by positivity : (0 : Real) < ((primeClassPrefix P n).card : Real) + 1) hPlus
    rw [Real.log_mul (by norm_num : Not ((2 : Real) = 0))
      (Real.rpow_pos_of_pos hnPos a).ne', Real.log_rpow hnPos a] at hLogPlus
    have hRatio : primeClassLogCount P n <= a +
        Real.log (2 : Real) / Real.log (n : Real) := by
      change Real.log (((primeClassPrefix P n).card : Real) + 1) /
        Real.log (n : Real) <= _
      calc
        _ <= (Real.log (2 : Real) + a * Real.log (n : Real)) /
            Real.log (n : Real) :=
          div_le_div_of_nonneg_right hLogPlus hLog.le
        _ = _ := by field_simp [hLog.ne']; ring
    apply Exists.intro n
    apply And.intro hN
    have hAllowance := hM n hMn
    dsimp only [a, delta] at hRatio hAllowance
    linarith only [hRatio, hAllowance]

theorem greedyDeletedPrimeClass_liminf_le_iff_sparse_power_count
    (eta : Real) (hEta : 0 <= eta) :
    Filter.liminf (primeClassLogCount greedyDeletedPrimeClass) atTop <= eta <->
      (forall epsilon : Real, 0 < epsilon -> forall N : Nat,
        Exists fun n : Nat => And (max N 2 <= n)
          (((primeClassPrefix greedyDeletedPrimeClass n).card : Real) <=
            (n : Real) ^ (eta + epsilon))) :=
  primeClassLogCount_liminf_iff_cofinal greedyDeletedPrimeClass eta hEta

theorem riemannHypothesis_iff_greedyDeletedPrimeClass_log_count_liminf :
    RiemannHypothesis <->
      Filter.liminf (primeClassLogCount greedyDeletedPrimeClass) atTop <= (1 / 2 : Real) := by
  rw [riemannHypothesis_iff_cofinal_greedyDeletedPrimeClass_count]
  exact (greedyDeletedPrimeClass_liminf_le_iff_sparse_power_count
    (1 / 2 : Real) (by norm_num)).symm

end PrimeFactorOscillations.PrimeClassDeletion

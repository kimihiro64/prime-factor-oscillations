/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Proof.PrimeClassDeletion.GreedyPrimeStripCriterion

/-!
# Actual logarithmic greedy deletion-count limit when RH is false

Uniform zero responses give every lower-limit inequality near the actual
zero supremum. The complete strip consumer gives the upper inequalities
below one. The endpoint supremum one uses the finite prefix count directly.
-/

set_option autoImplicit false
set_option Elab.async false

open Filter
open PrimeFactorOscillations.PrimeClassSampling

namespace PrimeFactorOscillations.PrimeClassDeletion

theorem primeClassLogCount_le_one (P : Set Nat) (n : Nat) (hn : 2 <= n) :
    primeClassLogCount P n <= 1 := by
  classical
  have hCard : (primeClassPrefix P n).card <= (Finset.Icc 2 n).card := by
    exact Finset.card_filter_le _ _
  rw [Nat.card_Icc] at hCard
  have hNat : (primeClassPrefix P n).card + 1 <= n := by omega
  have hPlus : ((primeClassPrefix P n).card : Real) + 1 <= (n : Real) := by
    exact_mod_cast hNat
  have hnR : (2 : Real) <= (n : Real) := by exact_mod_cast hn
  have hLog : 0 < Real.log (n : Real) := Real.log_pos (by linarith only [hnR])
  have hLogCount := Real.log_le_log
    (by positivity : (0 : Real) < ((primeClassPrefix P n).card : Real) + 1) hPlus
  change Real.log (((primeClassPrefix P n).card : Real) + 1) / Real.log (n : Real) <= 1
  calc
    _ <= Real.log (n : Real) / Real.log (n : Real) :=
      div_le_div_of_nonneg_right hLogCount hLog.le
    _ = 1 := by field_simp [hLog.ne']

private theorem logCount_le_power_allowance
    (P : Set Nat) {n : Nat} (hn : 2 <= n) {a : Real} (ha : 0 <= a)
    (hCount : ((primeClassPrefix P n).card : Real) <= (n : Real) ^ a) :
    primeClassLogCount P n <= a + Real.log (2 : Real) / Real.log (n : Real) := by
  have hnR : (2 : Real) <= (n : Real) := by exact_mod_cast hn
  have hnPos : (0 : Real) < (n : Real) := by linarith only [hnR]
  have hLog : 0 < Real.log (n : Real) := Real.log_pos (by linarith only [hnR])
  have hPower : 1 <= (n : Real) ^ a :=
    Real.one_le_rpow (by linarith only [hnR]) ha
  have hPlus : ((primeClassPrefix P n).card : Real) + 1 <= 2 * (n : Real) ^ a := by
    linarith only [hCount, hPower]
  have hLogPlus := Real.log_le_log
    (by positivity : (0 : Real) < ((primeClassPrefix P n).card : Real) + 1) hPlus
  rw [Real.log_mul (by norm_num : Not ((2 : Real) = 0))
    (Real.rpow_pos_of_pos hnPos a).ne', Real.log_rpow hnPos a] at hLogPlus
  change Real.log (((primeClassPrefix P n).card : Real) + 1) /
    Real.log (n : Real) <= _
  calc
    _ <= (Real.log (2 : Real) + a * Real.log (n : Real)) / Real.log (n : Real) :=
      div_le_div_of_nonneg_right hLogPlus hLog.le
    _ = _ := by field_simp [hLog.ne']; ring

theorem greedyDeletedPrimeClass_log_count_eventually_gt_of_zero
    (rho : Complex) (hZero : riemannZeta rho = 0)
    (hStrip : And (0 < rho.re) (rho.re < 1)) (hBeta : (1 / 2 : Real) < rho.re)
    (a : Real) (ha : a < rho.re) :
    Filter.Eventually (fun n : Nat =>
      a < primeClassLogCount greedyDeletedPrimeClass n) atTop := by
  let epsilon : Real := (rho.re - a) / 2
  have he : 0 < epsilon := by dsimp only [epsilon]; linarith only [ha]
  choose d hd X0 hLower using
    greedyDeletedPrimeClass_uniform_zero_response rho hZero hStrip hBeta epsilon he
  have hLogTop : Tendsto (fun n : Nat => Real.log (n : Real)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hSmall : Tendsto (fun n : Nat => Real.log d / Real.log (n : Real))
      atTop (nhds 0) := hLogTop.const_div_atTop (Real.log d)
  have hGap : a - (rho.re - epsilon) < 0 := by
    dsimp only [epsilon]
    linarith only [ha]
  have hAllowance : Filter.Eventually (fun n : Nat =>
      a - (rho.re - epsilon) < Real.log d / Real.log (n : Real)) atTop :=
    hSmall.eventually (eventually_gt_nhds hGap)
  filter_upwards [hAllowance, eventually_ge_atTop (max 2 (Nat.ceil X0))] with n hAllow hn
  have hnTwo : 2 <= n := (le_max_left 2 (Nat.ceil X0)).trans hn
  have hnR : (2 : Real) <= (n : Real) := by exact_mod_cast hnTwo
  have hnPos : (0 : Real) < (n : Real) := by linarith only [hnR]
  have hLog : 0 < Real.log (n : Real) := Real.log_pos (by linarith only [hnR])
  have hX : X0 <= (n : Real) :=
    (Nat.le_ceil X0).trans
      (Nat.cast_le.mpr ((le_max_right 2 (Nat.ceil X0)).trans hn))
  have hCount : d * (n : Real) ^ (rho.re - epsilon) <=
      ((primeClassPrefix greedyDeletedPrimeClass n).card : Real) := by
    simpa only [Nat.floor_natCast] using hLower (n : Real) hX
  have hPlus : d * (n : Real) ^ (rho.re - epsilon) <=
      ((primeClassPrefix greedyDeletedPrimeClass n).card : Real) + 1 := by
    linarith only [hCount]
  have hPower : 0 < (n : Real) ^ (rho.re - epsilon) :=
    Real.rpow_pos_of_pos hnPos _
  have hLogCount := Real.log_le_log (mul_pos hd hPower) hPlus
  rw [Real.log_mul hd.ne' hPower.ne',
    Real.log_rpow hnPos (rho.re - epsilon)] at hLogCount
  have hRatio : rho.re - epsilon + Real.log d / Real.log (n : Real) <=
      primeClassLogCount greedyDeletedPrimeClass n := by
    change _ <= Real.log (((primeClassPrefix greedyDeletedPrimeClass n).card : Real) + 1) /
      Real.log (n : Real)
    calc
      _ = (Real.log d + (rho.re - epsilon) * Real.log (n : Real)) /
          Real.log (n : Real) := by field_simp [hLog.ne']; ring
      _ <= _ := div_le_div_of_nonneg_right hLogCount hLog.le
  linarith only [hAllow, hRatio]

theorem greedyDeletedPrimeClass_log_count_tendsto_of_zero_supremum
    (Theta : Real) (hHalf : (1 / 2 : Real) < Theta) (hOne : Theta <= 1)
    (hUpper : forall rho : Complex, riemannZeta rho = 0 ->
      And (0 < rho.re) (rho.re < 1) -> rho.re <= Theta)
    (hNear : forall a : Real, a < Theta -> Exists fun rho : Complex =>
      And (riemannZeta rho = 0)
        (And (And (0 < rho.re) (rho.re < 1)) (a < rho.re))) :
    Tendsto (primeClassLogCount greedyDeletedPrimeClass) atTop (nhds Theta) := by
  apply tendsto_order.mpr
  constructor
  case left =>
    intro a ha
    have hMax : max a (1 / 2 : Real) < Theta :=
      max_lt_iff.mpr (And.intro ha hHalf)
    choose rho hZero hStrip hAbove using hNear (max a (1 / 2 : Real)) hMax
    exact greedyDeletedPrimeClass_log_count_eventually_gt_of_zero rho hZero hStrip
      ((le_max_right a (1 / 2 : Real)).trans_lt hAbove) a
      ((le_max_left a (1 / 2 : Real)).trans_lt hAbove)
  case right =>
    intro b hb
    by_cases hTheta : Theta < 1
    case pos =>
      let epsilon : Real := (b - Theta) / 2
      let a : Real := Theta + epsilon
      have he : 0 < epsilon := by dsimp only [epsilon]; linarith only [hb]
      have ha : 0 <= a := by dsimp only [a]; linarith only [hHalf, he]
      have hab : a < b := by dsimp only [a, epsilon]; linarith only [hb]
      have hNative (p : RiemannXiDivisorZeroIndex) :
          (riemannXiDivisorZeroValue p).re <= Theta := by
        have h := (riemannXi_zero_iff_nontrivial_zeta_zero
          (riemannXiDivisorZeroValue p)).mp (riemannXiDivisorZeroValue_eq_zero p)
        exact hUpper _ h.1 h.2
      have hCount := greedyDeletedPrimeClass_eventually_power_count_of_zero_strip
        Theta hHalf.le hTheta hNative epsilon he
      have hLogTop : Tendsto (fun n : Nat => Real.log (n : Real)) atTop atTop :=
        Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
      have hSmall : Filter.Eventually (fun n : Nat =>
          Real.log (2 : Real) / Real.log (n : Real) < b - a) atTop :=
        (hLogTop.const_div_atTop (Real.log (2 : Real))).eventually
          (eventually_lt_nhds (by linarith only [hab]))
      filter_upwards [hCount, hSmall, eventually_ge_atTop (2 : Nat)] with n hn hAllow hnTwo
      have hLogBound := logCount_le_power_allowance greedyDeletedPrimeClass hnTwo ha hn
      linarith only [hLogBound, hAllow]
    case neg =>
      have hEq : Theta = 1 := le_antisymm hOne (le_of_not_gt hTheta)
      rw [hEq] at hb
      filter_upwards [eventually_ge_atTop (2 : Nat)] with n hn
      exact (primeClassLogCount_le_one greedyDeletedPrimeClass n hn).trans_lt hb

theorem greedyDeletedPrimeClass_log_count_tendsto_zero_supremum_of_not_RH
    (hNotRH : Not RiemannHypothesis) :
    Tendsto (primeClassLogCount greedyDeletedPrimeClass) atTop
      (nhds (sSup (Set.range (fun z : ZetaDistinctZero => z.val.re)))) := by
  classical
  choose rho hZero hRight hOne using
    Robin1984.exists_riemannZeta_zero_re_gt_half_of_not_riemannHypothesis hNotRH
  have hStrip : And (0 < rho.re) (rho.re < 1) :=
    And.intro (by linarith only [hRight]) hOne
  let z0 : ZetaDistinctZero := Subtype.mk rho (And.intro hZero hStrip)
  let S : Set Real := Set.range (fun z : ZetaDistinctZero => z.val.re)
  have hNonempty : Set.Nonempty S :=
    Exists.intro z0.val.re (Set.mem_range.mpr (Exists.intro z0 rfl))
  have hBdd : BddAbove S := by
    apply Exists.intro (1 : Real)
    intro y hy
    choose z hz using hy
    rw [<- hz]
    exact z.property.2.2.le
  have hSupOne : sSup S <= 1 := by
    apply csSup_le hNonempty
    intro y hy
    choose z hz using hy
    rw [<- hz]
    exact z.property.2.2.le
  have hUpper : forall w : Complex, riemannZeta w = 0 ->
      And (0 < w.re) (w.re < 1) -> w.re <= sSup S := by
    intro w hw hs
    apply le_csSup hBdd
    exact Set.mem_range.mpr (Exists.intro (Subtype.mk w (And.intro hw hs)) rfl)
  have hSupHalf : (1 / 2 : Real) < sSup S :=
    hRight.trans_le (hUpper rho hZero hStrip)
  have hNear : forall a : Real, a < sSup S -> Exists fun w : Complex =>
      And (riemannZeta w = 0)
        (And (And (0 < w.re) (w.re < 1)) (a < w.re)) := by
    intro a ha
    by_contra hMissing
    have hAll (z : ZetaDistinctZero) : z.val.re <= a := by
      by_contra hFail
      apply hMissing
      exact Exists.intro z.val
        (And.intro z.property.1 (And.intro z.property.2 (lt_of_not_ge hFail)))
    have hSup : sSup S <= a := by
      apply csSup_le hNonempty
      intro y hy
      choose z hz using hy
      rw [<- hz]
      exact hAll z
    exact (not_le_of_gt ha) hSup
  exact greedyDeletedPrimeClass_log_count_tendsto_of_zero_supremum
    (sSup S) hSupHalf hSupOne hUpper hNear

end PrimeFactorOscillations.PrimeClassDeletion

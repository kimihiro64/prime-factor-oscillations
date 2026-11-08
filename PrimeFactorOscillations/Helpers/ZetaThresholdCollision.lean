/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.ThresholdSeparatedSpectrum
import PrimeFactorOscillations.Helpers.ZetaThresholdOrbitProfile

/-! # Radial collision rigidity for actual zeta orders with central mass retained -/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 5000000

noncomputable section
namespace PrimeFactorOscillations

theorem zeta_selected_collision_linear (W : Finset Complex) (t d g : Real)
    (ht : 0 < t) (hd : And (0 < d) (d < 1)) (hg : 0 <= g)
    (hStrip : forall w, Membership.mem W w -> And (0 < w.re) (w.re < 1))
    (hReflect : forall w, Membership.mem W w -> Membership.mem W (zetaHorizontalReflection w))
    (hMoment : Finset.sum W (fun w => (analyticOrderNatAt riemannZeta w : Real) *
        ((w.re - 1 / 2) ^ 2 / t) ^ 2) =
      Finset.sum W (fun w => (analyticOrderNatAt riemannZeta w : Real) *
        ((w.re - 1 / 2) ^ 2 / t)))
    (hK : 0 < thresholdSelectedMass d W
      (fun w => (analyticOrderNatAt riemannZeta w : Real)) (fun w => (w.re - 1 / 2) ^ 2 / t))
    (hSeparated : thresholdSelectedSeparated d W (analyticOrderNatAt riemannZeta)
      (fun w => (w.re - 1 / 2) ^ 2 / t) g)
    (hSmall :
      let a := fun w : Complex => (analyticOrderNatAt riemannZeta w : Real)
      let y := fun w : Complex => (w.re - 1 / 2) ^ 2 / t
      let N := Finset.sum W a
      let K := thresholdSelectedMass d W a y
      let v := thresholdModelHigh (N - K) K d
      thresholdVarianceBudget d v K
        (thresholdTotalUpper d N K - Finset.sum W (fun w => a w * y w)) <
          2 * (K - 2) * g ^ 2 / K) :
    let a := fun w : Complex => (analyticOrderNatAt riemannZeta w : Real)
    let y := fun w : Complex => (w.re - 1 / 2) ^ 2 / t
    let N := Finset.sum W a
    let K := thresholdSelectedMass d W a y
    let v := thresholdModelHigh (N - K) K d
    exists h : Real, And (thresholdSelectedDirac d W a y h)
      (forall phi : Real -> Real,
        (forall u z : Real, abs (phi u - phi z) <= abs (u - z)) ->
        abs (Finset.sum W (fun w => a w * phi (y w)) -
          thresholdTotalStatistic d v N K phi) <= thresholdSingleCoefficient d v *
            (thresholdTotalUpper d N K - Finset.sum W (fun w => a w * y w))) := by
  classical
  dsimp only
  let a0 := fun w : Complex => (analyticOrderNatAt riemannZeta w : Real)
  let y0 := fun w : Complex => (w.re - 1 / 2) ^ 2 / t
  let K := thresholdSelectedMass d W a0 y0
  choose n a y hy hCarrier hStat using zeta_finite_reflection_profile W t ht hStrip hReflect
  have hI0 : momentRoundIndicator d 0 = 0 := by
    simp [momentRoundIndicator, not_le.mpr hd.1]
  have hFold : forall phi : Real -> Real,
      Finset.sum W (fun w => a0 w * momentRoundIndicator d (y0 w) * phi (y0 w)) =
        Finset.sum Finset.univ (fun i => 2 * (a i : Real) *
          momentRoundIndicator d (y i) * phi (y i)) := by
    intro phi
    simpa only [hI0, zero_mul, mul_zero, add_zero, mul_assoc] using
      hStat (fun z => momentRoundIndicator d z * phi z)
  have hSelected : K = thresholdSelectedMass d Finset.univ
      (fun i => 2 * (a i : Real)) y := by
    have h := hFold (fun _ => (1 : Real))
    change Finset.sum W (fun w => a0 w * momentRoundIndicator d (y0 w)) =
      Finset.sum Finset.univ (fun i => 2 * (a i : Real) * momentRoundIndicator d (y i))
    simpa only [mul_one] using h
  have hMu : thresholdSelectedMean d W a0 y0 =
      thresholdSelectedMean d Finset.univ (fun i => 2 * (a i : Real)) y := by
    unfold thresholdSelectedMean
    change Finset.sum W (fun w => a0 w * momentRoundIndicator d (y0 w) * y0 w) / K = _
    rw [hFold (fun z => z), <- hSelected]
  have hVariance : thresholdSelectedVariance d W a0 y0 =
      thresholdSelectedVariance d Finset.univ (fun i => 2 * (a i : Real)) y := by
    unfold thresholdSelectedVariance
    rw [hMu]
    exact hFold (fun z => (z - thresholdSelectedMean d Finset.univ
      (fun i => 2 * (a i : Real)) y) ^ 2)
  have hSep : thresholdSelectedSeparated d Finset.univ a y g := by
    intro i j _ _ hai haj hci hcj hNe
    choose wi hwi hri haiEq hyi using hCarrier i
    choose wj hwj hrj hajEq hyj using hCarrier j
    have hpi : 0 < analyticOrderNatAt riemannZeta wi := by rw [<- haiEq]; exact hai
    have hpj : 0 < analyticOrderNatAt riemannZeta wj := by rw [<- hajEq]; exact haj
    have hdi : d <= (wi.re - 1 / 2) ^ 2 / t := by rw [<- hyi]; exact hci
    have hdj : d <= (wj.re - 1 / 2) ^ 2 / t := by rw [<- hyj]; exact hcj
    have hDistinct : Not ((wi.re - 1 / 2) ^ 2 / t = (wj.re - 1 / 2) ^ 2 / t) := by
      rw [<- hyi, <- hyj]
      exact hNe
    have h := hSeparated wi wj hwi hwj hpi hpj hdi hdj hDistinct
    simpa only [<- hyi, <- hyj] using h
  let b := fun i => 2 * (a i : Real) * momentRoundIndicator d (y i)
  have hb : forall i, Membership.mem Finset.univ i -> 0 <= b i := by
    intro i _
    apply mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _))
    unfold momentRoundIndicator
    split_ifs <;> norm_num
  have hKRight : 0 < Finset.sum Finset.univ b := by
    change 0 < thresholdSelectedMass d Finset.univ (fun i => 2 * (a i : Real)) y
    rw [<- hSelected]
    exact hK
  choose j hj hp using (Finset.sum_pos_iff_of_nonneg hb).mp hKRight
  have hcj : d <= y j := by
    by_contra hn
    simp [b, momentRoundIndicator, hn] at hp
  have haj : 0 < a j := by
    by_contra hn
    have hz : a j = 0 := Nat.eq_zero_of_not_pos hn
    simp [b, hz] at hp
  have hUpper := finiteWeighted_selected_variance_budget W a0 y0 d hd
    (fun w _ => Nat.cast_nonneg _) hMoment hK
  have hSmallScaled := _root_.mul_lt_mul_of_pos_left hSmall hK
  have hDen : K * (2 * (K - 2) * g ^ 2 / K) = 2 * (K - 2) * g ^ 2 := by
    have hKn : Not (K = 0) := ne_of_gt hK
    field_simp [hKn]
  rw [hDen] at hSmallScaled
  have hUpperScaled := _root_.mul_le_mul_of_nonneg_left hUpper (le_of_lt hK)
  have hSame : forall i, Membership.mem Finset.univ i -> 0 < a i -> d <= y i -> y i = y j := by
    intro i hi hai hci
    by_contra hNe
    have hGap := finiteEven_selected_separation_variance Finset.univ a y d g hg hSep
      j i hj hi haj hai hcj hci hNe
    dsimp only at hGap
    rw [<- hSelected, <- hVariance] at hGap
    exact (not_lt_of_ge (le_trans hGap hUpperScaled)) hSmallScaled
  have hDirac : thresholdSelectedDirac d W a0 y0 (y j) := by
    intro phi
    rw [hFold]
    calc
      _ = Finset.sum Finset.univ (fun i => b i * phi (y j)) := by
        apply Finset.sum_congr rfl
        intro i hi
        change b i * phi (y i) = b i * phi (y j)
        by_cases hCut : d <= y i
        case pos =>
          by_cases hai : 0 < a i
          case pos => rw [hSame i hi hai hCut]
          case neg =>
            have hz : a i = 0 := Nat.eq_zero_of_not_pos hai
            simp [b, hz]
        case neg => simp [b, momentRoundIndicator, hCut]
      _ = _ := by
        rw [<- Finset.sum_mul]
        change thresholdSelectedMass d Finset.univ (fun i => 2 * (a i : Real)) y * phi (y j) =
          K * phi (y j)
        rw [<- hSelected]
  exact Exists.intro (y j) (And.intro hDirac
    (finiteWeighted_single_level_linear W a0 y0 d (y j) hd
      (fun w _ => Nat.cast_nonneg _) hMoment hK hDirac).2.2.2)

end PrimeFactorOscillations

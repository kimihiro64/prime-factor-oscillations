/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.ThresholdRadialPacking
import PrimeFactorOscillations.Helpers.ZetaThresholdOrbitProfile

/-! # All-level radial packing for reflected zeta orders with full central mass -/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 5000000

noncomputable section
namespace PrimeFactorOscillations

theorem zeta_selected_radial_packing (W : Finset Complex) (t d g : Real)
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
      (fun w => (w.re - 1 / 2) ^ 2 / t) g) :
    let a := fun w : Complex => (analyticOrderNatAt riemannZeta w : Real)
    let y := fun w : Complex => (w.re - 1 / 2) ^ 2 / t
    let b := fun w => a w * momentRoundIndicator d (y w)
    let N := Finset.sum W a
    let K := thresholdSelectedMass d W a y
    let r := (thresholdRadialSupport W b y).card
    let v := thresholdModelHigh (N - K) K d
    And (2 * (r : Real) <= K)
      (g ^ 2 * Finset.separatedVarianceFloor r 2 K <=
        thresholdVarianceBudget d v K
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
  let b0 := fun w => a0 w * momentRoundIndicator d (y0 w)
  let b := fun i => 2 * (a i : Real) * momentRoundIndicator d (y i)
  have hb0 : forall w, Membership.mem W w -> 0 <= b0 w := by
    intro w _
    apply mul_nonneg (Nat.cast_nonneg _)
    unfold momentRoundIndicator
    split_ifs <;> norm_num
  have hb : forall i, Membership.mem Finset.univ i -> 0 <= b i := by
    intro i _
    apply mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _))
    unfold momentRoundIndicator
    split_ifs <;> norm_num
  have hSupport := finiteWeighted_radialSupport_eq_of_statistics W Finset.univ
    b0 y0 b y hb0 hb hFold
  have hKRight : 0 < thresholdSelectedMass d Finset.univ
      (fun i => 2 * (a i : Real)) y := by
    rw [<- hSelected]
    exact hK
  have hLower := finiteEven_selected_radial_variance_lower Finset.univ a y d g hg hSep hKRight
  dsimp only at hLower
  change And (2 * ((thresholdRadialSupport Finset.univ b y).card : Real) <=
      thresholdSelectedMass d Finset.univ (fun i => 2 * (a i : Real)) y)
    (g ^ 2 * Finset.separatedVarianceFloor (thresholdRadialSupport Finset.univ b y).card 2
      (thresholdSelectedMass d Finset.univ (fun i => 2 * (a i : Real)) y) <=
        thresholdSelectedVariance d Finset.univ (fun i => 2 * (a i : Real)) y) at hLower
  rw [<- hSupport, <- hSelected, <- hVariance] at hLower
  have hUpper := finiteWeighted_selected_variance_budget W a0 y0 d hd
    (fun w _ => Nat.cast_nonneg _) hMoment hK
  exact And.intro hLower.1 (hLower.2.trans hUpper)

end PrimeFactorOscillations

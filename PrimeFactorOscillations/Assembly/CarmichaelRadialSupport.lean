/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.CarmichaelThresholdTotal
import PrimeFactorOscillations.Helpers.ReflectedRadialCard
import PrimeFactorOscillations.Helpers.ThresholdRadialMinimal
import PrimeFactorOscillations.Helpers.ThresholdTwoLayerInverse

/-! # Actual radial diversity and uniquely reconstructed two-layer geometry -/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 5000000

noncomputable section
namespace PrimeFactorOscillations

def zetaFiniteRadialCoordinate (W : Finset Complex) (w : Complex) : Real :=
  (w.re - 1 / 2) ^ 2 / zetaFiniteHorizontalMomentRatio W

def zetaFiniteSelectedRadialMass (W : Finset Complex) (d : Real) : Real :=
  thresholdSelectedMass d W (fun w => (analyticOrderNatAt riemannZeta w : Real)) (zetaFiniteRadialCoordinate W)

theorem zeta_finite_radial_moments (W : Finset Complex)
    (hCritical : forall w, Membership.mem W w -> And (0 < w.re) (w.re < 1))
    (hN : 0 < zetaFiniteMultiplicityMass W) (hM : 0 < zetaFiniteHorizontalMoment W) :
    And (Finset.sum W (fun w => (analyticOrderNatAt riemannZeta w : Real) * zetaFiniteRadialCoordinate W w) =
      zetaFiniteHorizontalEffectiveMass W)
      (And (Finset.sum W (fun w => (analyticOrderNatAt riemannZeta w : Real) *
          (zetaFiniteRadialCoordinate W w) ^ 2) = zetaFiniteHorizontalEffectiveMass W)
        (And (0 < zetaFiniteHorizontalEffectiveMass W) (0 < zetaFiniteHorizontalMomentRatio W))) := by
  have hBounds := zetaFiniteHorizontalMomentRatio_bounds W hCritical hN hM
  have ht := hBounds.2.1
  have hCenter : Finset.sum W (fun w => (analyticOrderNatAt riemannZeta w : Real) *
      ((w.re - 1 / 2) ^ 2) ^ 2) = zetaFiniteHorizontalMomentRatio W * zetaFiniteHorizontalMoment W := by
    rw [zetaFiniteHorizontalFourthMoment_nested]
    unfold zetaFiniteHorizontalMomentRatio
    field_simp [hM.ne']
  have hEffective : zetaFiniteHorizontalMoment W / zetaFiniteHorizontalMomentRatio W =
      zetaFiniteHorizontalEffectiveMass W := by
    unfold zetaFiniteHorizontalMomentRatio zetaFiniteHorizontalEffectiveMass
    field_simp [hM.ne', hBounds.1.ne']
  have hFirst : Finset.sum W (fun w => (analyticOrderNatAt riemannZeta w : Real) * zetaFiniteRadialCoordinate W w) =
      zetaFiniteHorizontalEffectiveMass W := by
    unfold zetaFiniteRadialCoordinate
    rw [finiteWeighted_div_sum]
    exact hEffective
  have hSecond : Finset.sum W (fun w => (analyticOrderNatAt riemannZeta w : Real) *
      (zetaFiniteRadialCoordinate W w) ^ 2) = zetaFiniteHorizontalEffectiveMass W := by
    unfold zetaFiniteRadialCoordinate
    calc
      _ = Finset.sum W (fun w => (analyticOrderNatAt riemannZeta w : Real) *
          ((w.re - 1 / 2) ^ 2) ^ 2) / (zetaFiniteHorizontalMomentRatio W) ^ 2 := by
        simp only [div_pow]
        exact finiteWeighted_div_sum W (fun w => (analyticOrderNatAt riemannZeta w : Real))
          (fun w => ((w.re - 1 / 2) ^ 2) ^ 2) ((zetaFiniteHorizontalMomentRatio W) ^ 2)
      _ = zetaFiniteHorizontalMoment W / zetaFiniteHorizontalMomentRatio W := by
        rw [hCenter]
        field_simp [ht.ne']
      _ = _ := hEffective
  have hPos : 0 < zetaFiniteHorizontalEffectiveMass W := by rw [<- hEffective]; exact div_pos hM ht
  exact And.intro hFirst (And.intro hSecond (And.intro hPos ht))

theorem zeta_negative_branch_distinct_points (W : Finset Complex) (d : Real)
    (hd : And (0 < d) (d < 1))
    (hCritical : forall w, Membership.mem W w -> And (0 < w.re) (w.re < 1))
    (hReflect : forall w, Membership.mem W w -> Membership.mem W (zetaHorizontalReflection w))
    (hN : 0 < zetaFiniteMultiplicityMass W) (hM : 0 < zetaFiniteHorizontalMoment W)
    (hMK : zetaFiniteHorizontalEffectiveMass W < zetaFiniteSelectedRadialMass W d)
    (hKN : zetaFiniteSelectedRadialMass W d < zetaFiniteMultiplicityMass W) :
    And (5 <= (W.filter (fun w => 0 < analyticOrderNatAt riemannZeta w)).card)
      ((forall w, Membership.mem W w -> 0 < analyticOrderNatAt riemannZeta w -> Not (w.re = 1 / 2)) ->
        6 <= (W.filter (fun w => 0 < analyticOrderNatAt riemannZeta w)).card) := by
  classical
  let a := fun w : Complex => (analyticOrderNatAt riemannZeta w : Real)
  let y := zetaFiniteRadialCoordinate W
  let S := W.filter (fun w => 0 < analyticOrderNatAt riemannZeta w)
  have hNorm := zeta_finite_radial_moments W hCritical hN hM
  have hFirst : Finset.sum W (fun w => a w * y w) = zetaFiniteHorizontalEffectiveMass W := hNorm.1
  have hSecond : Finset.sum W (fun w => a w * (y w) ^ 2) = zetaFiniteHorizontalEffectiveMass W := hNorm.2.1
  have ha : forall w, Membership.mem W w -> 0 <= a w := fun _ _ => Nat.cast_nonneg _
  have hy : forall w, Membership.mem W w -> 0 <= y w :=
    fun w _ => div_nonneg (sq_nonneg (w.re - 1 / 2)) hNorm.2.2.2.le
  choose u v w h using finiteWeighted_three_radii W a y d hd ha hy (hSecond.trans hFirst.symm)
    (by rw [hFirst]; exact hNorm.2.2.1) (by rw [hFirst]; exact hMK) hKN
  have hu := h.1
  have hv := h.2.1
  have hw := h.2.2.1
  have hUV := h.2.2.2
  have hUW : Not (y u = y w) := by intro heq; linarith only [hu.2.2, hw.2.2, heq]
  have hVW : Not (y v = y w) := by intro heq; linarith only [hv.2.2, hw.2.2, heq]
  have hActive : forall p, Membership.mem W p -> 0 < a p -> Membership.mem S p := by
    intro p hp hpa
    have hCast : (0 : Real) < (analyticOrderNatAt riemannZeta p : Real) := hpa
    have hn : 0 < analyticOrderNatAt riemannZeta p := by exact_mod_cast hCast
    exact Finset.mem_filter.mpr (And.intro hp hn)
  have hMirrorActive : forall p, Membership.mem S p -> Membership.mem S (zetaHorizontalReflection p) := by
    intro p hp
    have hm := Finset.mem_filter.mp hp
    apply Finset.mem_filter.mpr
    apply And.intro (hReflect p hm.1)
    rw [zetaOrder_reflection p (hCritical p hm.1)]
    exact hm.2
  have hCoordinate (p : Complex) : y (zetaHorizontalReflection p) = y p := by
    dsimp [y, zetaFiniteRadialCoordinate]
    rw [zetaHorizontalCoord_reflection, neg_sq]
  have hNonfixed (p : Complex) (hp : 0 < y p) : Not (p = zetaHorizontalReflection p) := by
    intro heq
    have hre := congrArg Complex.re heq
    rw [zetaHorizontalReflection_re] at hre
    have hc : p.re = 1 / 2 := by linarith only [hre]
    have hz : y p = 0 := by simp [y, zetaFiniteRadialCoordinate, hc]
    rw [hz] at hp
    exact (lt_irrefl 0) hp
  have hPairU := hNonfixed u (lt_of_lt_of_le hd.1 hu.2.2)
  have hPairV := hNonfixed v (lt_of_lt_of_le hd.1 hv.2.2)
  have hMemU := hActive u hu.1 hu.2.1
  have hMemV := hActive v hv.1 hv.2.1
  have hMemW := hActive w hw.1 hw.2.1
  have hMemJU := hMirrorActive u hMemU
  have hMemJV := hMirrorActive v hMemV
  have hFive := finite_reflected_five_card zetaHorizontalReflection y u v w
    (hCoordinate u) (hCoordinate v) hUV hUW hVW hPairU hPairV
  have hSub5 : forall p, Membership.mem ({u, zetaHorizontalReflection u, v, zetaHorizontalReflection v, w} : Finset Complex) p ->
      Membership.mem S p := by
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with hh | hh | hh | hh | hh <;> subst p <;> assumption
  have hLe5 := Finset.card_le_card hSub5
  rw [hFive] at hLe5
  constructor
  case left => exact hLe5
  case right =>
    intro hNoCentral
    have hPairW : Not (w = zetaHorizontalReflection w) := by
      intro heq
      apply hNoCentral w hw.1 (Finset.mem_filter.mp hMemW).2
      have hre := congrArg Complex.re heq
      rw [zetaHorizontalReflection_re] at hre
      linarith only [hre]
    have hMemJW := hMirrorActive w hMemW
    have hSix := finite_reflected_six_card zetaHorizontalReflection y u v w
      (hCoordinate u) (hCoordinate v) (hCoordinate w) hUV hUW hVW hPairU hPairV hPairW
    have hSub6 : forall p, Membership.mem
        (insert (zetaHorizontalReflection w) ({u, zetaHorizontalReflection u, v, zetaHorizontalReflection v, w} : Finset Complex)) p ->
        Membership.mem S p := by
      intro p hp
      rcases Finset.mem_insert.mp hp with heq | hp
      case inl => subst p; exact hMemJW
      case inr => exact hSub5 p hp
    have hLe6 := Finset.card_le_card hSub6
    rw [hSix] at hLe6
    exact hLe6

theorem zeta_finite_two_layer_inverse (W : Finset Complex) (d u v : Real)
    (hd : And (0 < d) (d < 1))
    (hDomain : And (0 <= u) (And (u < d) (d <= v)))
    (hCritical : forall w, Membership.mem W w -> And (0 < w.re) (w.re < 1))
    (hN : 0 < zetaFiniteMultiplicityMass W) (hM : 0 < zetaFiniteHorizontalMoment W)
    (hKN : zetaFiniteSelectedRadialMass W d < zetaFiniteMultiplicityMass W)
    (hCover : forall w, Membership.mem W w -> 0 < analyticOrderNatAt riemannZeta w ->
      Or (zetaFiniteRadialCoordinate W w = u) (zetaFiniteRadialCoordinate W w = v)) :
    let K := zetaFiniteSelectedRadialMass W d
    And (K <= zetaFiniteHorizontalEffectiveMass W)
      (And (zetaFiniteHorizontalEffectiveMass W < zetaFiniteMultiplicityMass W)
        (And (u = thresholdTwoLow (zetaFiniteMultiplicityMass W) (zetaFiniteHorizontalEffectiveMass W) K)
          (v = thresholdTwoHigh (zetaFiniteMultiplicityMass W) (zetaFiniteHorizontalEffectiveMass W) K))) := by
  let a := fun w : Complex => (analyticOrderNatAt riemannZeta w : Real)
  let y := zetaFiniteRadialCoordinate W
  let K := zetaFiniteSelectedRadialMass W d
  have hNorm := zeta_finite_radial_moments W hCritical hN hM
  have hFirst : Finset.sum W (fun w => a w * y w) = zetaFiniteHorizontalEffectiveMass W := hNorm.1
  have hSecond : Finset.sum W (fun w => a w * (y w) ^ 2) = zetaFiniteHorizontalEffectiveMass W := hNorm.2.1
  have ha : forall w, Membership.mem W w -> 0 <= a w := fun _ _ => Nat.cast_nonneg _
  have hy : forall w, Membership.mem W w -> 0 <= y w :=
    fun w _ => div_nonneg (sq_nonneg (w.re - 1 / 2)) hNorm.2.2.2.le
  have hDomainMass := finiteWeightedThreshold_domain W a y d hd.2 ha hy
    (hSecond.trans hFirst.symm) (by rw [hFirst]; exact hNorm.2.2.1)
  have hK : 0 < K := hDomainMass.1
  have hCoverReal : forall w, Membership.mem W w -> 0 < a w -> Or (y w = u) (y w = v) := by
    intro w hw hp
    have hCast : (0 : Real) < (analyticOrderNatAt riemannZeta w : Real) := hp
    have hn : 0 < analyticOrderNatAt riemannZeta w := by exact_mod_cast hCast
    exact hCover w hw hn
  have hMoments := finiteWeighted_two_layer_moments W a y d u v ha hDomain.2.1 hDomain.2.2 hCoverReal
  have hLayer : thresholdTwoLayer d (zetaFiniteHorizontalEffectiveMass W) (zetaFiniteMultiplicityMass W) K u v :=
    And.intro hDomain (And.intro (hMoments.1.symm.trans hFirst) (hMoments.2.symm.trans hSecond))
  have hBounds := thresholdTwoLayer_bounds d (zetaFiniteHorizontalEffectiveMass W)
    (zetaFiniteMultiplicityMass W) K u v hd hK hKN hLayer
  have hInverse := thresholdTwoLayer_inverse d (zetaFiniteHorizontalEffectiveMass W)
    (zetaFiniteMultiplicityMass W) K u v hK hKN hLayer
  exact And.intro hBounds.2.1 (And.intro hBounds.2.2 hInverse)

end PrimeFactorOscillations

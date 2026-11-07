/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.CarmichaelParityCubic
import PrimeFactorOscillations.Helpers.ThreeLineMomentRatio

/-! # Joint moment geometry and even displaced multiplicity for actual zeta zeros -/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace PrimeFactorOscillations

open Complex Robin1984

def zetaFiniteHorizontalMomentRatio (W : Finset Complex) : Real :=
  zetaFiniteHorizontalFourthMoment W / zetaFiniteHorizontalMoment W

def zetaFiniteHorizontalEffectiveMass (W : Finset Complex) : Real :=
  (zetaFiniteHorizontalMoment W) ^ 2 / zetaFiniteHorizontalFourthMoment W

def zetaHorizontalThresholdSet (W : Finset Complex) (ratio : Real) : Finset Complex := by
  classical
  exact W.filter (fun w => 1 / 2 <= (w.re - 1 / 2) ^ 2 / ratio)

def zetaHorizontalThresholdOrder (W : Finset Complex) (ratio : Real) : Nat :=
  zetaFiniteTotalOrder (zetaHorizontalThresholdSet W ratio)

theorem zetaFiniteHorizontalFourthMoment_nested (W : Finset Complex) :
    Finset.sum W (fun w => (analyticOrderNatAt riemannZeta w : Real) *
      ((w.re - 1 / 2) ^ 2) ^ 2) = zetaFiniteHorizontalFourthMoment W := by
  unfold zetaFiniteHorizontalFourthMoment
  apply Finset.sum_congr rfl
  intro w _
  ring

theorem zeta_horizontal_square_bounds (w : Complex) (hw : And (0 < w.re) (w.re < 1)) :
    And (0 <= (w.re - 1 / 2) ^ 2) ((w.re - 1 / 2) ^ 2 <= 1 / 4) := by
  have hProduct := mul_pos hw.1 (sub_pos.mpr hw.2)
  exact And.intro (sq_nonneg _) (by nlinarith)

theorem zetaFiniteHorizontalMomentRatio_bounds (W : Finset Complex)
    (hCritical : forall w, Membership.mem W w -> And (0 < w.re) (w.re < 1))
    (hN : 0 < zetaFiniteMultiplicityMass W) (hM : 0 < zetaFiniteHorizontalMoment W) :
    And (0 < zetaFiniteHorizontalFourthMoment W)
      (And (0 < zetaFiniteHorizontalMomentRatio W) (zetaFiniteHorizontalMomentRatio W <= 1 / 4)) := by
  have h := threeLineMomentRatio_mean_bounds W
    (fun w => (analyticOrderNatAt riemannZeta w : Real)) (fun w => (w.re - 1 / 2) ^ 2)
    (fun _ _ => Nat.cast_nonneg _) (fun w hw => zeta_horizontal_square_bounds w (hCritical w hw)) hN hM
  rw [zetaFiniteHorizontalFourthMoment_nested] at h
  exact h

theorem zetaHorizontalThresholdSet_mem (W : Finset Complex) (ratio : Real) (w : Complex) :
    Membership.mem (zetaHorizontalThresholdSet W ratio) w <->
      And (Membership.mem W w) (1 / 2 <= (w.re - 1 / 2) ^ 2 / ratio) := by
  classical
  exact Finset.mem_filter

theorem zetaHorizontalThresholdOrder_cast (W : Finset Complex) (ratio : Real) :
    (zetaHorizontalThresholdOrder W ratio : Real) =
      Finset.sum W (fun w => (analyticOrderNatAt riemannZeta w : Real) *
        halfRoundIndicator ((w.re - 1 / 2) ^ 2 / ratio)) := by
  classical
  unfold zetaHorizontalThresholdOrder
  rw [zetaFiniteTotalOrder_cast]
  unfold zetaHorizontalThresholdSet
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro w _
  simp only [halfRoundIndicator, mul_ite, mul_one, mul_zero]

theorem zetaHorizontalThresholdSet_reflection (W : Finset Complex) (ratio : Real)
    (hReflect : forall w, Membership.mem W w -> Membership.mem W (zetaHorizontalReflection w)) :
    forall w, Membership.mem (zetaHorizontalThresholdSet W ratio) w ->
      Membership.mem (zetaHorizontalThresholdSet W ratio) (zetaHorizontalReflection w) := by
  intro w hw
  have hMem := (zetaHorizontalThresholdSet_mem W ratio w).mp hw
  apply (zetaHorizontalThresholdSet_mem W ratio (zetaHorizontalReflection w)).mpr
  apply And.intro (hReflect w hMem.1)
  rw [zetaHorizontalCoord_reflection, neg_sq]
  exact hMem.2

theorem zetaHorizontalThresholdOrder_parity (W : Finset Complex) (ratio : Real)
    (hCritical : forall w, Membership.mem W w -> And (0 < w.re) (w.re < 1))
    (hReflect : forall w, Membership.mem W w -> Membership.mem W (zetaHorizontalReflection w)) :
    And (Even (zetaHorizontalThresholdOrder W ratio)) (Not (Odd (zetaHorizontalThresholdOrder W ratio))) := by
  have hCriticalS (w : Complex) (hw : Membership.mem (zetaHorizontalThresholdSet W ratio) w) :
      And (0 < w.re) (w.re < 1) :=
    hCritical w ((zetaHorizontalThresholdSet_mem W ratio w).mp hw).1
  have hReflectS := zetaHorizontalThresholdSet_reflection W ratio hReflect
  have hNotOdd : Not (Odd (zetaHorizontalThresholdOrder W ratio)) := by
    intro hOdd
    choose w hw hRe _hOrder using zeta_odd_total_order_has_critical_point
      (zetaHorizontalThresholdSet W ratio) hCriticalS hReflectS hOdd
    have hThreshold := ((zetaHorizontalThresholdSet_mem W ratio w).mp hw).2
    rw [hRe] at hThreshold
    norm_num at hThreshold
  have hMod : zetaHorizontalThresholdOrder W ratio % 2 = 0 := by
    by_contra h
    have hOne : zetaHorizontalThresholdOrder W ratio % 2 = 1 := by omega
    exact hNotOdd (Nat.odd_iff.mpr hOne)
  have hEven : Even (zetaHorizontalThresholdOrder W ratio) := by
    apply Exists.intro (zetaHorizontalThresholdOrder W ratio / 2)
    omega
  exact And.intro hEven hNotOdd

theorem zeta_finite_horizontal_profile_upper (height : Real) (hHeight : 2 <= abs height)
    (W : Finset Complex)
    (hCritical : forall w, Membership.mem W w -> And (0 < w.re) (w.re < 1))
    (hSame : forall w, Membership.mem W w -> w.im = height) :
    Finset.sum W (fun w => (analyticOrderNatAt riemannZeta w : Real) *
      threeLineHorizontalProfile ((w.re - 1 / 2) ^ 2)) <=
        threeLineCharge * threeLineMultiplicityBudget height := by
  classical
  let S := xiFiniteMultiplicityUnion W
  have hTransport := zeta_finite_multiplicity_transport W hCritical
    (fun w => threeLineHorizontalProfile ((w.re - 1 / 2) ^ 2))
  have hSameS (p : RiemannXiDivisorZeroIndex) (hp : Membership.mem S p) :
      (riemannXiDivisorZeroValue p).im = height := by
    change Membership.mem (W.biUnion xiFiniteMultiplicityFiber) p at hp
    choose w hw hpf using Finset.mem_biUnion.mp hp
    have hw0 : Not (w = 0) := by
      intro he
      have h := (hCritical w hw).1
      rw [he] at h
      norm_num at h
    rw [(xiFiniteMultiplicityFiber_mem w hw0 p).mp hpf]
    exact hSame w hw
  have hKernel : Finset.sum S (fun p => threeLineHorizontalProfile
      (((riemannXiDivisorZeroValue p).re - 1 / 2) ^ 2)) =
      Finset.sum S (fun p => threeLineKernel ((riemannXiDivisorZeroValue p).re - 1 / 2)
        (height - (riemannXiDivisorZeroValue p).im)) := by
    apply Finset.sum_congr rfl
    intro p hp
    rw [hSameS p hp, sub_self, threeLineKernel_horizontal_profile _ (xi_seven_eighths_centered_strip p)]
  have hFinite := xi_threeLine_finite_mass height xi_seven_eighths_centered_strip S
  rw [<- hKernel] at hFinite
  have hUpper := xi_threeLine_trace_upper height hHeight
  have hUpperEq : (threeLineWeight1 + threeLineWeight2 + threeLineWeight3) / 2 *
      Real.log (abs height) + (threeLineWeight1 + threeLineWeight2 + threeLineWeight3) *
        threeLineHeightConstant + threeLineLipschitzConstant * threeLineRemainderScale =
      threeLineCharge * threeLineMultiplicityBudget height := by
    unfold threeLineMultiplicityBudget threeLineLeadingCoefficient threeLineMultiplicityConstant
    field_simp [threeLineCharge_pos.ne']
    ring
  rw [hUpperEq] at hUpper
  exact hTransport.trans_le (hFinite.trans hUpper)

theorem zeta_finite_moment_ratio_even_bound (height : Real) (hHeight : 2 <= abs height)
    (W : Finset Complex)
    (hCritical : forall w, Membership.mem W w -> And (0 < w.re) (w.re < 1))
    (hSame : forall w, Membership.mem W w -> w.im = height)
    (hReflect : forall w, Membership.mem W w -> Membership.mem W (zetaHorizontalReflection w))
    (hN : 0 < zetaFiniteMultiplicityMass W) (hM : 0 < zetaFiniteHorizontalMoment W) :
    And (0 < zetaFiniteHorizontalFourthMoment W)
      (And (Even (zetaHorizontalThresholdOrder W (zetaFiniteHorizontalMomentRatio W)))
        (And (threeLineMomentRatioCharge (zetaFiniteMultiplicityMass W)
            (zetaFiniteHorizontalMoment W) (zetaFiniteHorizontalFourthMoment W) +
          Finset.sum W (fun w => (analyticOrderNatAt riemannZeta w : Real) * (w.re - 1 / 2) ^ 2 *
            ((w.re - 1 / 2) ^ 2 - zetaFiniteHorizontalMomentRatio W) ^ 2) <=
              threeLineCharge * threeLineMultiplicityBudget height)
          ((zetaFiniteHorizontalMomentRatio W) ^ 3 *
            (zetaFiniteHorizontalEffectiveMass W -
              (zetaHorizontalThresholdOrder W (zetaFiniteHorizontalMomentRatio W) : Real)) ^ 2 <=
              2 * zetaFiniteMultiplicityMass W *
                (threeLineCharge * threeLineMultiplicityBudget height -
                  threeLineMomentRatioCharge (zetaFiniteMultiplicityMass W)
                    (zetaFiniteHorizontalMoment W) (zetaFiniteHorizontalFourthMoment W))))) := by
  have hBounds := zetaFiniteHorizontalMomentRatio_bounds W hCritical hN hM
  have ha : forall w, Membership.mem W w -> 0 <= (analyticOrderNatAt riemannZeta w : Real) :=
    fun _ _ => Nat.cast_nonneg _
  have hx : forall w, Membership.mem W w ->
      And (0 <= (w.re - 1 / 2) ^ 2) ((w.re - 1 / 2) ^ 2 <= 1 / 4) :=
    fun w hw => zeta_horizontal_square_bounds w (hCritical w hw)
  have hCenter : Finset.sum W (fun w => (analyticOrderNatAt riemannZeta w : Real) *
      ((w.re - 1 / 2) ^ 2) ^ 2) = zetaFiniteHorizontalMomentRatio W * zetaFiniteHorizontalMoment W := by
    rw [zetaFiniteHorizontalFourthMoment_nested]
    unfold zetaFiniteHorizontalMomentRatio
    field_simp [hM.ne']
  have hStrong := threeLineMomentRatio_weighted_charge W
    (fun w => (analyticOrderNatAt riemannZeta w : Real)) (fun w => (w.re - 1 / 2) ^ 2)
    (zetaFiniteHorizontalMomentRatio W) ha hx (And.intro (le_of_lt hBounds.2.1) hBounds.2.2) hCenter
  change threeLineMomentRatioCharge (zetaFiniteMultiplicityMass W)
      (zetaFiniteHorizontalMoment W) (zetaFiniteHorizontalFourthMoment W) +
    Finset.sum W (fun w => (analyticOrderNatAt riemannZeta w : Real) * (w.re - 1 / 2) ^ 2 *
      ((w.re - 1 / 2) ^ 2 - zetaFiniteHorizontalMomentRatio W) ^ 2) <= _ at hStrong
  have hRound := threeLineMomentRatio_rounding_charge W
    (fun w => (analyticOrderNatAt riemannZeta w : Real)) (fun w => (w.re - 1 / 2) ^ 2)
    (zetaFiniteHorizontalMomentRatio W) hBounds.2.1 ha hx hBounds.2.2 hN hCenter
  rw [<- zetaHorizontalThresholdOrder_cast W (zetaFiniteHorizontalMomentRatio W)] at hRound
  change (zetaFiniteHorizontalMomentRatio W) ^ 3 *
      (zetaFiniteHorizontalMoment W / zetaFiniteHorizontalMomentRatio W -
        (zetaHorizontalThresholdOrder W (zetaFiniteHorizontalMomentRatio W) : Real)) ^ 2 <=
      2 * zetaFiniteMultiplicityMass W *
        (Finset.sum W (fun w => (analyticOrderNatAt riemannZeta w : Real) *
          threeLineHorizontalProfile ((w.re - 1 / 2) ^ 2)) -
            threeLineMomentRatioCharge (zetaFiniteMultiplicityMass W)
              (zetaFiniteHorizontalMoment W) (zetaFiniteHorizontalFourthMoment W)) at hRound
  have hEffective : zetaFiniteHorizontalMoment W / zetaFiniteHorizontalMomentRatio W =
      zetaFiniteHorizontalEffectiveMass W := by
    unfold zetaFiniteHorizontalMomentRatio zetaFiniteHorizontalEffectiveMass
    field_simp [hM.ne', hBounds.1.ne']
  rw [hEffective] at hRound
  have hUpper := zeta_finite_horizontal_profile_upper height hHeight W hCritical hSame
  have hTransfer := _root_.mul_le_mul_of_nonneg_left
    (sub_le_sub_right hUpper (threeLineMomentRatioCharge (zetaFiniteMultiplicityMass W)
      (zetaFiniteHorizontalMoment W) (zetaFiniteHorizontalFourthMoment W)))
      (show 0 <= 2 * zetaFiniteMultiplicityMass W by linarith)
  have hParity := zetaHorizontalThresholdOrder_parity W (zetaFiniteHorizontalMomentRatio W) hCritical hReflect
  exact And.intro hBounds.1 (And.intro hParity.1 (And.intro (hStrong.trans hUpper) (hRound.trans hTransfer)))

theorem zeta_moment_ratio_odd_effective_gap (height : Real) (hHeight : 2 <= abs height)
    (W : Finset Complex)
    (hCritical : forall w, Membership.mem W w -> And (0 < w.re) (w.re < 1))
    (hSame : forall w, Membership.mem W w -> w.im = height)
    (hReflect : forall w, Membership.mem W w -> Membership.mem W (zetaHorizontalReflection w))
    (hN : 0 < zetaFiniteMultiplicityMass W) (hM : 0 < zetaFiniteHorizontalMoment W)
    (j : Nat) (hOdd : Odd j) (hEffective : zetaFiniteHorizontalEffectiveMass W = (j : Real)) :
    (zetaFiniteHorizontalMomentRatio W) ^ 3 <=
      2 * zetaFiniteMultiplicityMass W *
        (threeLineCharge * threeLineMultiplicityBudget height -
          threeLineMomentRatioCharge (zetaFiniteMultiplicityMass W)
            (zetaFiniteHorizontalMoment W) (zetaFiniteHorizontalFourthMoment W)) := by
  have hMain := zeta_finite_moment_ratio_even_bound height hHeight W hCritical hSame hReflect hN hM
  have hCross := hMain.2.2.2
  have hBounds := zetaFiniteHorizontalMomentRatio_bounds W hCritical hN hM
  let K := zetaHorizontalThresholdOrder W (zetaFiniteHorizontalMomentRatio W)
  have hNotOdd : Not (Odd K) :=
    (zetaHorizontalThresholdOrder_parity W (zetaFiniteHorizontalMomentRatio W) hCritical hReflect).2
  have hNe : Not (j = K) := by
    intro h
    rw [h] at hOdd
    exact hNotOdd hOdd
  have hDistance : 1 <= ((j : Real) - (K : Real)) ^ 2 := by
    rcases lt_or_gt_of_ne hNe with hLT | hGT
    case inl =>
      have hNat : j + 1 <= K := by omega
      have hReal : (j : Real) + 1 <= (K : Real) := by exact_mod_cast hNat
      have hProd := mul_nonneg
        (show 0 <= (K : Real) - (j : Real) - 1 by linarith)
        (show 0 <= (K : Real) - (j : Real) + 1 by linarith)
      nlinarith only [hProd]
    case inr =>
      have hNat : K + 1 <= j := by omega
      have hReal : (K : Real) + 1 <= (j : Real) := by exact_mod_cast hNat
      have hProd := mul_nonneg
        (show 0 <= (j : Real) - (K : Real) - 1 by linarith)
        (show 0 <= (j : Real) - (K : Real) + 1 by linarith)
      nlinarith only [hProd]
  rw [hEffective] at hCross
  have hUnit := _root_.mul_le_mul_of_nonneg_left hDistance
    (pow_nonneg (le_of_lt hBounds.2.1) 3)
  have hUnit' : (zetaFiniteHorizontalMomentRatio W) ^ 3 <=
      (zetaFiniteHorizontalMomentRatio W) ^ 3 * ((j : Real) - (K : Real)) ^ 2 := by
    simpa only [mul_one] using hUnit
  exact hUnit'.trans hCross

theorem zetaFiniteHorizontalMoments_feasible (W : Finset Complex)
    (hN : 0 < zetaFiniteMultiplicityMass W) :
    (zetaFiniteHorizontalMoment W) ^ 2 <=
      zetaFiniteMultiplicityMass W * zetaFiniteHorizontalFourthMoment W := by
  have h := finiteWeightedSquareSum_le W
    (fun w => (analyticOrderNatAt riemannZeta w : Real)) (fun w => (w.re - 1 / 2) ^ 2)
    (fun _ _ => Nat.cast_nonneg _) hN
  rw [zetaFiniteHorizontalFourthMoment_nested] at h
  exact h

theorem zetaFiniteHorizontalMomentRatio_strip (W : Finset Complex)
    (hCritical : forall w, Membership.mem W w -> And (0 < w.re) (w.re < 1))
    (hM : 0 < zetaFiniteHorizontalMoment W) : zetaFiniteHorizontalMomentRatio W <= 9 / 64 := by
  let S := xiFiniteMultiplicityUnion W
  let x : RiemannXiDivisorZeroIndex -> Real := fun p =>
    ((riemannXiDivisorZeroValue p).re - 1 / 2) ^ 2
  have hMoment := zeta_finite_multiplicity_transport W hCritical (fun w => (w.re - 1 / 2) ^ 2)
  change zetaFiniteHorizontalMoment W = Finset.sum S x at hMoment
  have hFourth := zeta_finite_multiplicity_transport W hCritical (fun w => (w.re - 1 / 2) ^ 4)
  have hFourthS : Finset.sum S (fun p => ((riemannXiDivisorZeroValue p).re - 1 / 2) ^ 4) =
      Finset.sum S (fun p => (x p) ^ 2) := by
    apply Finset.sum_congr rfl
    intro p _
    dsimp only [x]
    ring
  rw [hFourthS] at hFourth
  change zetaFiniteHorizontalFourthMoment W = Finset.sum S (fun p => (x p) ^ 2) at hFourth
  have hx (p : RiemannXiDivisorZeroIndex) : And (0 <= x p) (x p <= 9 / 64) := by
    have hu := abs_le.mp (xi_seven_eighths_centered_strip p)
    have hp := mul_nonneg (sub_nonneg.mpr hu.2)
      (show 0 <= ((riemannXiDivisorZeroValue p).re - 1 / 2) + 3 / 8 by linarith [hu.1])
    exact And.intro (sq_nonneg _) (by dsimp only [x]; nlinarith)
  have hQMax : Finset.sum S (fun p => (x p) ^ 2) <= (9 / 64) * Finset.sum S x := by
    calc
      _ <= Finset.sum S (fun p => (9 / 64 : Real) * x p) := by
        apply Finset.sum_le_sum
        intro p _
        have h := mul_nonneg (hx p).1 (sub_nonneg.mpr (hx p).2)
        nlinarith only [h]
      _ = _ := by rw [<- Finset.mul_sum]
  rw [<- hMoment, <- hFourth] at hQMax
  unfold zetaFiniteHorizontalMomentRatio
  apply (_root_.mul_le_mul_iff_of_pos_left hM).mp
  have hBalance : zetaFiniteHorizontalMoment W *
      (zetaFiniteHorizontalFourthMoment W / zetaFiniteHorizontalMoment W) =
        zetaFiniteHorizontalFourthMoment W := by field_simp [hM.ne']
  rw [hBalance]
  nlinarith

theorem zeta_odd_horizontal_moments_feasible (W : Finset Complex)
    (hCritical : forall w, Membership.mem W w -> And (0 < w.re) (w.re < 1))
    (hReflect : forall w, Membership.mem W w -> Membership.mem W (zetaHorizontalReflection w))
    (hOdd : Odd (zetaFiniteTotalOrder W)) (hN : 1 < zetaFiniteMultiplicityMass W) :
    (zetaFiniteHorizontalMoment W) ^ 2 <=
      (zetaFiniteMultiplicityMass W - 1) * zetaFiniteHorizontalFourthMoment W := by
  classical
  let S := xiFiniteMultiplicityUnion W
  let x : RiemannXiDivisorZeroIndex -> Real := fun p =>
    ((riemannXiDivisorZeroValue p).re - 1 / 2) ^ 2
  choose a ha hZero using zeta_odd_total_order_has_central_index W hCritical hReflect hOdd
  let R := S.erase a
  have hCardS : (S.card : Real) = zetaFiniteMultiplicityMass W := by
    rw [xiFiniteMultiplicityUnion_card_eq_totalOrder W hCritical, zetaFiniteTotalOrder_eq_mass]
  have hCardR : (R.card : Real) = zetaFiniteMultiplicityMass W - 1 := by
    have h := Finset.card_erase_add_one ha
    change R.card + 1 = S.card at h
    have hr : (R.card : Real) + 1 = (S.card : Real) := by exact_mod_cast h
    linarith
  have hMoment := zeta_finite_multiplicity_transport W hCritical (fun w => (w.re - 1 / 2) ^ 2)
  change zetaFiniteHorizontalMoment W = Finset.sum S x at hMoment
  have hFourth := zeta_finite_multiplicity_transport W hCritical (fun w => (w.re - 1 / 2) ^ 4)
  have hFourthS : Finset.sum S (fun p => ((riemannXiDivisorZeroValue p).re - 1 / 2) ^ 4) =
      Finset.sum S (fun p => (x p) ^ 2) := by
    apply Finset.sum_congr rfl
    intro p _
    dsimp only [x]
    ring
  rw [hFourthS] at hFourth
  change zetaFiniteHorizontalFourthMoment W = Finset.sum S (fun p => (x p) ^ 2) at hFourth
  have hxa : x a = 0 := hZero
  have hEraseM := Finset.sum_erase_add S x ha
  rw [hxa, add_zero] at hEraseM
  have hMR : Finset.sum R x = zetaFiniteHorizontalMoment W := hEraseM.trans hMoment.symm
  have hEraseQ := Finset.sum_erase_add S (fun p => (x p) ^ 2) ha
  rw [hxa, zero_pow (by decide : Not ((2 : Nat) = 0)), add_zero] at hEraseQ
  have hQR : Finset.sum R (fun p => (x p) ^ 2) = zetaFiniteHorizontalFourthMoment W :=
    hEraseQ.trans hFourth.symm
  have hRC : Finset.sum R (fun _ => (1 : Real)) = zetaFiniteMultiplicityMass W - 1 := by
    simpa only [Finset.sum_const, nsmul_eq_mul, mul_one] using hCardR
  have h := finiteWeightedSquareSum_le R (fun _ => (1 : Real)) x (by intro _ _; norm_num)
    (by rw [hRC]; linarith)
  simp only [one_mul] at h
  rw [hRC, hMR, hQR] at h
  exact h

theorem zeta_moment_ratio_dominates_full (W : Finset Complex)
    (hCritical : forall w, Membership.mem W w -> And (0 < w.re) (w.re < 1))
    (hN : 0 < zetaFiniteMultiplicityMass W) (hM : 0 < zetaFiniteHorizontalMoment W) :
    And (zetaFiniteMultiplicityMass W * threeLineHorizontalProfile (zetaFiniteHorizontalMean W) +
      threeLineHorizontalVarianceCoefficient * zetaFiniteHorizontalVariance W (zetaFiniteHorizontalMean W) <=
        threeLineMomentRatioCharge (zetaFiniteMultiplicityMass W)
          (zetaFiniteHorizontalMoment W) (zetaFiniteHorizontalFourthMoment W))
      ((zetaFiniteHorizontalMoment W) ^ 2 < zetaFiniteMultiplicityMass W * zetaFiniteHorizontalFourthMoment W ->
        zetaFiniteMultiplicityMass W * threeLineHorizontalProfile (zetaFiniteHorizontalMean W) +
          threeLineHorizontalVarianceCoefficient * zetaFiniteHorizontalVariance W (zetaFiniteHorizontalMean W) <
            threeLineMomentRatioCharge (zetaFiniteMultiplicityMass W)
              (zetaFiniteHorizontalMoment W) (zetaFiniteHorizontalFourthMoment W)) := by
  have h := threeLineMomentRatio_residual_comparison (zetaFiniteMultiplicityMass W)
    (zetaFiniteMultiplicityMass W) (zetaFiniteHorizontalMoment W) (zetaFiniteHorizontalFourthMoment W)
    hN hM (zetaFiniteHorizontalMoments_feasible W hN) (zetaFiniteHorizontalMomentRatio_strip W hCritical hM)
  constructor
  case left =>
    rw [zeta_horizontal_full_charge_residual_identity W hN]
    simpa only [sub_self, zero_mul, add_zero, zetaFiniteHorizontalMean] using h.1
  case right =>
    intro hStrict
    rw [zeta_horizontal_full_charge_residual_identity W hN]
    simpa only [sub_self, zero_mul, add_zero, zetaFiniteHorizontalMean] using h.2 hStrict

theorem zeta_moment_ratio_dominates_odd (W : Finset Complex)
    (hCritical : forall w, Membership.mem W w -> And (0 < w.re) (w.re < 1))
    (hReflect : forall w, Membership.mem W w -> Membership.mem W (zetaHorizontalReflection w))
    (hOdd : Odd (zetaFiniteTotalOrder W)) (hN : 1 < zetaFiniteMultiplicityMass W)
    (hM : 0 < zetaFiniteHorizontalMoment W) :
    And (threeLineHorizontalVarianceCoefficient * zetaFiniteHorizontalFourthMoment W + threeLineCharge +
      (zetaFiniteMultiplicityMass W - 1) * threeLineHorizontalResidualProfile
        (zetaFiniteHorizontalMoment W / (zetaFiniteMultiplicityMass W - 1)) <=
          threeLineMomentRatioCharge (zetaFiniteMultiplicityMass W)
            (zetaFiniteHorizontalMoment W) (zetaFiniteHorizontalFourthMoment W))
      ((zetaFiniteHorizontalMoment W) ^ 2 <
          (zetaFiniteMultiplicityMass W - 1) * zetaFiniteHorizontalFourthMoment W ->
        threeLineHorizontalVarianceCoefficient * zetaFiniteHorizontalFourthMoment W + threeLineCharge +
          (zetaFiniteMultiplicityMass W - 1) * threeLineHorizontalResidualProfile
            (zetaFiniteHorizontalMoment W / (zetaFiniteMultiplicityMass W - 1)) <
              threeLineMomentRatioCharge (zetaFiniteMultiplicityMass W)
                (zetaFiniteHorizontalMoment W) (zetaFiniteHorizontalFourthMoment W)) := by
  have h := threeLineMomentRatio_residual_comparison (zetaFiniteMultiplicityMass W)
    (zetaFiniteMultiplicityMass W - 1) (zetaFiniteHorizontalMoment W) (zetaFiniteHorizontalFourthMoment W)
    (by linarith) hM (zeta_odd_horizontal_moments_feasible W hCritical hReflect hOdd hN)
      (zetaFiniteHorizontalMomentRatio_strip W hCritical hM)
  have hOne : zetaFiniteMultiplicityMass W - (zetaFiniteMultiplicityMass W - 1) = 1 := by ring
  simpa only [hOne, one_mul] using h

theorem zeta_moment_ratio_equality_quantized (W : Finset Complex)
    (hCritical : forall w, Membership.mem W w -> And (0 < w.re) (w.re < 1))
    (hReflect : forall w, Membership.mem W w -> Membership.mem W (zetaHorizontalReflection w))
    (hN : 0 < zetaFiniteMultiplicityMass W) (hM : 0 < zetaFiniteHorizontalMoment W)
    (hEquality : Finset.sum W (fun w => (analyticOrderNatAt riemannZeta w : Real) *
      threeLineHorizontalProfile ((w.re - 1 / 2) ^ 2)) =
        threeLineMomentRatioCharge (zetaFiniteMultiplicityMass W)
          (zetaFiniteHorizontalMoment W) (zetaFiniteHorizontalFourthMoment W)) :
    And (zetaFiniteHorizontalEffectiveMass W =
      (zetaHorizontalThresholdOrder W (zetaFiniteHorizontalMomentRatio W) : Real))
      (Even (zetaHorizontalThresholdOrder W (zetaFiniteHorizontalMomentRatio W))) := by
  have hBounds := zetaFiniteHorizontalMomentRatio_bounds W hCritical hN hM
  have ha : forall w, Membership.mem W w -> 0 <= (analyticOrderNatAt riemannZeta w : Real) :=
    fun _ _ => Nat.cast_nonneg _
  have hx : forall w, Membership.mem W w ->
      And (0 <= (w.re - 1 / 2) ^ 2) ((w.re - 1 / 2) ^ 2 <= 1 / 4) :=
    fun w hw => zeta_horizontal_square_bounds w (hCritical w hw)
  have hCenter : Finset.sum W (fun w => (analyticOrderNatAt riemannZeta w : Real) *
      ((w.re - 1 / 2) ^ 2) ^ 2) = zetaFiniteHorizontalMomentRatio W * zetaFiniteHorizontalMoment W := by
    rw [zetaFiniteHorizontalFourthMoment_nested]
    unfold zetaFiniteHorizontalMomentRatio
    field_simp [hM.ne']
  have hSupport := (threeLineMomentRatio_equality_iff W
    (fun w => (analyticOrderNatAt riemannZeta w : Real)) (fun w => (w.re - 1 / 2) ^ 2)
    (zetaFiniteHorizontalMomentRatio W) ha hx (And.intro (le_of_lt hBounds.2.1) hBounds.2.2) hCenter).mp hEquality
  have hPoint (w : Complex) (hw : Membership.mem W w) :
      (analyticOrderNatAt riemannZeta w : Real) * ((w.re - 1 / 2) ^ 2 / zetaFiniteHorizontalMomentRatio W) =
        (analyticOrderNatAt riemannZeta w : Real) *
          halfRoundIndicator ((w.re - 1 / 2) ^ 2 / zetaFiniteHorizontalMomentRatio W) := by
    by_cases haZero : (analyticOrderNatAt riemannZeta w : Real) = 0
    case pos => simp [haZero]
    case neg =>
      by_cases hxZero : (w.re - 1 / 2) ^ 2 = 0
      case pos =>
        rw [hxZero]
        norm_num [halfRoundIndicator]
      case neg =>
        have hX := hSupport w hw (lt_of_le_of_ne (ha w hw) (Ne.symm haZero))
          (lt_of_le_of_ne (hx w hw).1 (Ne.symm hxZero))
        rw [hX, div_self hBounds.2.1.ne']
        norm_num [halfRoundIndicator]
  have hSum := Finset.sum_congr rfl hPoint
  rw [finiteWeighted_div_sum, <- zetaHorizontalThresholdOrder_cast] at hSum
  have hEffective : zetaFiniteHorizontalMoment W / zetaFiniteHorizontalMomentRatio W =
      zetaFiniteHorizontalEffectiveMass W := by
    unfold zetaFiniteHorizontalMomentRatio zetaFiniteHorizontalEffectiveMass
    field_simp [hM.ne', hBounds.1.ne']
  change zetaFiniteHorizontalMoment W / zetaFiniteHorizontalMomentRatio W = _ at hSum
  rw [hEffective] at hSum
  exact And.intro hSum (zetaHorizontalThresholdOrder_parity W (zetaFiniteHorizontalMomentRatio W) hCritical hReflect).1

end PrimeFactorOscillations

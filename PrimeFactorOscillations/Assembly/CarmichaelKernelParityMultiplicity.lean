/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.CarmichaelCompensatedMomentParity
import PrimeFactorOscillations.Helpers.ThreeLineCompensatedKernelSharpness

/-! # The sharp full-kernel parity penalty on actual zero clusters -/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 5000000

noncomputable section
namespace PrimeFactorOscillations

theorem threeLineEvenWeightedKernel_odd_charge {Iota : Type*} (S : Finset Iota)
    (m : Iota -> Nat) (x : Iota -> Real) (t : Real) (ht : 0 < t) (htMax : t <= 9 / 64)
    (hx : forall i, Membership.mem S i -> And (0 <= x i) (x i <= 1 / 4))
    (hMoment : Finset.sum S (fun i => (2 * (m i : Real)) * (x i) ^ 2) =
      t * Finset.sum S (fun i => (2 * (m i : Real)) * x i))
    (j : Nat) (hOdd : Odd j)
    (hCount : Finset.sum S (fun i => (2 * (m i : Real)) * x i) / t = (j : Real)) :
    threeLineCharge * Finset.sum S (fun i => 2 * (m i : Real)) +
      threeLineSizeBiasedProfile t * Finset.sum S (fun i => (2 * (m i : Real)) * x i) +
      threeLineKernelParityCoefficient t * t ^ 3 <=
      Finset.sum S (fun i => (2 * (m i : Real)) * threeLineHorizontalProfile (x i)) := by
  classical
  let R := S.filter (fun i => momentRoundThreshold <= x i / t)
  let K : Nat := 2 * Finset.sum R m
  have hCast : (K : Real) = Finset.sum S
      (fun i => (2 * (m i : Real)) * momentRoundIndicator momentRoundThreshold (x i / t)) := by
    simp [K, R, Finset.sum_filter, Finset.mul_sum, momentRoundIndicator, mul_ite]
  have hNotOdd : Not (Odd K) := by
    intro h
    have hMod := Nat.odd_iff.mp h
    dsimp [K] at hMod
    omega
  have ha : forall i, Membership.mem S i -> 0 <= 2 * (m i : Real) := by
    intro i _
    positivity
  have hMain := threeLineWeightedCompensatedKernel_charge S
    (fun i => 2 * (m i : Real)) x t ht htMax ha hx hMoment
  rw [<- hCast, hCount] at hMain
  have hGap := odd_even_real_abs_gap j K hOdd hNotOdd
  have hCoefficient : 0 <= threeLineKernelParityCoefficient t * t ^ 3 :=
    mul_nonneg (le_of_lt (threeLineKernelParityCoefficient_pos t (le_of_lt ht) htMax))
      (pow_nonneg (le_of_lt ht) 3)
  have hScaled := _root_.mul_le_mul_of_nonneg_left hGap hCoefficient
  nlinarith only [hMain, hScaled]

theorem threeLineEvenWeightedKernel_uniform_odd_charge {Iota : Type*} (S : Finset Iota)
    (m : Iota -> Nat) (x : Iota -> Real) (t : Real) (ht : 0 < t) (htMax : t <= 9 / 64)
    (hx : forall i, Membership.mem S i -> And (0 <= x i) (x i <= 1 / 4))
    (hMoment : Finset.sum S (fun i => (2 * (m i : Real)) * (x i) ^ 2) =
      t * Finset.sum S (fun i => (2 * (m i : Real)) * x i))
    (j : Nat) (hOdd : Odd j)
    (hCount : Finset.sum S (fun i => (2 * (m i : Real)) * x i) / t = (j : Real)) :
    threeLineCharge * Finset.sum S (fun i => 2 * (m i : Real)) +
      threeLineSizeBiasedProfile t * Finset.sum S (fun i => (2 * (m i : Real)) * x i) +
      (momentRoundThreshold * threeLineParityCubicCoefficient) * t ^ 3 <=
      Finset.sum S (fun i => (2 * (m i : Real)) * threeLineHorizontalProfile (x i)) := by
  have hMain := threeLineEvenWeightedKernel_odd_charge S m x t ht htMax hx hMoment j hOdd hCount
  have hFloor := _root_.mul_le_mul_of_nonneg_right
    (threeLineKernelParityCoefficient_ge_tau t (le_of_lt ht) htMax)
    (pow_nonneg (le_of_lt ht) 3)
  nlinarith only [hMain, hFloor]

theorem zeta_finite_kernel_parity_bound (height : Real) (hHeight : 2 <= abs height)
    (W : Finset Complex)
    (hCritical : forall w, Membership.mem W w -> And (0 < w.re) (w.re < 1))
    (hSame : forall w, Membership.mem W w -> w.im = height)
    (hReflect : forall w, Membership.mem W w ->
      Membership.mem W (zetaHorizontalReflection w))
    (hN : 0 < zetaFiniteMultiplicityMass W) (hM : 0 < zetaFiniteHorizontalMoment W) :
    And (Even (zetaCompensatedThresholdOrder W))
      (threeLineMomentRatioCharge (zetaFiniteMultiplicityMass W)
          (zetaFiniteHorizontalMoment W) (zetaFiniteHorizontalFourthMoment W) +
        threeLineKernelParityCoefficient (zetaFiniteHorizontalMomentRatio W) *
          (zetaFiniteHorizontalMomentRatio W) ^ 3 *
          abs (zetaFiniteHorizontalEffectiveMass W - (zetaCompensatedThresholdOrder W : Real)) <=
            threeLineCharge * threeLineMultiplicityBudget height) := by
  have hBounds := zetaFiniteHorizontalMomentRatio_bounds W hCritical hN hM
  have htMax := zetaFiniteHorizontalMomentRatio_strip W hCritical hM
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
  have hStrong := threeLineWeightedCompensatedKernel_charge W
    (fun w => (analyticOrderNatAt riemannZeta w : Real)) (fun w => (w.re - 1 / 2) ^ 2)
    (zetaFiniteHorizontalMomentRatio W) hBounds.2.1 htMax ha hx hCenter
  rw [<- zetaCompensatedThresholdOrder_cast W hBounds.2.1] at hStrong
  change threeLineCharge * zetaFiniteMultiplicityMass W +
    threeLineSizeBiasedProfile (zetaFiniteHorizontalMomentRatio W) * zetaFiniteHorizontalMoment W +
    threeLineKernelParityCoefficient (zetaFiniteHorizontalMomentRatio W) *
      (zetaFiniteHorizontalMomentRatio W) ^ 3 *
      abs (zetaFiniteHorizontalMoment W / zetaFiniteHorizontalMomentRatio W -
        (zetaCompensatedThresholdOrder W : Real)) <= _ at hStrong
  have hEffective : zetaFiniteHorizontalMoment W / zetaFiniteHorizontalMomentRatio W =
      zetaFiniteHorizontalEffectiveMass W := by
    unfold zetaFiniteHorizontalMomentRatio zetaFiniteHorizontalEffectiveMass
    field_simp [hM.ne', hBounds.1.ne']
  rw [hEffective] at hStrong
  have hCharge : threeLineMomentRatioCharge (zetaFiniteMultiplicityMass W)
      (zetaFiniteHorizontalMoment W) (zetaFiniteHorizontalFourthMoment W) =
      threeLineCharge * zetaFiniteMultiplicityMass W +
        threeLineSizeBiasedProfile (zetaFiniteHorizontalMomentRatio W) * zetaFiniteHorizontalMoment W := by
    unfold threeLineMomentRatioCharge zetaFiniteHorizontalMomentRatio
    ring
  have hUpper := zeta_finite_horizontal_profile_upper height hHeight W hCritical hSame
  exact And.intro (zetaCompensatedThresholdOrder_parity W hCritical hReflect).1
    (by nlinarith only [hStrong, hUpper, hCharge])

theorem zeta_kernel_parity_odd_effective_gap (height : Real) (hHeight : 2 <= abs height)
    (W : Finset Complex)
    (hCritical : forall w, Membership.mem W w -> And (0 < w.re) (w.re < 1))
    (hSame : forall w, Membership.mem W w -> w.im = height)
    (hReflect : forall w, Membership.mem W w ->
      Membership.mem W (zetaHorizontalReflection w))
    (hN : 0 < zetaFiniteMultiplicityMass W) (hM : 0 < zetaFiniteHorizontalMoment W)
    (j : Nat) (hOdd : Odd j) (hEffective : zetaFiniteHorizontalEffectiveMass W = (j : Real)) :
    threeLineMomentRatioCharge (zetaFiniteMultiplicityMass W)
        (zetaFiniteHorizontalMoment W) (zetaFiniteHorizontalFourthMoment W) +
      threeLineKernelParityCoefficient (zetaFiniteHorizontalMomentRatio W) *
        (zetaFiniteHorizontalMomentRatio W) ^ 3 <=
        threeLineCharge * threeLineMultiplicityBudget height := by
  have hBounds := zetaFiniteHorizontalMomentRatio_bounds W hCritical hN hM
  have htMax := zetaFiniteHorizontalMomentRatio_strip W hCritical hM
  have hMain := (zeta_finite_kernel_parity_bound height hHeight W
    hCritical hSame hReflect hN hM).2
  have hGap := odd_even_real_abs_gap j (zetaCompensatedThresholdOrder W) hOdd
    (zetaCompensatedThresholdOrder_parity W hCritical hReflect).2
  rw [<- hEffective] at hGap
  have hCoefficient : 0 <= threeLineKernelParityCoefficient (zetaFiniteHorizontalMomentRatio W) *
      (zetaFiniteHorizontalMomentRatio W) ^ 3 :=
    mul_nonneg (le_of_lt (threeLineKernelParityCoefficient_pos _ (le_of_lt hBounds.2.1) htMax))
      (pow_nonneg (le_of_lt hBounds.2.1) 3)
  have hScaled := _root_.mul_le_mul_of_nonneg_left hGap hCoefficient
  nlinarith only [hMain, hScaled]

theorem zeta_kernel_parity_uniform_odd_gap (height : Real) (hHeight : 2 <= abs height)
    (W : Finset Complex)
    (hCritical : forall w, Membership.mem W w -> And (0 < w.re) (w.re < 1))
    (hSame : forall w, Membership.mem W w -> w.im = height)
    (hReflect : forall w, Membership.mem W w ->
      Membership.mem W (zetaHorizontalReflection w))
    (hN : 0 < zetaFiniteMultiplicityMass W) (hM : 0 < zetaFiniteHorizontalMoment W)
    (j : Nat) (hOdd : Odd j) (hEffective : zetaFiniteHorizontalEffectiveMass W = (j : Real)) :
    threeLineMomentRatioCharge (zetaFiniteMultiplicityMass W)
        (zetaFiniteHorizontalMoment W) (zetaFiniteHorizontalFourthMoment W) +
      (momentRoundThreshold * threeLineParityCubicCoefficient) *
        (zetaFiniteHorizontalMomentRatio W) ^ 3 <=
        threeLineCharge * threeLineMultiplicityBudget height := by
  have hBounds := zetaFiniteHorizontalMomentRatio_bounds W hCritical hN hM
  have htMax := zetaFiniteHorizontalMomentRatio_strip W hCritical hM
  have hMain := zeta_kernel_parity_odd_effective_gap height hHeight W
    hCritical hSame hReflect hN hM j hOdd hEffective
  have hFloor := _root_.mul_le_mul_of_nonneg_right
    (threeLineKernelParityCoefficient_ge_tau _ (le_of_lt hBounds.2.1) htMax)
    (pow_nonneg (le_of_lt hBounds.2.1) 3)
  nlinarith only [hMain, hFloor]

theorem kernelParityPenalty_stronger (t : Real) (ht : 0 < t) (htMax : t <= 9 / 64) :
    momentRoundThreshold * t ^ 3 < threeLineKernelParityCoefficient t * t ^ 3 := by
  exact _root_.mul_lt_mul_of_pos_right
    (threeLineKernelParityCoefficient_gt_delta t (le_of_lt ht) htMax) (pow_pos ht 3)

theorem kernelParityPenalty_stronger_than_squared (N t : Real)
    (hN : 2 <= N) (ht : 0 < t) (htMax : t <= 9 / 64) :
    t ^ 3 / (2 * N) < threeLineKernelParityCoefficient t * t ^ 3 := by
  exact lt_trans (compensatedParityPenalty_stronger N t hN ht)
    (kernelParityPenalty_stronger t ht htMax)

end PrimeFactorOscillations

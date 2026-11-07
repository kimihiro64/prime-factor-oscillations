/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.ThresholdEvenSharpness
import PrimeFactorOscillations.Helpers.ThresholdNonlinearTransfer

/-! # Finite nonattainment and the strict full signed nonlinear charge -/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 5000000

noncomputable section
namespace PrimeFactorOscillations

theorem thresholdPositivePacket_zero_coordinate (d z y : Real)
    (hd : And (0 < d) (d < 1)) (hz : 1 <= z) (hy : 0 <= y)
    (hQ : thresholdPositivePacket d z y = 0) : y = z * momentRoundIndicator d y := by
  have hb := thresholdPositiveMultiplier_bounds d z hd hz
  by_cases hCut : d <= y
  case pos =>
    rw [thresholdPositivePacket_selected d z y hCut] at hQ
    have hFactor : Not (y - thresholdPositiveMultiplier d z = 0) := by linarith only [hy, hb.1]
    have hSq : (y - z) ^ 2 = 0 := (mul_eq_zero.mp hQ).resolve_right hFactor
    have hY : y = z := sub_eq_zero.mp (sq_eq_zero_iff.mp hSq)
    simp only [momentRoundIndicator, if_pos hCut, mul_one]
    exact hY
  case neg =>
    have hLow : y < d := lt_of_not_ge hCut
    rw [thresholdPositivePacket_unselected d z y hd hz hLow] at hQ
    have hFactor : Not ((y - d) * (y - (2 * z + thresholdPositiveMultiplier d z - d)) = 0) :=
      (mul_pos_of_neg_of_neg (by linarith only [hLow]) (by linarith only [hLow, hb.2])).ne'
    have hQ' : y * ((y - d) * (y - (2 * z + thresholdPositiveMultiplier d z - d))) = 0 := by
      nlinarith only [hQ]
    have hY : y = 0 := (mul_eq_zero.mp hQ').resolve_right hFactor
    simp only [momentRoundIndicator, if_neg hCut, mul_zero]
    exact hY

theorem finiteWeightedThreshold_positive_strict {Iota : Type*} (S : Finset Iota)
    (a y : Iota -> Real) (d : Real) (hd : And (0 < d) (d < 1))
    (ha : forall i, Membership.mem S i -> 0 <= a i)
    (hy : forall i, Membership.mem S i -> 0 <= y i)
    (hMoment : Finset.sum S (fun i => a i * (y i) ^ 2) = Finset.sum S (fun i => a i * y i))
    (hMass : 0 < Finset.sum S (fun i => a i * y i))
    (hKM : thresholdSelectedMass d S a y < Finset.sum S (fun i => a i * y i)) :
    thresholdPositiveCost d (Finset.sum S (fun i => a i * y i)) (thresholdSelectedMass d S a y) <
      Finset.sum S (fun i => a i * y i * (y i - 1) ^ 2) := by
  classical
  let M := Finset.sum S (fun i => a i * y i)
  let K := thresholdSelectedMass d S a y
  let z := thresholdPositiveRoot d M K
  have hK := (finiteWeightedThreshold_domain S a y d hd.2 ha hy hMoment hMass).1
  have hz := thresholdPositiveRoot_gt_one d M K hd hMass hK hKM
  have hCost := finiteWeightedThreshold_positive_cost S a y d hd ha hy hMoment hMass hKM.le
  by_contra h
  have hEq : Finset.sum S (fun i => a i * y i * (y i - 1) ^ 2) = thresholdPositiveCost d M K :=
    le_antisymm (le_of_not_gt h) hCost
  have hDefect := finiteWeightedThreshold_exact_positive_defect S a y d hd ha hy hMoment hMass hKM.le
  have hSum : Finset.sum S (fun i => a i * thresholdPositivePacket d z (y i)) = 0 := by
    rw [hEq] at hDefect
    exact hDefect.trans (sub_self _)
  have hNonneg : forall i, Membership.mem S i -> 0 <= a i * thresholdPositivePacket d z (y i) :=
    fun i hi => mul_nonneg (ha i hi) (thresholdPositivePacket_nonneg d z (y i) hd (by linarith only [hz]) (hy i hi))
  have hEach : forall i, Membership.mem S i -> a i * y i = z * (a i * momentRoundIndicator d (y i)) := by
    intro i hi
    by_cases haZero : a i = 0
    case pos => simp [haZero]
    case neg =>
      have hTerm : a i * thresholdPositivePacket d z (y i) = 0 := by
        have hh := Finset.single_le_sum hNonneg hi
        rw [hSum] at hh
        exact le_antisymm hh (hNonneg i hi)
      have hQ := (mul_eq_zero.mp hTerm).resolve_left haZero
      have hY := thresholdPositivePacket_zero_coordinate d z (y i) hd (by linarith only [hz]) (hy i hi) hQ
      have hh := congrArg (fun q : Real => a i * q) hY
      nlinarith only [hh]
  have hMZ : M = z * K := by
    calc
      _ = Finset.sum S (fun i => z * (a i * momentRoundIndicator d (y i))) := Finset.sum_congr rfl hEach
      _ = _ := by rw [<- Finset.mul_sum]; rfl
  have hr := thresholdPositiveRoot_relation d M K hd hMass hK
  change K * z * (z - d) = (1 - d) * M at hr
  rw [hMZ] at hr
  have hPositive := mul_pos (mul_pos hK (show 0 < z by linarith only [hz])) (sub_pos.mpr hz)
  nlinarith only [hr, hPositive]

theorem finiteWeightedThreshold_nonlinear_strict {Iota : Type*} (S : Finset Iota)
    (a y : Iota -> Real) (d : Real) (hd : And (0 < d) (d < 1))
    (ha : forall i, Membership.mem S i -> 0 <= a i)
    (hy : forall i, Membership.mem S i -> 0 <= y i)
    (hMoment : Finset.sum S (fun i => a i * (y i) ^ 2) = Finset.sum S (fun i => a i * y i))
    (hMass : 0 < Finset.sum S (fun i => a i * y i))
    (hKM : thresholdSelectedMass d S a y < Finset.sum S (fun i => a i * y i)) :
    thresholdNonlinearCost d (Finset.sum S (fun i => a i * y i)) (thresholdSelectedMass d S a y) <
      Finset.sum S (fun i => a i * y i * (y i - 1) ^ 2) := by
  unfold thresholdNonlinearCost
  rw [if_pos hKM.le]
  exact finiteWeightedThreshold_positive_strict S a y d hd ha hy hMoment hMass hKM

theorem finiteWeightedThreshold_nonlinear_scaled_strict {Iota : Type*} (S : Finset Iota)
    (a x : Iota -> Real) (d : Real) (hd : And (0 < d) (d < 1)) (t : Real) (ht : 0 < t)
    (ha : forall i, Membership.mem S i -> 0 <= a i)
    (hx : forall i, Membership.mem S i -> 0 <= x i)
    (hMoment : Finset.sum S (fun i => a i * (x i) ^ 2) =
      t * Finset.sum S (fun i => a i * x i))
    (hMass : 0 < Finset.sum S (fun i => a i * x i))
    (hKM : thresholdSelectedMass d S a (fun i => x i / t) < Finset.sum S (fun i => a i * x i) / t) :
    thresholdNonlinearCost d (Finset.sum S (fun i => a i * x i) / t)
      (thresholdSelectedMass d S a (fun i => x i / t)) * t ^ 3 <
        Finset.sum S (fun i => a i * x i * (x i - t) ^ 2) := by
  have hNormalized : Finset.sum S (fun i => a i * (x i / t) ^ 2) =
      Finset.sum S (fun i => a i * (x i / t)) := by
    calc
      _ = Finset.sum S (fun i => a i * (x i) ^ 2) / t ^ 2 := by
        simp only [div_pow]
        exact finiteWeighted_div_sum S a (fun i => (x i) ^ 2) (t ^ 2)
      _ = Finset.sum S (fun i => a i * x i) / t := by
        rw [hMoment]
        field_simp [ht.ne']
      _ = _ := (finiteWeighted_div_sum S a x t).symm
  have hNormalizedMass : 0 < Finset.sum S (fun i => a i * (x i / t)) := by
    rw [finiteWeighted_div_sum]
    exact div_pos hMass ht
  have hKM' : thresholdSelectedMass d S a (fun i => x i / t) < Finset.sum S (fun i => a i * (x i / t)) := by
    rw [finiteWeighted_div_sum]
    exact hKM
  have hCost := finiteWeightedThreshold_nonlinear_strict S a (fun i => x i / t) d hd
    ha (fun i hi => div_nonneg (hx i hi) (le_of_lt ht)) hNormalized hNormalizedMass hKM'
  rw [finiteWeighted_div_sum] at hCost
  have hScaled := _root_.mul_lt_mul_of_pos_right hCost (pow_pos ht 3)
  have hEnergy : t ^ 3 * Finset.sum S (fun i => a i * (x i / t) * (x i / t - 1) ^ 2) =
      Finset.sum S (fun i => a i * x i * (x i - t) ^ 2) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    have h := congrArg (fun q : Real => a i * q) (finiteWeighted_rescale_energy (x i) t ht)
    nlinarith only [h]
  nlinarith only [hScaled, hEnergy]

theorem threeLineWeightedNonlinearThreshold_strict {Iota : Type*} (S : Finset Iota)
    (a x : Iota -> Real) (d : Real) (hd : And (0 < d) (d < 1))
    (t : Real) (ht : 0 < t) (htMax : t <= 9 / 64)
    (ha : forall i, Membership.mem S i -> 0 <= a i)
    (hx : forall i, Membership.mem S i -> And (0 <= x i) (x i <= 1 / 4))
    (hMoment : Finset.sum S (fun i => a i * (x i) ^ 2) =
      t * Finset.sum S (fun i => a i * x i))
    (hMass : 0 < Finset.sum S (fun i => a i * x i))
    (hKM : thresholdSelectedMass d S a (fun i => x i / t) < Finset.sum S (fun i => a i * x i) / t) :
    threeLineCharge * Finset.sum S a +
      threeLineSizeBiasedProfile t * Finset.sum S (fun i => a i * x i) +
      threeLineParityCubicCoefficient * t ^ 3 *
        thresholdNonlinearCost d (Finset.sum S (fun i => a i * x i) / t)
          (thresholdSelectedMass d S a (fun i => x i / t)) <
      Finset.sum S (fun i => a i * threeLineHorizontalProfile (x i)) := by
  have hCost := finiteWeightedThreshold_nonlinear_scaled_strict S a x d hd t ht ha
    (fun i hi => (hx i hi).1) hMoment hMass hKM
  have hTau := threeLineParityCubicCoefficient_pos
  have hScaled := _root_.mul_lt_mul_of_pos_left hCost hTau
  have hFloor : threeLineParityCubicCoefficient *
      Finset.sum S (fun i => a i * x i * (x i - t) ^ 2) <=
      Finset.sum S (fun i => a i * x i * (x i - t) ^ 2 * threeLineSizeBiasedRemainder (x i) t) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    have hKernel := threeLineSizeBiasedRemainder_ge_tau (x i) t (hx i hi).1 (hx i hi).2
      (le_of_lt ht) htMax
    have hNonneg : 0 <= a i * x i * (x i - t) ^ 2 :=
      mul_nonneg (mul_nonneg (ha i hi) (hx i hi).1) (sq_nonneg _)
    have hProduct := _root_.mul_le_mul_of_nonneg_left hKernel hNonneg
    nlinarith only [hProduct]
  have hLedger := threeLineWeightedKernel_ledger S a x t (by linarith)
    (fun i hi => (hx i hi).2) hMoment
  nlinarith only [hScaled, hFloor, hLedger]

end PrimeFactorOscillations

/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.ThresholdBandIntegerCost
import PrimeFactorOscillations.Helpers.ThresholdNonlinearTransfer

/-! # The integer correction in the full signed kernel ledger -/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 5000000

noncomputable section
namespace PrimeFactorOscillations

theorem finiteWeightedThreshold_integer_scaled {Iota : Type*} (S : Finset Iota)
    (a x : Iota -> Real) (d : Real) (hd : And (0 < d) (d < 1)) (t : Real) (ht : 0 < t)
    (ha : forall i, Membership.mem S i -> 0 <= a i)
    (hx : forall i, Membership.mem S i -> 0 <= x i)
    (hMoment : Finset.sum S (fun i => a i * (x i) ^ 2) =
      t * Finset.sum S (fun i => a i * x i))
    (hMass : 0 < Finset.sum S (fun i => a i * x i))
    (hBand : exists m : Nat, thresholdBandMass d S a (fun i => x i / t) = 2 * (m : Real)) :
    (thresholdNonlinearCost d (Finset.sum S (fun i => a i * x i) / t)
      (thresholdSelectedMass d S a (fun i => x i / t)) +
      thresholdIntegerCorrection d (Finset.sum S (fun i => a i * x i) / t)
        (thresholdSelectedMass d S a (fun i => x i / t))) * t ^ 3 <=
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
  have hCost := finiteWeightedThreshold_integer_cost S a (fun i => x i / t) d hd
    ha (fun i hi => div_nonneg (hx i hi) (le_of_lt ht)) hNormalized hNormalizedMass hBand
  rw [finiteWeighted_div_sum] at hCost
  have hScaled := _root_.mul_le_mul_of_nonneg_right hCost (le_of_lt (pow_pos ht 3))
  have hEnergy : t ^ 3 * Finset.sum S (fun i => a i * (x i / t) * (x i / t - 1) ^ 2) =
      Finset.sum S (fun i => a i * x i * (x i - t) ^ 2) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    have h := congrArg (fun q : Real => a i * q) (finiteWeighted_rescale_energy (x i) t ht)
    nlinarith only [h]
  nlinarith only [hScaled, hEnergy]

theorem threeLineWeightedIntegerThreshold_charge {Iota : Type*} (S : Finset Iota)
    (a x : Iota -> Real) (d : Real) (hd : And (0 < d) (d < 1))
    (t : Real) (ht : 0 < t) (htMax : t <= 9 / 64)
    (ha : forall i, Membership.mem S i -> 0 <= a i)
    (hx : forall i, Membership.mem S i -> And (0 <= x i) (x i <= 1 / 4))
    (hMoment : Finset.sum S (fun i => a i * (x i) ^ 2) =
      t * Finset.sum S (fun i => a i * x i))
    (hMass : 0 < Finset.sum S (fun i => a i * x i))
    (hBand : exists m : Nat, thresholdBandMass d S a (fun i => x i / t) = 2 * (m : Real)) :
    threeLineCharge * Finset.sum S a +
      threeLineSizeBiasedProfile t * Finset.sum S (fun i => a i * x i) +
      threeLineParityCubicCoefficient * t ^ 3 *
        (thresholdNonlinearCost d (Finset.sum S (fun i => a i * x i) / t)
          (thresholdSelectedMass d S a (fun i => x i / t)) +
          thresholdIntegerCorrection d (Finset.sum S (fun i => a i * x i) / t)
            (thresholdSelectedMass d S a (fun i => x i / t))) <=
      Finset.sum S (fun i => a i * threeLineHorizontalProfile (x i)) := by
  have hCost := finiteWeightedThreshold_integer_scaled S a x d hd t ht ha
    (fun i hi => (hx i hi).1) hMoment hMass hBand
  have hTau := threeLineParityCubicCoefficient_pos
  have hScaled := _root_.mul_le_mul_of_nonneg_left hCost (le_of_lt hTau)
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

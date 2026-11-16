/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianNormalizedSpectralScaling

/-! # Full forbidden-edge error allowance and the retained half-gap -/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

def hamiltonianForbiddenRepairCost (delta : Real) : Real :=
  hamiltonianNormalizedScalingCost delta + 1 / Real.log 4

def hamiltonianForbiddenRepairSmall (delta : Real) : Real :=
  min (hamiltonianNormalizedScalingSmall delta)
    (delta * Real.log 4 / (2 * hamiltonianForbiddenRepairCost delta))

theorem hamiltonian_forbidden_repair_constants_positive
    (delta : Real) (hd0 : 0 < delta) (hd1 : delta < 1) :
    0 < hamiltonianForbiddenRepairSmall delta /\
      0 < hamiltonianForbiddenRepairCost delta := by
  have hBase := hamiltonian_normalized_scaling_constants_positive delta hd0 hd1
  have hFour : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hC : 0 < hamiltonianForbiddenRepairCost delta := by
    have hBaseCost := hBase.2
    dsimp [hamiltonianForbiddenRepairCost]
    positivity
  refine And.intro ?_ hC
  unfold hamiltonianForbiddenRepairSmall
  apply lt_min
  . exact hBase.1
  . positivity

theorem hamiltonian_forbidden_repair_all_budgets
    (n delta eta : Real) (hn : 1 <= n)
    (hd0 : 0 < delta) (hd1 : delta < 1) (he : 0 <= eta)
    (hSmall : eta * Real.log (4 * n) ^ 2 <= hamiltonianForbiddenRepairSmall delta) :
    (eta <= 1 / 2) /\
    (eta * Real.log (4 * n) ^ 2 <= hamiltonianNormalizedScalingSmall delta) /\
    (hamiltonianNormalizedScalingCost delta * eta * Real.log (4 * n) + eta <=
      hamiltonianForbiddenRepairCost delta * eta * Real.log (4 * n)) /\
    (hamiltonianForbiddenRepairCost delta * eta * Real.log (4 * n) <= delta / 2) := by
  let L := Real.log (4 * n)
  let C := hamiltonianForbiddenRepairCost delta
  have hFour : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hL : Real.log 4 <= L :=
    Real.log_le_log (by norm_num) (by linarith only [hn])
  have hL0 : 0 <= L := hFour.le.trans hL
  have hL2 : (Real.log 4) ^ 2 <= L ^ 2 := by
    have h := mul_le_mul hL hL hFour.le hL0
    simpa only [pow_two] using h
  have hC : 0 < C := (hamiltonian_forbidden_repair_constants_positive delta hd0 hd1).2
  have hScaleSmall : eta * L ^ 2 <= hamiltonianNormalizedScalingSmall delta :=
    hSmall.trans (min_le_left _ _)
  have hCore : hamiltonianNormalizedScalingSmall delta <=
      (delta / 28) * (Real.log 4) ^ 2 := by
    have h := min_le_left
      (((1 - (1 - delta / 2)) / 14) * (Real.log 4) ^ 2)
      (1 / (256 * hamiltonianScalingOrderCost (1 - delta / 2) ^ 2))
    change hamiltonianNormalizedScalingSmall delta <= _ at h
    have hId : ((1 - (1 - delta / 2)) / 14) * (Real.log 4) ^ 2 =
      (delta / 28) * (Real.log 4) ^ 2 := by ring
    rwa [hId] at h
  have hEtaScaled : eta * (Real.log 4) ^ 2 <=
      (delta / 28) * (Real.log 4) ^ 2 :=
    (mul_le_mul_of_nonneg_left hL2 he).trans (hScaleSmall.trans hCore)
  have hEta : eta <= delta / 28 := by
    by_contra h
    exact (not_lt_of_ge hEtaScaled)
      (mul_lt_mul_of_pos_right (lt_of_not_ge h) (sq_pos_of_pos hFour))
  have hEtaHalf : eta <= 1 / 2 := by linarith only [hEta, hd1]
  have hAbsorb := mul_le_mul_of_nonneg_left hL (div_nonneg he hFour.le)
  have hCancel : (eta / Real.log 4) * Real.log 4 = eta := by field_simp [ne_of_gt hFour]
  rw [hCancel] at hAbsorb
  have hFullError : hamiltonianNormalizedScalingCost delta * eta * L + eta <= C * eta * L := by
    change hamiltonianNormalizedScalingCost delta * eta * L + eta <=
      (hamiltonianNormalizedScalingCost delta + 1 / Real.log 4) * eta * L
    calc
      _ <= hamiltonianNormalizedScalingCost delta * eta * L +
          (eta / Real.log 4) * L := add_le_add (le_refl _) hAbsorb
      _ = _ := by ring
  have hLastSmall : eta * L ^ 2 <= delta * Real.log 4 / (2 * C) :=
    hSmall.trans (min_le_right _ _)
  have hProduct := mul_le_mul_of_nonneg_left hL (mul_nonneg he hL0)
  have hEtaLScaled : (eta * L) * Real.log 4 <=
      (delta / (2 * C)) * Real.log 4 := by
    calc
      _ <= eta * L ^ 2 := by nlinarith only [hProduct]
      _ <= delta * Real.log 4 / (2 * C) := hLastSmall
      _ = _ := by ring
  have hEtaL : eta * L <= delta / (2 * C) := by
    by_contra h
    exact (not_lt_of_ge hEtaLScaled)
      (mul_lt_mul_of_pos_right (lt_of_not_ge h) hFour)
  have hGap : C * eta * L <= delta / 2 := by
    have h := mul_le_mul_of_nonneg_left hEtaL hC.le
    have hId : C * (delta / (2 * C)) = delta / 2 := by field_simp [ne_of_gt hC]
    rw [hId] at h
    nlinarith only [h]
  exact And.intro hEtaHalf (And.intro hScaleSmall (And.intro hFullError hGap))

end PrimeFactorOscillations

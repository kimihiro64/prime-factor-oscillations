/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import OAI.NumberTheory.DirichletL.Energy.FirstSourceParameters
import OAI.NumberTheory.DirichletL.Energy.LiveClippingDefect

/-!
# QRHSourceRange

Maintained extraction of completed detector/packet proof components.
All original theorem hypotheses and retained proof bodies are preserved.
This module alone asserts no improved zero-free boundary.
-/

set_option autoImplicit false
set_option Elab.async false

/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

/-!
# Exact range of the QRH source parameter gates

Use the pinned fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb source quantities.
These two source gates only need nonnegative kappa. This file makes no change
to the separate beta-compatibility or analytic physical-moment requirements.
-/


noncomputable section
namespace PrimeFactorOscillations.QRHSourceRange

open OAI.SevenEighths
open CenteredMomentEnergyWidthSchedule CenteredMomentEnergyStageReserveSchedule
open CenteredMomentEnergyFirstStageLossBudget CenteredMomentEnergyFirstActualFrequencyBudget
open CenteredMomentEnergyFirstGaussianProfileWeights CenteredMomentFirstAmplifiedFourCoefficients
open CenteredMomentEnergyFirstLiveAdmission CenteredMomentSectorLocalization
open CenteredMomentEnergyFirstSourceParameters

theorem parameter_gates_nonnegative (M A B kappa eps : Real)
    (hM : 0 <= M) (hA : 0 <= A) (hB : 0 <= B)
    (hkappa : 0 <= kappa) (heps : 0 < eps) :
    let sigma := amplification eps
    let r := reserve M B eps
    And (0 < sigma) (And (sigma <= 1) (And (0 < r / 4) (And (r / 4 <= sigma / 4) (And (r / 4 <= 1) (And (0 < sourceEpsilon M A B eps) (And (sourceEpsilon M A B eps <= 1) (And (0 < maskEpsilon M B eps) (And (0 < mesh M B kappa eps) (And (mesh M B kappa eps <= sigma / 12) (And (0 <= sigma / 12) (And (sigma / 12 < sigma / 6) (And (0 < 2 * sigma + 1) (0 <= A + 1))))))))))))) := by
  dsimp only
  have hb := bounds M B kappa eps hM hB hkappa heps
  have hr := hb.2.2.2.1
  have hrs : reserve M B eps <= amplification eps / 100 := min_le_left _ _
  have hm := hb.2.2.2.2.2.1
  have hes : 0 < sourceEpsilon M A B eps := by
    unfold sourceEpsilon
    positivity
  have hesr : sourceEpsilon M A B eps <= reserve M B eps := by
    unfold sourceEpsilon
    exact div_le_self hr.le (by linarith)
  exact And.intro (hb.1) (And.intro (hb.2.1) (And.intro ((by positivity)) (And.intro ((by linarith)) (And.intro ((by linarith)) (And.intro (hes) (And.intro ((by linarith)) (And.intro ((by unfold maskEpsilon; positivity)) (And.intro (hb.2.2.2.2.1) (And.intro ((by linarith)) (And.intro ((by linarith [hb.1])) (And.intro ((by linarith [hb.1])) (And.intro ((by linarith [hb.1])) ((by linarith))))))))))))))

theorem eventually_actual_four_fit_nonnegative (M A P B kappa eps : Real)
    (hM : 0 <= M) (hA : 0 <= A) (hB : 0 <= B)
    (hready : readyBudget A P <= B)
    (hkappa : 0 <= kappa) (heps : 0 < eps) :
    let r := reserve M B eps
    Filter.Eventually (fun Z : Real =>
      And (1 < Z) (forall (k : Nat) (epsChild : Real),
        epsChild <= stageLoss M B eps k -> forall j : Fin 4,
          losses (sourceEpsilon M A B eps) (r / 4) (r / 4) (readyBudget A P) j +
          lossVector (amplification eps) (frequencyLoss Z 32 (r / 4)) (r / 4)
            ((readyBudget A P + readyBudget A P) * maskEpsilon M B eps + epsChild + r / 4 +
              (frequencyLoss Z 32 (r / 4) + r / 4 + r / 4) / 6 + (r / 4) / 3 +
              kappa * mesh M B kappa eps)
            (sourceEpsilon M A B eps) A (2 * amplification eps + 1) j +
          sourceEpsilon M A B eps * (A + 1) + r / 4 <= columnLoss M B eps k))
      Filter.atTop := by
  dsimp only
  have h := actual_frequency_four_budget M A B (A + 1) kappa eps
    hM hA hB (by linarith) hkappa heps
  have hem := h.2.2.1
  have hevent := h.2.2.2.2.2
  have hr : 0 < reserve M B eps := (bounds M B kappa eps hM hB hkappa heps).2.2.2.1
  filter_upwards [hevent] with Z hZ
  refine And.intro hZ.1 ?_
  intro k epsChild hchild j
  have hfit := hZ.2.2.2 k epsChild (reserve M B eps) (reserve M B eps)
    hchild le_rfl le_rfl j
  have hmono := source_cap_mono
    (sourceEpsilon M A B eps) (reserve M B eps / 4) (reserve M B eps / 4)
    (readyBudget A P) B (amplification eps) (frequencyLoss Z 32 (reserve M B eps / 4))
    (reserve M B eps / 4) (maskEpsilon M B eps) epsChild (reserve M B eps / 4)
    (reserve M B eps / 4) (reserve M B eps / 4) kappa (mesh M B kappa eps)
    A (2 * amplification eps + 1) hready (by positivity) hem.le j
  change losses (sourceEpsilon M A B eps) _ _ B j +
    lossVector _ _ _ (sourcePaid B (maskEpsilon M B eps) epsChild _ _ _ _ _ _ _) _ _ _ j +
    sourceEpsilon M A B eps * (A + 1) + _ + _ + _ + _ <= _ at hfit
  dsimp only [sourcePaid] at hmono hfit
  unfold columnLoss
  dsimp only [sourceEpsilon, maskEpsilon] at *
  linarith only [hmono, hfit]


/-- The exact slot budget has no lower bound on kappa. -/
theorem slot_budget (M total ell kappa defect : Real)
    (hlarge : 5 * M / 6 - defect <= total + ell)
    (hcap : total + ell + (6 * kappa - 1) * ell <= M) :
    (6 * kappa - 1) * ell <= M / 6 + defect := by
  linarith

/-- A kappa-dependent reserve replaces the fixed kappa = 3/4 reserve. -/
theorem small_slot_reserve (M ell kappa xi defect : Real)
    (hk : 1 / 2 < kappa)
    (hslot : (6 * kappa - 1) * ell <= M / 6 + defect)
    (hreserve :
      2 * (6 * kappa - 1) * xi + 2 * (6 * kappa + 1) * defect <=
        (2 * kappa - 1) * M) :
    2 * ell + defect + xi <= M / 6 := by
  by_contra hn
  have ht : 0 < 2 * ell + defect + xi - M / 6 := by linarith
  have hp := mul_pos (by linarith : 0 < 6 * kappa - 1) ht
  nlinarith [hslot, hreserve]

theorem balanced_long_nonnegative (M total ell kappa xi defect : Real)
    (hM : 0 <= M) (hell : 0 <= ell) (hk : 1 / 2 < kappa)
    (hxi : 0 <= xi)
    (hreserve :
      2 * (6 * kappa - 1) * xi + 2 * (6 * kappa + 1) * defect <=
        (2 * kappa - 1) * M)
    (hlarge : 5 * M / 6 - defect <= total + ell)
    (hcap : total + ell + (6 * kappa - 1) * ell <= M) :
    0 <= total - M / 4 := by
  have hs := small_slot_reserve M ell kappa xi defect hk
    (slot_budget M total ell kappa defect hlarge hcap) hreserve
  linarith

theorem deleted_cases (M total short along ell z kappa xi defect reflected : Real)
    (hM : 0 <= M) (hs : 0 <= short) (hsM : short <= M / 4)
    (hell : 0 <= ell) (hz : 0 <= z) (hze : z <= ell)
    (hk : 1 / 2 < kappa) (hxi : 0 <= xi) (hd : 0 <= defect)
    (hreserve :
      2 * (6 * kappa - 1) * xi + 2 * (6 * kappa + 1) * defect <=
        (2 * kappa - 1) * M)
    (hlarge : 5 * M / 6 - defect <= total + ell)
    (hcap : total + ell + (6 * kappa - 1) * ell <= M)
    (halong : max 0 along <= total - M / 4)
    (href : reflected <= max 0 (M - along + xi)) :
    Or
      (And (short + max 0 along + z <= 5 * M / 6)
        (short + max 0 along + 6 * kappa * z <= M))
      (And (0 < along)
        (And (reflected + short + z <= 5 * M / 6)
          (reflected + short + 6 * kappa * z <= M))) := by
  have hslot := slot_budget M total ell kappa defect hlarge hcap
  have hsmall := small_slot_reserve M ell kappa xi defect hk hslot hreserve
  have hzslot : (6 * kappa - 1) * z <= M / 6 + defect :=
    (mul_le_mul_of_nonneg_left hze (by linarith)).trans hslot
  by_cases hlo : short + max 0 along + z <= 5 * M / 6
  case pos =>
    apply Or.inl
    refine And.intro hlo ?_
    have hzcap := mul_le_mul_of_nonneg_left hze (by linarith : 0 <= 6 * kappa)
    nlinarith
  case neg =>
    have hhigh : 5 * M / 6 < short + max 0 along + z := lt_of_not_ge hlo
    have ha : 0 < along := by
      by_contra hn
      rw [max_eq_left (le_of_not_gt hn)] at hhigh
      linarith
    rw [max_eq_right ha.le] at hhigh
    apply Or.inr
    refine And.intro ha ?_
    by_cases hr : 0 <= M - along + xi
    case pos =>
      rw [max_eq_right hr] at href
      constructor <;> nlinarith
    case neg =>
      rw [max_eq_left (le_of_not_ge hr)] at href
      constructor <;> nlinarith

/-- Positive reserves exist for every fixed kappa > 1/2, uniformly in M >= rho. -/
theorem positive_reserve (rho kappa : Real) (hrho : 0 < rho) (hk : 1 / 2 < kappa) :
    let e := rho * (2 * kappa - 1) / (48 * kappa)
    And (0 < e) (forall M : Real, rho <= M ->
      2 * (6 * kappa - 1) * e + 2 * (6 * kappa + 1) * e <=
        (2 * kappa - 1) * M) := by
  dsimp only
  have hk0 : 0 < kappa := by linarith
  have hg : 0 < 2 * kappa - 1 := by linarith
  refine And.intro (by positivity) ?_
  intro M hM
  have heq :
      2 * (6 * kappa - 1) * (rho * (2 * kappa - 1) / (48 * kappa)) +
        2 * (6 * kappa + 1) * (rho * (2 * kappa - 1) / (48 * kappa)) =
      rho * (2 * kappa - 1) / 2 := by
    field_simp
    <;> ring
  rw [heq]
  nlinarith [mul_le_mul_of_nonneg_left hM hg.le]


open HeckeFamily CenteredMomentEnergyBands
open CenteredMomentEnergyReferenceState CenteredMomentEnergyReferenceDeletionBudget
open CenteredMomentEnergyReferenceDeletionCapacity
open scoped BigOperators

/-- The actual deleted prime-ideal windows satisfy the same enlarged range. -/
theorem deleted_reference_cases (Z M X1 X2 ell z kappa xi e reflected : Real)
    (hZ : 1 < Z) (hM : 0 <= M) (hX1 : 0 < X1) (hX2 : 0 < X2)
    (hell : 0 <= ell) (hz : 0 <= z) (hze : z <= ell)
    (hk : 1 / 2 < kappa) (hxi : 0 <= xi) (he : 0 <= e)
    (hreserve :
      2 * (6 * kappa - 1) * xi + 2 * (6 * kappa + 1) * e <=
        (2 * kappa - 1) * M)
    (hlarge : 5 * M / 6 - e <= Real.logb Z (X1 * X2) + ell)
    (hcap : Real.logb Z (X1 * X2) + ell + (6 * kappa - 1) * ell <= M)
    (D1 D2 : Finset (Ideal HeckeFamily.O))
    (hD1 : forall I, Membership.mem D1 I -> Prime I)
    (hD2 : forall I, Membership.mem D2 I -> Prime I)
    (href : reflected <= max 0 (M - Real.logb Z
      (comparisonSecond Z M X1 X2 / ((Finset.prod D2 (fun I => I)).absNorm : Real)) + xi)) :
    let short := length Z
      (comparisonFirst Z M / ((Finset.prod D1 (fun I => I)).absNorm : Real))
    let long := length Z
      (comparisonSecond Z M X1 X2 / ((Finset.prod D2 (fun I => I)).absNorm : Real))
    let along := Real.logb Z
      (comparisonSecond Z M X1 X2 / ((Finset.prod D2 (fun I => I)).absNorm : Real))
    Or (And (short + long + z <= 5 * M / 6) (short + long + 6 * kappa * z <= M))
      (And (0 < along)
        (And (reflected + short + z <= 5 * M / 6)
          (reflected + short + 6 * kappa * z <= M))) := by
  dsimp only
  have hb := balanced_long_nonnegative M (Real.logb Z (X1 * X2)) ell kappa xi e
    hM hell hk hxi hreserve hlarge hcap
  have hp := comparison_positive Z M X1 X2 (zero_lt_one.trans hZ) hX1 hX2
  have hl : Real.logb Z (comparisonSecond Z M X1 X2) =
      Real.logb Z (X1 * X2) - M / 4 := by
    rw [comparison_second_power Z M X1 X2 hZ hX1 hX2,
      Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne']
  have hy : 1 <= comparisonSecond Z M X1 X2 := by
    rw [comparison_second_power Z M X1 X2 hZ hX1 hX2]
    exact Real.one_le_rpow hZ.le hb
  have hn := product_norm_ge_one D2 hD2
  have hlongpos := div_pos hp.2 (zero_lt_one.trans_le hn)
  have hshort := deleted_short_length Z M hZ hM D1 hD1
  have hshort0 := length_nonneg Z
    (comparisonFirst Z M / ((Finset.prod D1 (fun I => I)).absNorm : Real)) hZ
  have hlong : length Z
      (comparisonSecond Z M X1 X2 / ((Finset.prod D2 (fun I => I)).absNorm : Real)) <=
      Real.logb Z (X1 * X2) - M / 4 := by
    rw [<- hl]
    exact Real.logb_le_logb_of_le hZ
      (zero_lt_one.trans_le (le_max_left 1 _))
      (max_le hy (div_le_self hp.2.le hn))
  have hlength := CenteredMomentEnergyReferenceLowBranchGeometry.length_eq_max_log Z
    (comparisonSecond Z M X1 X2 / ((Finset.prod D2 (fun I => I)).absNorm : Real))
    hZ hlongpos
  rw [hlength] at hlong
  have hh := deleted_cases M (Real.logb Z (X1 * X2))
    (length Z (comparisonFirst Z M / ((Finset.prod D1 (fun I => I)).absNorm : Real)))
    (Real.logb Z (comparisonSecond Z M X1 X2 /
      ((Finset.prod D2 (fun I => I)).absNorm : Real)))
    ell z kappa xi e reflected hM hshort0 hshort hell hz hze hk hxi he
    hreserve hlarge hcap hlong href
  simpa only [hlength] using hh

theorem deleted_reference_window (Z M X1 X2 ell z kappa xi e : Real)
    (hZ : 1 < Z) (hM : 0 <= M) (hX1 : 0 < X1) (hX2 : 0 < X2)
    (hell : 0 <= ell) (hz : 0 <= z) (hze : z <= ell)
    (hk : 1 / 2 < kappa) (hxi : 0 <= xi) (he : 0 <= e)
    (hreserve :
      2 * (6 * kappa - 1) * xi + 2 * (6 * kappa + 1) * e <=
        (2 * kappa - 1) * M)
    (hlarge : 5 * M / 6 - e <= Real.logb Z (X1 * X2) + ell)
    (hcap : Real.logb Z (X1 * X2) + ell + (6 * kappa - 1) * ell <= M)
    (D1 D2 : Finset (Ideal HeckeFamily.O))
    (hD1 : forall I, Membership.mem D1 I -> Prime I)
    (hD2 : forall I, Membership.mem D2 I -> Prime I) :
    let short := length Z
      (comparisonFirst Z M / ((Finset.prod D1 (fun I => I)).absNorm : Real))
    let long := length Z
      (comparisonSecond Z M X1 X2 / ((Finset.prod D2 (fun I => I)).absNorm : Real))
    let along := Real.logb Z
      (comparisonSecond Z M X1 X2 / ((Finset.prod D2 (fun I => I)).absNorm : Real))
    Or (And (short + long + z <= 5 * M / 6) (short + long + 6 * kappa * z <= M))
      (And (0 < along)
        (forall x : Real,
          Membership.mem (Set.Icc 0 (max 0 (M - along + xi) * Real.log Z)) x ->
          And (length Z (Real.exp x) + short + z <= 5 * M / 6)
            (length Z (Real.exp x) + short + 6 * kappa * z <= M))) := by
  dsimp only
  let along := Real.logb Z
    (comparisonSecond Z M X1 X2 / ((Finset.prod D2 (fun I => I)).absNorm : Real))
  have hh := deleted_reference_cases Z M X1 X2 ell z kappa xi e
    (max 0 (M - along + xi)) hZ hM hX1 hX2 hell hz hze hk hxi he hreserve
    hlarge hcap D1 D2 hD1 hD2 le_rfl
  dsimp only at hh
  rcases hh with hd | hr
  case inl =>
    exact Or.inl hd
  case inr =>
    apply Or.inr
    refine And.intro hr.1 ?_
    intro x hx
    have hw := CenteredMomentEnergyReferenceLowWindow.reflection_window_length Z
      (max 0 (M - along + xi)) x hZ (le_max_left _ _) hx
    exact And.intro (by linarith [hr.2.1, hw.1]) (by linarith [hr.2.2, hw.1])

end PrimeFactorOscillations.QRHSourceRange

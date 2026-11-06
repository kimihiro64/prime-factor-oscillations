/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.CarmichaelEqualityBudget

/-!
# Pointwise saturation and support at equality

The full signed equality saturates each reference floor and leaves no positive
weight outside the two reference images and their reflections.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations.CarmichaelDyadicSharpness.ReflectedSpectrum

open CarmichaelWeightedSignal

variable {I : Type*} [Fintype I]

theorem fifth_equality_two_weight (S : ReflectedSpectrum I (7 / 8))
    (hEq : S.carrierMass =
      39 * S.weakUnitMass + S.weakRepeatedUnitMass + 4 * S.weakFifthUnitMass)
    (i : I) (hi : Membership.mem S.weakIndices i) :
    S.multiplicitySupportWeight (S.referenceIndex 2 i) =
      4 * S.unitMass i + 2 * S.fifthUnitAt i := by
  classical
  have hWeak : forall j, Membership.mem S.weakIndices j ->
      (S.mult j : Real) <= 2 * (S.rowOrder 2 j : Real) := by
    intro j hj
    exact (Finset.mem_filter.mp hj).2.1
  have hImage : S.quadraticReferenceImage.sum S.multiplicitySupportWeight =
      S.weakIndices.sum (fun j => S.multiplicitySupportWeight (S.referenceIndex 2 j)) := by
    change (S.weakIndices.image (S.referenceIndex 2)).sum _ = _
    exact Finset.sum_image (fun j hj k hk h =>
      S.referenceIndex_injOn S.weakIndices 2 (by norm_num) hWeak hj hk h)
  have hSum := (S.fifth_equality_reference_sums hEq).1
  rw [hImage] at hSum
  have hDiff : S.weakIndices.sum (fun j =>
      S.multiplicitySupportWeight (S.referenceIndex 2 j) -
        (4 * S.unitMass j + 2 * S.fifthUnitAt j)) = 0 := by
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib,
      <- Finset.mul_sum, <- Finset.mul_sum]
    change S.weakIndices.sum (fun j => S.multiplicitySupportWeight (S.referenceIndex 2 j)) -
      (4 * S.weakUnitMass + 2 * S.weakFifthUnitMass) = 0
    linarith
  have hSingle := Finset.single_le_sum
    (fun j hj => sub_nonneg.mpr (S.reference_two_fifth_weight_le j hj)) hi
  rw [hDiff] at hSingle
  linarith [S.reference_two_fifth_weight_le i hi]

theorem fifth_equality_four_weight (S : ReflectedSpectrum I (7 / 8))
    (hEq : S.carrierMass =
      39 * S.weakUnitMass + S.weakRepeatedUnitMass + 4 * S.weakFifthUnitMass)
    (i : I) (hi : Membership.mem S.weakIndices i) :
    S.multiplicitySupportWeight (S.referenceIndex 4 i) = 16 * S.unitMass i := by
  classical
  have hWeak : forall j, Membership.mem S.weakIndices j ->
      (S.mult j : Real) <= 4 * (S.rowOrder 4 j : Real) := by
    intro j hj
    exact (Finset.mem_filter.mp hj).2.2
  have hFloor : forall j, Membership.mem S.weakIndices j ->
      16 * S.unitMass j <= S.multiplicitySupportWeight (S.referenceIndex 4 j) := by
    intro j hj
    have hr := S.weak_reference_four_lower j hj
    have h := S.multiplicitySupportWeight_right (S.referenceIndex 4 j) (by linarith)
    rw [S.reference_unit_mass_eq 4 (by norm_num) j (hWeak j hj)] at h
    norm_num at h
    exact h
  have hImage : S.quarticReferenceImage.sum S.multiplicitySupportWeight =
      S.weakIndices.sum (fun j => S.multiplicitySupportWeight (S.referenceIndex 4 j)) := by
    change (S.weakIndices.image (S.referenceIndex 4)).sum _ = _
    exact Finset.sum_image (fun j hj k hk h =>
      S.referenceIndex_injOn S.weakIndices 4 (by norm_num) hWeak hj hk h)
  have hSum := (S.fifth_equality_reference_sums hEq).2
  rw [hImage] at hSum
  have hDiff : S.weakIndices.sum (fun j =>
      S.multiplicitySupportWeight (S.referenceIndex 4 j) - 16 * S.unitMass j) = 0 := by
    rw [Finset.sum_sub_distrib, <- Finset.mul_sum]
    change S.weakIndices.sum (fun j => S.multiplicitySupportWeight (S.referenceIndex 4 j)) -
      16 * S.weakUnitMass = 0
    linarith
  have hSingle := Finset.single_le_sum
    (fun j hj => sub_nonneg.mpr (hFloor j hj)) hi
  rw [hDiff] at hSingle
  linarith [hFloor i hi]

theorem jointReferenceImage_disjoint_mirror (S : ReflectedSpectrum I (7 / 8))
    [DecidableEq I] :
    Disjoint S.jointReferenceImage (S.jointReferenceImage.image S.mirror) := by
  classical
  apply Finset.disjoint_left.mpr
  intro k hk hm
  choose j hj he using Finset.mem_image.mp hm
  have hK := S.jointReferenceImage_right k hk
  have hJ := S.jointReferenceImage_right j hj
  have hPoint := S.point_mirror j
  rw [he] at hPoint
  have hRe := congrArg Complex.re hPoint
  rw [zeroReflection_re] at hRe
  linarith

theorem jointReferenceImage_mirror_weight_sum (S : ReflectedSpectrum I (7 / 8))
    [DecidableEq I] :
    (S.jointReferenceImage.image S.mirror).sum S.multiplicitySupportWeight =
      S.jointReferenceImage.sum S.multiplicitySupportWeight := by
  classical
  rw [Finset.sum_image (fun i _ j _ h => S.mirror_injective h)]
  exact Finset.sum_congr rfl (fun i _ => S.multiplicitySupportWeight_mirror i)

theorem fifth_equality_outside_weight_zero (S : ReflectedSpectrum I (7 / 8))
    (hEq : S.carrierMass =
      39 * S.weakUnitMass + S.weakRepeatedUnitMass + 4 * S.weakFifthUnitMass)
    (i : I) (hi : Not (Membership.mem S.jointReferenceImage i))
    (hmi : Not (Membership.mem S.jointReferenceImage (S.mirror i))) :
    S.multiplicitySupportWeight i = 0 := by
  classical
  let B := S.jointReferenceImage
  let D := Union.union B (B.image S.mirror)
  have hiD : Not (Membership.mem D i) := by
    intro h
    rcases Finset.mem_union.mp h with h | h
    . exact hi h
    . choose j hj he using Finset.mem_image.mp h
      apply hmi
      rw [<- he, S.mirror_involutive j]
      exact hj
  have hTotal : Finset.univ.sum S.multiplicitySupportWeight =
      D.sum S.multiplicitySupportWeight := by
    dsimp only [D, B]
    rw [Finset.sum_union S.jointReferenceImage_disjoint_mirror,
      S.jointReferenceImage_mirror_weight_sum]
    linarith [S.fifth_equality_reflection_sum hEq]
  have hBound := Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.subset_univ (insert i D))
    (fun j _ _ => S.multiplicitySupportWeight_nonneg j)
  rw [Finset.sum_insert hiD, <- hTotal] at hBound
  exact le_antisymm (by linarith) (S.multiplicitySupportWeight_nonneg i)

end PrimeFactorOscillations.CarmichaelDyadicSharpness.ReflectedSpectrum


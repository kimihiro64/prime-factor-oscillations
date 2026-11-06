/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.CarmichaelFifthSupport

/-!
# Complete reference-image budgets at fifth-tail equality

Equality in the full signed carrier bound forces both actual reference-image
sums to attain their floors. No compensation charge or reflected atom is
discarded.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations.CarmichaelDyadicSharpness.ReflectedSpectrum

variable {I : Type*} [Fintype I]

def quadraticReferenceImage (S : ReflectedSpectrum I (7 / 8)) : Finset I := by
  classical
  exact S.weakIndices.image (S.referenceIndex 2)

def quarticReferenceImage (S : ReflectedSpectrum I (7 / 8)) : Finset I := by
  classical
  exact S.weakIndices.image (S.referenceIndex 4)

def jointReferenceImage (S : ReflectedSpectrum I (7 / 8)) : Finset I := by
  classical
  exact Union.union S.quadraticReferenceImage S.quarticReferenceImage

theorem quadraticReference_weight_lower (S : ReflectedSpectrum I (7 / 8)) :
    4 * S.weakUnitMass + 2 * S.weakFifthUnitMass <=
      S.quadraticReferenceImage.sum S.multiplicitySupportWeight := by
  classical
  have hWeak : forall i, Membership.mem S.weakIndices i ->
      (S.mult i : Real) <= 2 * (S.rowOrder 2 i : Real) := by
    intro i hi
    exact (Finset.mem_filter.mp hi).2.1
  change 4 * S.weakIndices.sum S.unitMass + 2 * S.weakIndices.sum S.fifthUnitAt <=
    (S.weakIndices.image (S.referenceIndex 2)).sum S.multiplicitySupportWeight
  rw [Finset.mul_sum, Finset.mul_sum, <- Finset.sum_add_distrib,
    Finset.sum_image (fun i hi j hj h =>
      S.referenceIndex_injOn S.weakIndices 2 (by norm_num) hWeak hi hj h)]
  exact Finset.sum_le_sum (fun i hi => S.reference_two_fifth_weight_le i hi)

theorem quarticReference_weight_lower (S : ReflectedSpectrum I (7 / 8)) :
    16 * S.weakUnitMass <=
      S.quarticReferenceImage.sum S.multiplicitySupportWeight := by
  classical
  have hWeak : forall i, Membership.mem S.weakIndices i ->
      (S.mult i : Real) <= 4 * (S.rowOrder 4 i : Real) := by
    intro i hi
    exact (Finset.mem_filter.mp hi).2.2
  change 16 * S.weakIndices.sum S.unitMass <=
    (S.weakIndices.image (S.referenceIndex 4)).sum S.multiplicitySupportWeight
  rw [Finset.mul_sum, Finset.sum_image (fun i hi j hj h =>
    S.referenceIndex_injOn S.weakIndices 4 (by norm_num) hWeak hi hj h)]
  apply Finset.sum_le_sum
  intro i hi
  have hr := S.weak_reference_four_lower i hi
  have h := S.multiplicitySupportWeight_right (S.referenceIndex 4 i) (by linarith)
  rw [S.reference_unit_mass_eq 4 (by norm_num) i (hWeak i hi)] at h
  norm_num at h
  exact h

theorem jointReferenceImages_disjoint (S : ReflectedSpectrum I (7 / 8))
    [DecidableEq I] :
    Disjoint S.quadraticReferenceImage S.quarticReferenceImage := by
  classical
  simpa only [quadraticReferenceImage, quarticReferenceImage,
    Finset.disjoint_left, Finset.mem_image] using S.weak_reference_images_disjoint

theorem jointReferenceImage_right (S : ReflectedSpectrum I (7 / 8)) :
    forall i, Membership.mem S.jointReferenceImage i -> 1 / 2 < (S.point i).re := by
  classical
  intro i hi
  apply Or.elim (Finset.mem_union.mp hi)
  . intro h2
    choose j hj he using Finset.mem_image.mp h2
    rw [<- he]
    exact (S.weak_reference_two_bounds j hj).1
  . intro h4
    choose j hj he using Finset.mem_image.mp h4
    rw [<- he]
    have h := S.weak_reference_four_lower j hj
    linarith

theorem fifth_equality_weight_sum (S : ReflectedSpectrum I (7 / 8))
    (hEq : S.carrierMass = 39 * S.weakUnitMass + S.weakRepeatedUnitMass +
      4 * S.weakFifthUnitMass) :
    Finset.univ.sum S.multiplicitySupportWeight =
      40 * S.weakUnitMass + 4 * S.weakFifthUnitMass := by
  rw [S.sum_multiplicitySupportWeight]
  have hw := S.weakMass_eq_unit_add_excess
  have ht := S.totalMass_eq_weakMass_add_carrierMass
  linarith

theorem fifth_equality_reference_sums (S : ReflectedSpectrum I (7 / 8))
    (hEq : S.carrierMass = 39 * S.weakUnitMass + S.weakRepeatedUnitMass +
      4 * S.weakFifthUnitMass) :
    S.quadraticReferenceImage.sum S.multiplicitySupportWeight =
        4 * S.weakUnitMass + 2 * S.weakFifthUnitMass /\
      S.quarticReferenceImage.sum S.multiplicitySupportWeight = 16 * S.weakUnitMass := by
  classical
  have hTwo := S.quadraticReference_weight_lower
  have hFour := S.quarticReference_weight_lower
  have hTotal := S.reflected_right_weight_le S.multiplicitySupportWeight
    S.multiplicitySupportWeight_nonneg S.multiplicitySupportWeight_mirror
    S.jointReferenceImage S.jointReferenceImage_right
  rw [jointReferenceImage, Finset.sum_union S.jointReferenceImages_disjoint,
    S.fifth_equality_weight_sum hEq] at hTotal
  exact And.intro (by linarith) (by linarith)

theorem fifth_equality_reflection_sum (S : ReflectedSpectrum I (7 / 8))
    (hEq : S.carrierMass = 39 * S.weakUnitMass + S.weakRepeatedUnitMass +
      4 * S.weakFifthUnitMass) :
    Finset.univ.sum S.multiplicitySupportWeight =
      2 * S.jointReferenceImage.sum S.multiplicitySupportWeight := by
  classical
  have hs := S.fifth_equality_reference_sums hEq
  rw [S.fifth_equality_weight_sum hEq, jointReferenceImage,
    Finset.sum_union S.jointReferenceImages_disjoint, hs.1, hs.2]
  ring

end PrimeFactorOscillations.CarmichaelDyadicSharpness.ReflectedSpectrum

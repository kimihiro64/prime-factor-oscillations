/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.CarmichaelMultiplicitySupport

/-!
# Joint multiplicity-support comparison for complete compensated carriers

The reference-image budget uses the nonnegative symmetric charged weight.
No multiplicity cap is assumed. Both reference images and all reflection
charges remain coupled through the final carrier inequality.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations.CarmichaelDyadicSharpness.ReflectedSpectrum

open DirichletCompensatedProbe CarmichaelWeightedSignal

variable {I : Type*} [Fintype I] {sigma : Real}

theorem reference_unit_mass_eq (S : ReflectedSpectrum I sigma)
    (a : Real) (ha : 0 < a) (i : I)
    (hWeak : (S.mult i : Real) <= a * (S.rowOrder a i : Real)) :
    S.unitMass (S.referenceIndex a i) = a ^ 2 * S.unitMass i := by
  have hIm : (S.point (S.referenceIndex a i)).im = (S.point i).im / a := by
    rw [S.point_referenceIndex a i hWeak]
    exact (eq_div_iff ha.ne').mpr (powerMap_im_identity a ha (S.point i))
  unfold unitMass
  rw [hIm]
  field_simp [ha.ne', (S.im_pos i).ne']

theorem multiplicity_support_budget (S : ReflectedSpectrum I (7 / 8)) :
    40 * S.weakUnitMass + S.weakExcessMass + S.weakRepeatedUnitMass <= S.totalMass := by
  classical
  let U := S.weakIndices
  let B := Union.union (U.image (S.referenceIndex 2)) (U.image (S.referenceIndex 4))
  have hWeak2 : forall i, Membership.mem U i ->
      (S.mult i : Real) <= 2 * (S.rowOrder 2 i : Real) := by
    intro i hi
    exact (Finset.mem_filter.mp hi).2.1
  have hWeak4 : forall i, Membership.mem U i ->
      (S.mult i : Real) <= 4 * (S.rowOrder 4 i : Real) := by
    intro i hi
    exact (Finset.mem_filter.mp hi).2.2
  have hTwo : 4 * S.weakUnitMass <=
      (U.image (S.referenceIndex 2)).sum S.multiplicitySupportWeight := by
    change 4 * U.sum S.unitMass <= _
    rw [Finset.mul_sum, Finset.sum_image
      (fun i hi j hj h => S.referenceIndex_injOn U 2 (by norm_num) hWeak2 hi hj h)]
    apply Finset.sum_le_sum
    intro i hi
    have h := S.multiplicitySupportWeight_right (S.referenceIndex 2 i)
      (S.weak_reference_two_bounds i hi).1
    rw [S.reference_unit_mass_eq 2 (by norm_num) i (hWeak2 i hi)] at h
    norm_num at h
    exact h
  have hFour : 16 * S.weakUnitMass <=
      (U.image (S.referenceIndex 4)).sum S.multiplicitySupportWeight := by
    change 16 * U.sum S.unitMass <= _
    rw [Finset.mul_sum, Finset.sum_image
      (fun i hi j hj h => S.referenceIndex_injOn U 4 (by norm_num) hWeak4 hi hj h)]
    apply Finset.sum_le_sum
    intro i hi
    have hr := S.weak_reference_four_lower i hi
    have h := S.multiplicitySupportWeight_right (S.referenceIndex 4 i) (by linarith)
    rw [S.reference_unit_mass_eq 4 (by norm_num) i (hWeak4 i hi)] at h
    norm_num at h
    exact h
  have hDisjoint : Disjoint (U.image (S.referenceIndex 2))
      (U.image (S.referenceIndex 4)) := S.weak_reference_images_disjoint
  have hB : 20 * S.weakUnitMass <= B.sum S.multiplicitySupportWeight := by
    dsimp only [B]
    rw [Finset.sum_union hDisjoint]
    linarith
  have hRight : forall i, Membership.mem B i -> 1 / 2 < (S.point i).re := by
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
  have hTotal := S.reflected_right_weight_le S.multiplicitySupportWeight
    S.multiplicitySupportWeight_nonneg S.multiplicitySupportWeight_mirror B hRight
  rw [S.sum_multiplicitySupportWeight] at hTotal
  linarith

theorem carrier_multiplicity_support_bound (S : ReflectedSpectrum I (7 / 8)) :
    39 * S.weakUnitMass + S.weakRepeatedUnitMass <= S.carrierMass := by
  have hb := S.multiplicity_support_budget
  have hw := S.weakMass_eq_unit_add_excess
  have ht := S.totalMass_eq_weakMass_add_carrierMass
  linarith

theorem carrier_affine_support_bound (S : ReflectedSpectrum I (7 / 8))
    (a b : Real) (ha : a <= 39) (hab : a + b <= 40) :
    a * S.weakUnitMass + b * S.weakRepeatedUnitMass <= S.carrierMass := by
  have hq := S.weakRepeatedUnitMass_nonneg
  have hpq := S.weakRepeatedUnitMass_le_unit
  have h1 := mul_le_mul_of_nonneg_right ha (sub_nonneg.mpr hpq)
  have h2 := mul_le_mul_of_nonneg_right hab hq
  have hc := S.carrier_multiplicity_support_bound
  nlinarith

end PrimeFactorOscillations.CarmichaelDyadicSharpness.ReflectedSpectrum

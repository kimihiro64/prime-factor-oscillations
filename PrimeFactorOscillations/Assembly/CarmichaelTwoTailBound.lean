/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.CarmichaelOffcriticalTail

/-!
# The joint fifth-order and offcritical-triple carrier budget

The two signed adjustments give D>=V3 and D+3V3>=16R5. Nonnegative
interpolation then proves every coefficient pair in the proposed sharp cone.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations.CarmichaelDyadicSharpness.ReflectedSpectrum

variable {I : Type*} [Fintype I]

theorem joint_adjusted_weight_budget (S : ReflectedSpectrum I (7 / 8))
    (f : I -> Real) (e : Real) (hNonneg : forall i, 0 <= f i)
    (hMirror : forall i, f (S.mirror i) = f i)
    (hUnit : forall i, 1 / 2 < (S.point i).re -> S.unitMass i <= f i)
    (hTwo : forall i, Membership.mem S.weakIndices i ->
      4 * S.unitMass i + e * S.fifthUnitAt i <= f (S.referenceIndex 2 i)) :
    40 * S.weakUnitMass + 2 * e * S.weakFifthUnitMass <= Finset.univ.sum f := by
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
  have hTwoSum : 4 * S.weakUnitMass + e * S.weakFifthUnitMass <=
      (U.image (S.referenceIndex 2)).sum f := by
    change 4 * U.sum S.unitMass + e * U.sum S.fifthUnitAt <= _
    rw [Finset.mul_sum, Finset.mul_sum, <- Finset.sum_add_distrib,
      Finset.sum_image
        (fun i hi j hj h => S.referenceIndex_injOn U 2 (by norm_num) hWeak2 hi hj h)]
    exact Finset.sum_le_sum (fun i hi => hTwo i hi)
  have hFour : 16 * S.weakUnitMass <= (U.image (S.referenceIndex 4)).sum f := by
    change 16 * U.sum S.unitMass <= _
    rw [Finset.mul_sum, Finset.sum_image
      (fun i hi j hj h => S.referenceIndex_injOn U 4 (by norm_num) hWeak4 hi hj h)]
    apply Finset.sum_le_sum
    intro i hi
    have hr := S.weak_reference_four_lower i hi
    have h := hUnit (S.referenceIndex 4 i) (by linarith)
    rw [S.reference_unit_mass_eq 4 (by norm_num) i (hWeak4 i hi)] at h
    norm_num at h
    exact h
  have hDisjoint : Disjoint (U.image (S.referenceIndex 2))
      (U.image (S.referenceIndex 4)) := S.weak_reference_images_disjoint
  have hB : 20 * S.weakUnitMass + e * S.weakFifthUnitMass <= B.sum f := by
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
  have hTotal := S.reflected_right_weight_le f hNonneg hMirror B hRight
  linarith

theorem carrier_offTriple_bound (S : ReflectedSpectrum I (7 / 8)) :
    39 * S.weakUnitMass + S.weakRepeatedUnitMass + S.weakOffTripleUnitMass <=
      S.carrierMass := by
  have hb := S.joint_adjusted_weight_budget (S.offTripleAdjustedWeight (-1)) 0
    S.offTripleMinusWeight_nonneg (S.offTripleAdjustedWeight_mirror (-1))
    S.offTripleMinusWeight_right (by
      intro i hi
      have h := S.offTripleMinusWeight_right (S.referenceIndex 2 i)
        (S.weak_reference_two_bounds i hi).1
      have hw := (Finset.mem_filter.mp hi).2.1
      rw [S.reference_unit_mass_eq 2 (by norm_num) i hw] at h
      norm_num at h
      simpa only [zero_mul, add_zero] using h)
  rw [S.sum_offTripleAdjustedWeight] at hb
  have hw := S.weakMass_eq_unit_add_excess
  have ht := S.totalMass_eq_weakMass_add_carrierMass
  linarith

theorem reference_two_fifth_plus_weight_le (S : ReflectedSpectrum I (7 / 8))
    (i : I) (hi : Membership.mem S.weakIndices i) :
    4 * S.unitMass i + 8 * S.fifthUnitAt i <=
      S.offTripleAdjustedWeight 3 (S.referenceIndex 2 i) := by
  classical
  have hWeak := (Finset.mem_filter.mp hi).2.1
  have hRight := (S.weak_reference_two_bounds i hi).1
  have hUnit := S.reference_unit_mass_eq 2 (by norm_num) i hWeak
  norm_num at hUnit
  by_cases h5 : 5 <= S.mult i
  . have hRef := S.rowOrder_referenceIndex 2 i hWeak
    have hNatWeak : S.mult i <= 2 * S.mult (S.referenceIndex 2 i) := by
      have h := hWeak
      rw [hRef] at h
      exact_mod_cast h
    have hm : 3 <= S.mult (S.referenceIndex 2 i) := by omega
    have h := S.offTriplePlusWeight_right_triple (S.referenceIndex 2 i) hRight hm
    rw [hUnit] at h
    simp only [fifthUnitAt, if_pos h5]
    linarith
  . have h := S.offTriplePlusWeight_right (S.referenceIndex 2 i) hRight
    rw [hUnit] at h
    simpa only [fifthUnitAt, if_neg h5, mul_zero, add_zero] using h

theorem carrier_fifth_offTriple_bound (S : ReflectedSpectrum I (7 / 8)) :
    39 * S.weakUnitMass + S.weakRepeatedUnitMass + 16 * S.weakFifthUnitMass <=
      S.carrierMass + 3 * S.weakOffTripleUnitMass := by
  have hb := S.joint_adjusted_weight_budget (S.offTripleAdjustedWeight 3) 8
    S.offTriplePlusWeight_nonneg (S.offTripleAdjustedWeight_mirror 3)
    S.offTriplePlusWeight_right S.reference_two_fifth_plus_weight_le
  rw [S.sum_offTripleAdjustedWeight] at hb
  have hw := S.weakMass_eq_unit_add_excess
  have ht := S.totalMass_eq_weakMass_add_carrierMass
  linarith

theorem carrier_two_tail_bound (S : ReflectedSpectrum I (7 / 8))
    (a b : Real) (ha : a <= 16) (hb : b <= 1) (hab : a + 4 * b <= 4) :
    39 * S.weakUnitMass + S.weakRepeatedUnitMass +
        a * S.weakFifthUnitMass + b * S.weakOffTripleUnitMass <= S.carrierMass := by
  have h1 := S.carrier_offTriple_bound
  have h2 := S.carrier_fifth_offTriple_bound
  have hR := S.weakFifthUnitMass_nonneg
  have hV := S.weakOffTripleUnitMass_nonneg
  by_cases hLow : b <= -3
  . have hA := mul_le_mul_of_nonneg_right ha hR
    have hB := mul_le_mul_of_nonneg_right hLow hV
    linarith
  . have hMix1 := mul_le_mul_of_nonneg_left h1 (by linarith : 0 <= b + 3)
    have hMix2 := mul_le_mul_of_nonneg_left h2 (by linarith : 0 <= 1 - b)
    have hA := mul_le_mul_of_nonneg_right hab hR
    nlinarith

theorem carrier_sixteen_fifth_of_no_offTriple (S : ReflectedSpectrum I (7 / 8))
    (hZero : S.weakOffTripleUnitMass = 0) :
    39 * S.weakUnitMass + S.weakRepeatedUnitMass + 16 * S.weakFifthUnitMass <=
      S.carrierMass := by
  simpa only [hZero, mul_zero, add_zero] using S.carrier_fifth_offTriple_bound

theorem offTriple_eq_four_fifth_of_fifth_equality (S : ReflectedSpectrum I (7 / 8))
    (hEq : S.carrierMass = 39 * S.weakUnitMass + S.weakRepeatedUnitMass +
      4 * S.weakFifthUnitMass) :
    S.weakOffTripleUnitMass = 4 * S.weakFifthUnitMass := by
  have h1 := S.carrier_offTriple_bound
  have h2 := S.carrier_fifth_offTriple_bound
  linarith

end PrimeFactorOscillations.CarmichaelDyadicSharpness.ReflectedSpectrum

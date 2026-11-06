/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.CarmichaelEqualityBudget
import PrimeFactorOscillations.Assembly.CarmichaelGlobalExcess

/-!
# A global multiplicity-profile carrier bound

The complete offcritical excess above three and the common-weak ninth tail
fit together with the sharp fifth tail in one signed reflection budget.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations.CarmichaelDyadicSharpness.ReflectedSpectrum

variable {I : Type*} [Fintype I] {sigma : Real}

def ninthUnitAt (S : ReflectedSpectrum I sigma) (i : I) : Real :=
  if 9 <= S.mult i then S.unitMass i else 0

def weakNinthUnitMass (S : ReflectedSpectrum I sigma) : Real :=
  S.weakIndices.sum S.ninthUnitAt

omit [Fintype I] in
theorem ninthUnitAt_nonneg (S : ReflectedSpectrum I sigma) (i : I) :
    0 <= S.ninthUnitAt i := by
  unfold ninthUnitAt
  split_ifs
  . exact S.unitMass_nonneg i
  . exact le_refl _

theorem weakNinthUnitMass_nonneg (S : ReflectedSpectrum I sigma) :
    0 <= S.weakNinthUnitMass :=
  Finset.sum_nonneg (fun i _ => S.ninthUnitAt_nonneg i)

theorem reference_two_global_excess_floor (S : ReflectedSpectrum I (7 / 8))
    (i : I) (hi : Membership.mem S.weakIndices i) :
    4 * S.unitMass i + 2 * S.fifthUnitAt i <=
      S.globalExcessWeight (S.referenceIndex 2 i) := by
  have hw := (Finset.mem_filter.mp hi).2.1
  have hu := S.reference_unit_mass_eq 2 (by norm_num) i hw
  norm_num at hu
  have hr := (S.weak_reference_two_bounds i hi).1
  by_cases h5 : 5 <= S.mult i
  . have ho := S.rowOrder_referenceIndex 2 i hw
    rw [ho] at hw
    have hn : S.mult i <= 2 * S.mult (S.referenceIndex 2 i) := by exact_mod_cast hw
    have h3 : 3 <= S.mult (S.referenceIndex 2 i) := by omega
    have hf := S.globalExcessWeight_right_three (S.referenceIndex 2 i) hr h3
    rw [hu] at hf
    simp only [fifthUnitAt, ite_eq_left h5]
    linarith
  . have hf := S.globalExcessWeight_right (S.referenceIndex 2 i) hr
    rw [hu] at hf
    simpa only [fifthUnitAt, ite_eq_right h5, mul_zero, add_zero] using hf

theorem reference_four_global_excess_floor (S : ReflectedSpectrum I (7 / 8))
    (i : I) (hi : Membership.mem S.weakIndices i) :
    16 * S.unitMass i + 8 * S.ninthUnitAt i <=
      S.globalExcessWeight (S.referenceIndex 4 i) := by
  have hw := (Finset.mem_filter.mp hi).2.2
  have hu := S.reference_unit_mass_eq 4 (by norm_num) i hw
  norm_num at hu
  have hrl := S.weak_reference_four_lower i hi
  have hr : 1 / 2 < (S.point (S.referenceIndex 4 i)).re := by linarith
  by_cases h9 : 9 <= S.mult i
  . have ho := S.rowOrder_referenceIndex 4 i hw
    rw [ho] at hw
    have hn : S.mult i <= 4 * S.mult (S.referenceIndex 4 i) := by exact_mod_cast hw
    have h3 : 3 <= S.mult (S.referenceIndex 4 i) := by omega
    have hf := S.globalExcessWeight_right_three (S.referenceIndex 4 i) hr h3
    rw [hu] at hf
    simp only [ninthUnitAt, ite_eq_left h9]
    linarith
  . have hf := S.globalExcessWeight_right (S.referenceIndex 4 i) hr
    rw [hu] at hf
    simpa only [ninthUnitAt, ite_eq_right h9, mul_zero, add_zero] using hf

theorem global_excess_budget (S : ReflectedSpectrum I (7 / 8)) :
    40 * S.weakUnitMass + S.weakExcessMass + S.weakRepeatedUnitMass +
      4 * S.weakFifthUnitMass + 16 * S.weakNinthUnitMass +
        S.globalOffcriticalExcess <= S.totalMass := by
  classical
  have hw2 : forall i, Membership.mem S.weakIndices i ->
      (S.mult i : Real) <= 2 * (S.rowOrder 2 i : Real) := by
    intro i hi
    exact (Finset.mem_filter.mp hi).2.1
  have hw4 : forall i, Membership.mem S.weakIndices i ->
      (S.mult i : Real) <= 4 * (S.rowOrder 4 i : Real) := by
    intro i hi
    exact (Finset.mem_filter.mp hi).2.2
  have hTwo : 4 * S.weakUnitMass + 2 * S.weakFifthUnitMass <=
      S.quadraticReferenceImage.sum S.globalExcessWeight := by
    change 4 * S.weakIndices.sum S.unitMass + 2 * S.weakIndices.sum S.fifthUnitAt <=
      (S.weakIndices.image (S.referenceIndex 2)).sum S.globalExcessWeight
    rw [Finset.mul_sum, Finset.mul_sum, <- Finset.sum_add_distrib,
      Finset.sum_image (fun i hi j hj h =>
        S.referenceIndex_injOn S.weakIndices 2 (by norm_num) hw2 hi hj h)]
    exact Finset.sum_le_sum (fun i hi => S.reference_two_global_excess_floor i hi)
  have hFour : 16 * S.weakUnitMass + 8 * S.weakNinthUnitMass <=
      S.quarticReferenceImage.sum S.globalExcessWeight := by
    change 16 * S.weakIndices.sum S.unitMass + 8 * S.weakIndices.sum S.ninthUnitAt <=
      (S.weakIndices.image (S.referenceIndex 4)).sum S.globalExcessWeight
    rw [Finset.mul_sum, Finset.mul_sum, <- Finset.sum_add_distrib,
      Finset.sum_image (fun i hi j hj h =>
        S.referenceIndex_injOn S.weakIndices 4 (by norm_num) hw4 hi hj h)]
    exact Finset.sum_le_sum (fun i hi => S.reference_four_global_excess_floor i hi)
  have hTotal := S.reflected_right_weight_le S.globalExcessWeight
    S.globalExcessWeight_nonneg S.globalExcessWeight_mirror S.jointReferenceImage
    S.jointReferenceImage_right
  rw [jointReferenceImage, Finset.sum_union S.jointReferenceImages_disjoint,
    S.sum_globalExcessWeight] at hTotal
  linarith

theorem carrier_global_excess_bound (S : ReflectedSpectrum I (7 / 8)) :
    39 * S.weakUnitMass + S.weakRepeatedUnitMass +
      4 * S.weakFifthUnitMass + 16 * S.weakNinthUnitMass +
        S.globalOffcriticalExcess <= S.carrierMass := by
  have h := S.global_excess_budget
  have hw := S.weakMass_eq_unit_add_excess
  have ht := S.totalMass_eq_weakMass_add_carrierMass
  linarith

theorem offcritical_order_excess_le (S : ReflectedSpectrum I sigma)
    (i : I) (hCenter : Not ((S.point i).re = 1 / 2)) :
    ((S.mult i - 3 : Nat) : Real) * S.unitMass i <= S.globalOffcriticalExcess := by
  rcases lt_or_gt_of_ne hCenter with hLeft | hRight
  . have h := Finset.single_le_sum (fun j _ => S.offcriticalExcessAt_nonneg j)
      (Finset.mem_univ i)
    change S.offcriticalExcessAt i <= S.globalOffcriticalExcess at h
    have hi : S.offcriticalExcessAt i =
        ((S.mult i - 3 : Nat) : Real) * S.unitMass i := by
      unfold offcriticalExcessAt
      exact ite_eq_left hLeft
    rwa [hi] at h
  . have h := Finset.single_le_sum (fun j _ => S.offcriticalExcessAt_nonneg j)
      (Finset.mem_univ (S.mirror i))
    rwa [S.offcriticalExcessAt_mirror_right i hRight] at h

theorem offcritical_order_excess_le_carrier_remainder (S : ReflectedSpectrum I (7 / 8))
    (i : I) (hCenter : Not ((S.point i).re = 1 / 2)) :
    ((S.mult i - 3 : Nat) : Real) * S.unitMass i <=
      S.carrierMass - 39 * S.weakUnitMass - S.weakRepeatedUnitMass -
        4 * S.weakFifthUnitMass - 16 * S.weakNinthUnitMass := by
  have h := S.offcritical_order_excess_le i hCenter
  have hb := S.carrier_global_excess_bound
  linarith

theorem globalOffcriticalExcess_eq_zero_iff (S : ReflectedSpectrum I sigma) :
    S.globalOffcriticalExcess = 0 <->
      forall i, Not ((S.point i).re = 1 / 2) -> S.mult i <= 3 := by
  constructor
  . intro hz i hi
    have h := S.offcritical_order_excess_le i hi
    rw [hz] at h
    by_contra hn
    have hd : 1 <= S.mult i - 3 := by omega
    have hdr : (1 : Real) <= ((S.mult i - 3 : Nat) : Real) := by exact_mod_cast hd
    have hm := mul_le_mul_of_nonneg_right hdr (S.unitMass_nonneg i)
    have hp : 0 < S.unitMass i := by
      unfold unitMass
      exact div_pos (by norm_num) (pow_pos (S.im_pos i) 2)
    linarith
  . intro h
    unfold globalOffcriticalExcess
    apply Finset.sum_eq_zero
    intro i hi
    by_cases hc : (S.point i).re = 1 / 2
    . exact S.offcriticalExcessAt_eq_zero_of_half_le i (by rw [hc])
    . exact S.offcriticalExcessAt_eq_zero_of_order_le_three i (h i hc)

theorem offcritical_order_le_three_of_zero_remainder (S : ReflectedSpectrum I (7 / 8))
    (hEq : S.carrierMass = 39 * S.weakUnitMass + S.weakRepeatedUnitMass +
      4 * S.weakFifthUnitMass + 16 * S.weakNinthUnitMass) :
    forall i, Not ((S.point i).re = 1 / 2) -> S.mult i <= 3 := by
  have hb := S.carrier_global_excess_bound
  have hn := S.globalOffcriticalExcess_nonneg
  have hz : S.globalOffcriticalExcess = 0 := by linarith
  exact S.globalOffcriticalExcess_eq_zero_iff.mp hz

end PrimeFactorOscillations.CarmichaelDyadicSharpness.ReflectedSpectrum


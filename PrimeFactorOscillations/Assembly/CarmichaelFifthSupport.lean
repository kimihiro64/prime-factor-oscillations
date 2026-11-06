/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.CarmichaelMultiplicitySupportBound

/-!
# Fifth-multiplicity stability of the joint carrier comparison

An order at least five forces its quadratic reference order to be at least
three. The retained symmetric weight then supplies an extra half unit at
that reference, giving four source units after the complete reflection
budget. Every compensation charge and reference image is retained.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations.CarmichaelDyadicSharpness.ReflectedSpectrum

variable {I : Type*} {sigma : Real}

def fifthUnitAt (S : ReflectedSpectrum I sigma) (i : I) : Real :=
  if 5 <= S.mult i then S.unitMass i else 0

theorem fifthUnitAt_nonneg (S : ReflectedSpectrum I sigma) (i : I) :
    0 <= S.fifthUnitAt i := by
  unfold fifthUnitAt
  split_ifs
  . exact S.unitMass_nonneg i
  . exact le_refl 0

variable [Fintype I]

def weakFifthUnitMass (S : ReflectedSpectrum I sigma) : Real :=
  S.weakIndices.sum S.fifthUnitAt

theorem weakFifthUnitMass_nonneg (S : ReflectedSpectrum I sigma) :
    0 <= S.weakFifthUnitMass :=
  Finset.sum_nonneg (fun i _ => S.fifthUnitAt_nonneg i)

theorem multiplicitySupportWeight_right_half_mass (S : ReflectedSpectrum I (7 / 8))
    (i : I) (hRight : 1 / 2 < (S.point i).re) :
    S.mass i / 2 <= S.multiplicitySupportWeight i := by
  classical
  have hNot : Not (Membership.mem S.weakIndices i) := by
    intro hi
    exact (not_lt_of_ge (S.weak_re_le_half i hi)) hRight
  have hCharge : S.multiplicitySupportCharge i = 0 := by
    simp only [multiplicitySupportCharge, ite_eq_right hNot]
  have hj := S.multiplicitySupportCharge_le (S.mirror i)
  rw [S.multiplicitySupportCost_mirror i] at hj
  have hc := S.multiplicitySupportCost_le_mass i
  unfold multiplicitySupportWeight
  rw [hCharge]
  linarith

theorem reference_two_fifth_weight_le (S : ReflectedSpectrum I (7 / 8))
    (i : I) (hi : Membership.mem S.weakIndices i) :
    4 * S.unitMass i + 2 * S.fifthUnitAt i <=
      S.multiplicitySupportWeight (S.referenceIndex 2 i) := by
  classical
  have hWeak : (S.mult i : Real) <= 2 * (S.rowOrder 2 i : Real) :=
    (Finset.mem_filter.mp hi).2.1
  have hRight := (S.weak_reference_two_bounds i hi).1
  have hUnit := S.reference_unit_mass_eq 2 (by norm_num) i hWeak
  norm_num at hUnit
  by_cases h5 : 5 <= S.mult i
  . have hRef := S.rowOrder_referenceIndex 2 i hWeak
    have hNatWeak : S.mult i <= 2 * S.mult (S.referenceIndex 2 i) := by
      have h := hWeak
      rw [hRef] at h
      exact_mod_cast h
    have hmNat : 3 <= S.mult (S.referenceIndex 2 i) := by omega
    have hm : (3 : Real) <= (S.mult (S.referenceIndex 2 i) : Real) := by
      exact_mod_cast hmNat
    have hFraction := div_le_div_of_nonneg_right hm
      (sq_nonneg (S.point (S.referenceIndex 2 i)).im)
    have hMass : 3 * S.unitMass (S.referenceIndex 2 i) <=
        S.mass (S.referenceIndex 2 i) := by
      unfold unitMass mass
      simpa only [div_eq_mul_inv, one_mul] using hFraction
    rw [hUnit] at hMass
    have hHalf := S.multiplicitySupportWeight_right_half_mass (S.referenceIndex 2 i) hRight
    simp only [fifthUnitAt, ite_eq_left h5]
    linarith
  . have h := S.multiplicitySupportWeight_right (S.referenceIndex 2 i) hRight
    rw [hUnit] at h
    simpa only [fifthUnitAt, ite_eq_right h5, mul_zero, add_zero] using h

theorem fifth_support_budget (S : ReflectedSpectrum I (7 / 8)) :
    40 * S.weakUnitMass + S.weakExcessMass + S.weakRepeatedUnitMass +
        4 * S.weakFifthUnitMass <= S.totalMass := by
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
  have hTwo : 4 * S.weakUnitMass + 2 * S.weakFifthUnitMass <=
      (U.image (S.referenceIndex 2)).sum S.multiplicitySupportWeight := by
    change 4 * U.sum S.unitMass + 2 * U.sum S.fifthUnitAt <= _
    rw [Finset.mul_sum, Finset.mul_sum, <- Finset.sum_add_distrib,
      Finset.sum_image
        (fun i hi j hj h => S.referenceIndex_injOn U 2 (by norm_num) hWeak2 hi hj h)]
    apply Finset.sum_le_sum
    intro i hi
    exact S.reference_two_fifth_weight_le i hi
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
  have hB : 20 * S.weakUnitMass + 2 * S.weakFifthUnitMass <=
      B.sum S.multiplicitySupportWeight := by
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

theorem carrier_fifth_support_bound (S : ReflectedSpectrum I (7 / 8)) :
    39 * S.weakUnitMass + S.weakRepeatedUnitMass +
        4 * S.weakFifthUnitMass <= S.carrierMass := by
  have hb := S.fifth_support_budget
  have hw := S.weakMass_eq_unit_add_excess
  have ht := S.totalMass_eq_weakMass_add_carrierMass
  linarith

theorem weakFifthUnitMass_eq_zero_iff (S : ReflectedSpectrum I sigma) :
    S.weakFifthUnitMass = 0 <->
      forall i, Membership.mem S.weakIndices i -> S.mult i <= 4 := by
  classical
  constructor
  . intro hZero i hi
    by_contra hn
    have h5 : 5 <= S.mult i := by omega
    have hTerm : S.fifthUnitAt i <= S.weakFifthUnitMass :=
      Finset.single_le_sum (fun j _ => S.fifthUnitAt_nonneg j) hi
    rw [hZero] at hTerm
    simp only [fifthUnitAt, ite_eq_left h5] at hTerm
    have hPos : 0 < S.unitMass i :=
      div_pos (by norm_num) (pow_pos (S.im_pos i) 2)
    exact (not_lt_of_ge hTerm) hPos
  . intro hSmall
    unfold weakFifthUnitMass
    apply Finset.sum_eq_zero
    intro i hi
    have hNot : Not (5 <= S.mult i) := by
      have h := hSmall i hi
      omega
    simp only [fifthUnitAt, ite_eq_right hNot]

theorem weak_order_le_four_of_joint_equality (S : ReflectedSpectrum I (7 / 8))
    (hEquality : S.carrierMass = 39 * S.weakUnitMass + S.weakRepeatedUnitMass) :
    forall i, Membership.mem S.weakIndices i -> S.mult i <= 4 := by
  have hb := S.carrier_fifth_support_bound
  have hr := S.weakFifthUnitMass_nonneg
  have hZero : S.weakFifthUnitMass = 0 := by linarith
  exact S.weakFifthUnitMass_eq_zero_iff.mp hZero

end PrimeFactorOscillations.CarmichaelDyadicSharpness.ReflectedSpectrum

/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.CarmichaelEqualitySaturation

/-!
# Multiplicity and centrality forced by sharp equality

Every noncentral atom has order at most three. A common weak atom of order at
least five is central, has order five or six, and forces the three weak branches
needed for the smallest equality configuration.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations.CarmichaelDyadicSharpness.ReflectedSpectrum

open CarmichaelWeightedSignal

variable {I : Type*} [Fintype I]

theorem equality_unitMass_pos (S : ReflectedSpectrum I (7 / 8)) (i : I) :
    0 < S.unitMass i := by
  unfold unitMass
  exact one_div_pos.mpr (sq_pos_of_pos (S.im_pos i))

theorem equality_mass_eq_mult_unit (S : ReflectedSpectrum I (7 / 8)) (i : I) :
    S.mass i = (S.mult i : Real) * S.unitMass i := by
  unfold mass unitMass
  ring

theorem fifthUnitAt_le_unitMass (S : ReflectedSpectrum I (7 / 8)) (i : I) :
    S.fifthUnitAt i <= S.unitMass i := by
  unfold fifthUnitAt
  split_ifs
  . exact le_refl _
  . exact S.unitMass_nonneg i

theorem right_weight_eq_mass_of_not_mirror_weak (S : ReflectedSpectrum I (7 / 8))
    (i : I) (hRight : 1 / 2 < (S.point i).re)
    (hMirror : Not (Membership.mem S.weakIndices (S.mirror i))) :
    S.multiplicitySupportWeight i = S.mass i := by
  classical
  have hNot : Not (Membership.mem S.weakIndices i) := by
    intro hi
    exact (not_lt_of_ge (S.weak_re_le_half i hi)) hRight
  simp only [multiplicitySupportWeight, multiplicitySupportCharge,
    if_neg hNot, if_neg hMirror, sub_zero]

theorem right_mirror_weak_of_weight_lt_mass (S : ReflectedSpectrum I (7 / 8))
    (i : I) (hRight : 1 / 2 < (S.point i).re)
    (hLt : S.multiplicitySupportWeight i < S.mass i) :
    Membership.mem S.weakIndices (S.mirror i) := by
  classical
  by_contra h
  rw [S.right_weight_eq_mass_of_not_mirror_weak i hRight h] at hLt
  exact (lt_irrefl _) hLt

theorem right_order_le_three_of_weight_le (S : ReflectedSpectrum I (7 / 8))
    (i : I) (hRight : 1 / 2 < (S.point i).re)
    (hFloor : S.multiplicitySupportWeight i <= (3 / 2) * S.unitMass i) :
    S.mult i <= 3 := by
  have hHalf := S.multiplicitySupportWeight_right_half_mass i hRight
  rw [S.equality_mass_eq_mult_unit i] at hHalf
  have hu := S.equality_unitMass_pos i
  by_contra h
  have hNat : 4 <= S.mult i := by omega
  have hReal : (4 : Real) <= (S.mult i : Real) := by exact_mod_cast hNat
  nlinarith

theorem right_order_le_two_of_weight_eq_unit (S : ReflectedSpectrum I (7 / 8))
    (i : I) (hRight : 1 / 2 < (S.point i).re)
    (hFloor : S.multiplicitySupportWeight i = S.unitMass i) :
    S.mult i <= 2 := by
  have hHalf := S.multiplicitySupportWeight_right_half_mass i hRight
  rw [S.equality_mass_eq_mult_unit i, hFloor] at hHalf
  have hu := S.equality_unitMass_pos i
  by_contra h
  have hNat : 3 <= S.mult i := by omega
  have hReal : (3 : Real) <= (S.mult i : Real) := by exact_mod_cast hNat
  nlinarith

theorem fifth_equality_two_order_le_three (S : ReflectedSpectrum I (7 / 8))
    (hEq : S.carrierMass =
      39 * S.weakUnitMass + S.weakRepeatedUnitMass + 4 * S.weakFifthUnitMass)
    (i : I) (hi : Membership.mem S.weakIndices i) :
    S.mult (S.referenceIndex 2 i) <= 3 := by
  have hw := (Finset.mem_filter.mp hi).2.1
  have hu := S.reference_unit_mass_eq 2 (by norm_num) i hw
  norm_num at hu
  apply S.right_order_le_three_of_weight_le (S.referenceIndex 2 i)
    (S.weak_reference_two_bounds i hi).1
  rw [S.fifth_equality_two_weight hEq i hi, hu]
  linarith [S.fifthUnitAt_le_unitMass i]

theorem fifth_equality_four_order_le_two (S : ReflectedSpectrum I (7 / 8))
    (hEq : S.carrierMass =
      39 * S.weakUnitMass + S.weakRepeatedUnitMass + 4 * S.weakFifthUnitMass)
    (i : I) (hi : Membership.mem S.weakIndices i) :
    S.mult (S.referenceIndex 4 i) <= 2 := by
  have hw := (Finset.mem_filter.mp hi).2.2
  have hu := S.reference_unit_mass_eq 4 (by norm_num) i hw
  norm_num at hu
  have hr := S.weak_reference_four_lower i hi
  apply S.right_order_le_two_of_weight_eq_unit (S.referenceIndex 4 i) (by linarith)
  rw [S.fifth_equality_four_weight hEq i hi, hu]

theorem fifth_equality_image_order_le_three (S : ReflectedSpectrum I (7 / 8))
    (hEq : S.carrierMass =
      39 * S.weakUnitMass + S.weakRepeatedUnitMass + 4 * S.weakFifthUnitMass)
    (i : I) (hi : Membership.mem S.jointReferenceImage i) :
    S.mult i <= 3 := by
  classical
  rcases Finset.mem_union.mp hi with h | h
  . choose j hj he using Finset.mem_image.mp h
    rw [<- he]
    exact S.fifth_equality_two_order_le_three hEq j hj
  . choose j hj he using Finset.mem_image.mp h
    rw [<- he]
    exact (S.fifth_equality_four_order_le_two hEq j hj).trans (by norm_num)

theorem fifth_equality_noncentral_image (S : ReflectedSpectrum I (7 / 8))
    (hEq : S.carrierMass =
      39 * S.weakUnitMass + S.weakRepeatedUnitMass + 4 * S.weakFifthUnitMass)
    (i : I) (hCenter : Not ((S.point i).re = 1 / 2)) :
    Membership.mem S.jointReferenceImage i \/
      Membership.mem S.jointReferenceImage (S.mirror i) := by
  classical
  by_contra h
  have hi : Not (Membership.mem S.jointReferenceImage i) := fun ht => h (Or.inl ht)
  have hm : Not (Membership.mem S.jointReferenceImage (S.mirror i)) := fun ht => h (Or.inr ht)
  have hz := S.fifth_equality_outside_weight_zero hEq i hi hm
  rcases lt_or_gt_of_ne hCenter with hLeft | hRight
  . have hp := congrArg Complex.re (S.point_mirror i)
    rw [zeroReflection_re] at hp
    have hr : 1 / 2 < (S.point (S.mirror i)).re := by linarith
    have hw := S.multiplicitySupportWeight_right (S.mirror i) hr
    rw [S.multiplicitySupportWeight_mirror i, hz] at hw
    linarith [S.equality_unitMass_pos (S.mirror i)]
  . have hw := S.multiplicitySupportWeight_right i hRight
    rw [hz] at hw
    linarith [S.equality_unitMass_pos i]

theorem fifth_equality_noncentral_order_le_three (S : ReflectedSpectrum I (7 / 8))
    (hEq : S.carrierMass =
      39 * S.weakUnitMass + S.weakRepeatedUnitMass + 4 * S.weakFifthUnitMass)
    (i : I) (hCenter : Not ((S.point i).re = 1 / 2)) :
    S.mult i <= 3 := by
  rcases S.fifth_equality_noncentral_image hEq i hCenter with h | h
  . exact S.fifth_equality_image_order_le_three hEq i h
  . have ho := S.fifth_equality_image_order_le_three hEq (S.mirror i) h
    simpa only [S.mult_mirror i] using ho

theorem fifth_equality_high_central (S : ReflectedSpectrum I (7 / 8))
    (hEq : S.carrierMass =
      39 * S.weakUnitMass + S.weakRepeatedUnitMass + 4 * S.weakFifthUnitMass)
    (i : I) (hFive : 5 <= S.mult i) :
    (S.point i).re = 1 / 2 := by
  by_contra h
  have ho := S.fifth_equality_noncentral_order_le_three hEq i h
  omega

theorem fifth_equality_weak_root_order (S : ReflectedSpectrum I (7 / 8))
    (hEq : S.carrierMass =
      39 * S.weakUnitMass + S.weakRepeatedUnitMass + 4 * S.weakFifthUnitMass)
    (i : I) (hi : Membership.mem S.weakIndices i) (hFive : 5 <= S.mult i) :
    S.mult i = 5 \/ S.mult i = 6 := by
  have hw := (Finset.mem_filter.mp hi).2.1
  rw [S.rowOrder_referenceIndex 2 i hw] at hw
  have hNat : S.mult i <= 2 * S.mult (S.referenceIndex 2 i) := by exact_mod_cast hw
  have ho := S.fifth_equality_two_order_le_three hEq i hi
  omega

theorem fifth_equality_weak_fifth_two_order (S : ReflectedSpectrum I (7 / 8))
    (hEq : S.carrierMass =
      39 * S.weakUnitMass + S.weakRepeatedUnitMass + 4 * S.weakFifthUnitMass)
    (i : I) (hi : Membership.mem S.weakIndices i) (hFive : 5 <= S.mult i) :
    S.mult (S.referenceIndex 2 i) = 3 := by
  have hw := (Finset.mem_filter.mp hi).2.1
  rw [S.rowOrder_referenceIndex 2 i hw] at hw
  have hNat : S.mult i <= 2 * S.mult (S.referenceIndex 2 i) := by exact_mod_cast hw
  have ho := S.fifth_equality_two_order_le_three hEq i hi
  omega

theorem fifth_equality_weak_fifth_four_order (S : ReflectedSpectrum I (7 / 8))
    (hEq : S.carrierMass =
      39 * S.weakUnitMass + S.weakRepeatedUnitMass + 4 * S.weakFifthUnitMass)
    (i : I) (hi : Membership.mem S.weakIndices i) (hFive : 5 <= S.mult i) :
    S.mult (S.referenceIndex 4 i) = 2 := by
  have hw := (Finset.mem_filter.mp hi).2.2
  rw [S.rowOrder_referenceIndex 4 i hw] at hw
  have hNat : S.mult i <= 4 * S.mult (S.referenceIndex 4 i) := by exact_mod_cast hw
  have ho := S.fifth_equality_four_order_le_two hEq i hi
  omega

theorem fifth_equality_weak_fifth_two_mirror (S : ReflectedSpectrum I (7 / 8))
    (hEq : S.carrierMass =
      39 * S.weakUnitMass + S.weakRepeatedUnitMass + 4 * S.weakFifthUnitMass)
    (i : I) (hi : Membership.mem S.weakIndices i) (hFive : 5 <= S.mult i) :
    Membership.mem S.weakIndices (S.mirror (S.referenceIndex 2 i)) := by
  have hw := (Finset.mem_filter.mp hi).2.1
  have hu := S.reference_unit_mass_eq 2 (by norm_num) i hw
  norm_num at hu
  have ho := S.fifth_equality_weak_fifth_two_order hEq i hi hFive
  have hf := S.fifth_equality_two_weight hEq i hi
  simp only [fifthUnitAt, if_pos hFive] at hf
  apply S.right_mirror_weak_of_weight_lt_mass (S.referenceIndex 2 i)
    (S.weak_reference_two_bounds i hi).1
  rw [S.equality_mass_eq_mult_unit, ho, hu, hf]
  norm_num
  linarith [S.equality_unitMass_pos i]

theorem fifth_equality_weak_fifth_four_mirror (S : ReflectedSpectrum I (7 / 8))
    (hEq : S.carrierMass =
      39 * S.weakUnitMass + S.weakRepeatedUnitMass + 4 * S.weakFifthUnitMass)
    (i : I) (hi : Membership.mem S.weakIndices i) (hFive : 5 <= S.mult i) :
    Membership.mem S.weakIndices (S.mirror (S.referenceIndex 4 i)) := by
  have hw := (Finset.mem_filter.mp hi).2.2
  have hu := S.reference_unit_mass_eq 4 (by norm_num) i hw
  norm_num at hu
  have ho := S.fifth_equality_weak_fifth_four_order hEq i hi hFive
  have hf := S.fifth_equality_four_weight hEq i hi
  have hr := S.weak_reference_four_lower i hi
  apply S.right_mirror_weak_of_weight_lt_mass (S.referenceIndex 4 i) (by linarith)
  rw [S.equality_mass_eq_mult_unit, ho, hu, hf]
  norm_num
  linarith [S.equality_unitMass_pos i]

theorem fifth_equality_weak_three_two_order (S : ReflectedSpectrum I (7 / 8))
    (hEq : S.carrierMass =
      39 * S.weakUnitMass + S.weakRepeatedUnitMass + 4 * S.weakFifthUnitMass)
    (i : I) (hi : Membership.mem S.weakIndices i) (hThree : S.mult i = 3) :
    S.mult (S.referenceIndex 2 i) = 2 := by
  have hw := (Finset.mem_filter.mp hi).2.1
  have hu := S.reference_unit_mass_eq 2 (by norm_num) i hw
  norm_num at hu
  have hf := S.fifth_equality_two_weight hEq i hi
  have hNot : Not (5 <= S.mult i) := by omega
  simp only [fifthUnitAt, if_neg hNot, mul_zero, add_zero] at hf
  have ho := S.right_order_le_two_of_weight_eq_unit (S.referenceIndex 2 i)
    (S.weak_reference_two_bounds i hi).1 (by rw [hf, hu])
  rw [S.rowOrder_referenceIndex 2 i hw] at hw
  have hNat : S.mult i <= 2 * S.mult (S.referenceIndex 2 i) := by exact_mod_cast hw
  omega

theorem fifth_equality_weak_three_two_mirror (S : ReflectedSpectrum I (7 / 8))
    (hEq : S.carrierMass =
      39 * S.weakUnitMass + S.weakRepeatedUnitMass + 4 * S.weakFifthUnitMass)
    (i : I) (hi : Membership.mem S.weakIndices i) (hThree : S.mult i = 3) :
    Membership.mem S.weakIndices (S.mirror (S.referenceIndex 2 i)) := by
  have hw := (Finset.mem_filter.mp hi).2.1
  have hu := S.reference_unit_mass_eq 2 (by norm_num) i hw
  norm_num at hu
  have ho := S.fifth_equality_weak_three_two_order hEq i hi hThree
  have hf := S.fifth_equality_two_weight hEq i hi
  have hNot : Not (5 <= S.mult i) := by omega
  simp only [fifthUnitAt, if_neg hNot, mul_zero, add_zero] at hf
  apply S.right_mirror_weak_of_weight_lt_mass (S.referenceIndex 2 i)
    (S.weak_reference_two_bounds i hi).1
  rw [S.equality_mass_eq_mult_unit, ho, hu, hf]
  norm_num
  linarith [S.equality_unitMass_pos i]

end PrimeFactorOscillations.CarmichaelDyadicSharpness.ReflectedSpectrum


/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.CarmichaelFiniteSpectrum

/-!
# The universal quadratic-quartic finite-spectrum carrier bound

In the closed strip [1/8, 7/8], the two reference images of the common weak
rows are disjoint and lie strictly to the right of the critical line.
Their reflected images retain all natural multiplicities. The complete
finite mass ledger therefore forces the strict-sign carrier fraction 11/12.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations.CarmichaelDyadicSharpness.ReflectedSpectrum

open DirichletCompensatedProbe CarmichaelWeightedSignal

variable {I : Type*} [Fintype I]

theorem weak_re_le_half (S : ReflectedSpectrum I (7 / 8)) (i : I)
    (hi : Membership.mem S.weakIndices i) : (S.point i).re <= 1 / 2 := by
  classical
  have hw := (Finset.mem_filter.mp hi).2.2
  have h := powerMap_real_identity 4 (by norm_num) (S.point i)
  rw [<- S.point_referenceIndex 4 i hw] at h
  have hu := S.re_upper (S.referenceIndex 4 i)
  linarith

theorem weak_reference_two_bounds (S : ReflectedSpectrum I (7 / 8)) (i : I)
    (hi : Membership.mem S.weakIndices i) :
    1 / 2 < (S.point (S.referenceIndex 2 i)).re /\
      (S.point (S.referenceIndex 2 i)).re <= 3 / 4 := by
  classical
  have hw := (Finset.mem_filter.mp hi).2.1
  have h := powerMap_real_identity 2 (by norm_num) (S.point i)
  rw [<- S.point_referenceIndex 2 i hw] at h
  have hl := S.re_lower i
  have hu := S.weak_re_le_half i hi
  constructor <;> linarith

theorem weak_reference_four_lower (S : ReflectedSpectrum I (7 / 8)) (i : I)
    (hi : Membership.mem S.weakIndices i) :
    25 / 32 <= (S.point (S.referenceIndex 4 i)).re := by
  classical
  have hw := (Finset.mem_filter.mp hi).2.2
  have h := powerMap_real_identity 4 (by norm_num) (S.point i)
  rw [<- S.point_referenceIndex 4 i hw] at h
  have hl := S.re_lower i
  linarith

theorem weak_reference_images_disjoint [DecidableEq I] (S : ReflectedSpectrum I (7 / 8)) :
    Disjoint (S.weakIndices.image (S.referenceIndex 2))
      (S.weakIndices.image (S.referenceIndex 4)) := by
  classical
  apply Finset.disjoint_left.mpr
  intro k hk2 hk4
  choose i hi he2 using Finset.mem_image.mp hk2
  choose j hj he4 using Finset.mem_image.mp hk4
  have hTwo := (S.weak_reference_two_bounds i hi).2
  have hFour := S.weak_reference_four_lower j hj
  rw [he2] at hTwo
  rw [he4] at hFour
  linarith

theorem reflected_right_mass_le (S : ReflectedSpectrum I (7 / 8)) (B : Finset I)
    (hRight : forall i, Membership.mem B i -> 1 / 2 < (S.point i).re) :
    2 * B.sum S.mass <= S.totalMass := by
  classical
  have hDisjoint : Disjoint B (B.image S.mirror) := by
    apply Finset.disjoint_left.mpr
    intro k hk hm
    choose j hj he using Finset.mem_image.mp hm
    have hK := hRight k hk
    have hJ := hRight j hj
    have hPoint := S.point_mirror j
    rw [he] at hPoint
    have hRe := congrArg Complex.re hPoint
    rw [zeroReflection_re] at hRe
    linarith
  have hImage : (B.image S.mirror).sum S.mass = B.sum S.mass := by
    rw [Finset.sum_image (fun i _ j _ h => S.mirror_injective h)]
    apply Finset.sum_congr rfl
    intro i hi
    exact S.mass_mirror i
  have hSum := Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.subset_univ (Union.union B (B.image S.mirror)))
    (fun i _ _ => S.mass_nonneg i)
  rw [Finset.sum_union hDisjoint, hImage] at hSum
  change 2 * B.sum S.mass <= Finset.univ.sum S.mass
  linarith

theorem twelve_weakMass_le_totalMass (S : ReflectedSpectrum I (7 / 8)) :
    12 * S.weakMass <= S.totalMass := by
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
  have hTwo : 2 * S.weakMass <= (U.image (S.referenceIndex 2)).sum S.mass := by
    change 2 * U.sum S.mass <= _
    rw [Finset.mul_sum, Finset.sum_image
      (fun i hi j hj h => S.referenceIndex_injOn U 2 (by norm_num) hWeak2 hi hj h)]
    exact Finset.sum_le_sum (fun i hi => S.mass_le_reference 2 (by norm_num) i (hWeak2 i hi))
  have hFour : 4 * S.weakMass <= (U.image (S.referenceIndex 4)).sum S.mass := by
    change 4 * U.sum S.mass <= _
    rw [Finset.mul_sum, Finset.sum_image
      (fun i hi j hj h => S.referenceIndex_injOn U 4 (by norm_num) hWeak4 hi hj h)]
    exact Finset.sum_le_sum (fun i hi => S.mass_le_reference 4 (by norm_num) i (hWeak4 i hi))
  have hDisjoint : Disjoint (U.image (S.referenceIndex 2))
      (U.image (S.referenceIndex 4)) := S.weak_reference_images_disjoint
  have hB : 6 * S.weakMass <= B.sum S.mass := by
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
  have hTotal := S.reflected_right_mass_le B hRight
  linarith

theorem totalMass_eq_weakMass_add_carrierMass (S : ReflectedSpectrum I (7 / 8)) :
    S.totalMass = S.weakMass + S.carrierMass := by
  classical
  unfold totalMass weakMass carrierMass weakIndices carrierIndices
  rw [Finset.sum_filter, Finset.sum_filter, <- Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hw : (S.mult i : Real) <= 2 * (S.rowOrder 2 i : Real) /\
      (S.mult i : Real) <= 4 * (S.rowOrder 4 i : Real)
  . have hc : Not (2 * (S.rowOrder 2 i : Real) < (S.mult i : Real) \/
        4 * (S.rowOrder 4 i : Real) < (S.mult i : Real)) := by
      intro h
      exact h.elim (fun h2 => (not_lt_of_ge hw.1) h2) (fun h4 => (not_lt_of_ge hw.2) h4)
    simp only [ite_eq_left hw, ite_eq_right hc, add_zero]
  . have hc : 2 * (S.rowOrder 2 i : Real) < (S.mult i : Real) \/
        4 * (S.rowOrder 4 i : Real) < (S.mult i : Real) := by
      by_cases h2 : (S.mult i : Real) <= 2 * (S.rowOrder 2 i : Real)
      . exact Or.inr (lt_of_not_ge (fun h4 => hw (And.intro h2 h4)))
      . exact Or.inl (lt_of_not_ge h2)
    simp only [ite_eq_right hw, ite_eq_left hc, zero_add]

theorem eleven_twelfths_carrier_bound (S : ReflectedSpectrum I (7 / 8)) :
    (11 / 12 : Real) * S.totalMass <= S.carrierMass := by
  have hWeak := S.twelve_weakMass_le_totalMass
  have hSplit := S.totalMass_eq_weakMass_add_carrierMass
  linarith

end PrimeFactorOscillations.CarmichaelDyadicSharpness.ReflectedSpectrum

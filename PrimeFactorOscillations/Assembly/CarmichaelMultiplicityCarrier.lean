/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.CarmichaelFiniteCarrier

/-!
# Compensated carrier deficits certify excess multiplicity

Positive natural reference orders give quadratic height gains for unit
mass. The two complete reference images and their reflections force a
39/40 carrier bound after charging the exact common-weak excess mass.
In particular a strict deficit certifies a repeated common-weak atom.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations.CarmichaelDyadicSharpness.ReflectedSpectrum

open DirichletCompensatedProbe CarmichaelWeightedSignal

variable {I : Type*} {sigma : Real}

def unitMass (S : ReflectedSpectrum I sigma) (i : I) : Real :=
  1 / (S.point i).im ^ 2

def excessMassAt (S : ReflectedSpectrum I sigma) (i : I) : Real :=
  ((S.mult i : Real) - 1) / (S.point i).im ^ 2

theorem unitMass_nonneg (S : ReflectedSpectrum I sigma) (i : I) :
    0 <= S.unitMass i := div_nonneg (by norm_num) (sq_nonneg _)

theorem excessMassAt_nonneg (S : ReflectedSpectrum I sigma) (i : I) :
    0 <= S.excessMassAt i := by
  have hm : (1 : Real) <= (S.mult i : Real) := by
    exact_mod_cast Nat.succ_le_of_lt (S.mult_pos i)
  exact div_nonneg (sub_nonneg.mpr hm) (sq_nonneg _)

theorem mass_eq_unit_add_excess (S : ReflectedSpectrum I sigma) (i : I) :
    S.mass i = S.unitMass i + S.excessMassAt i := by
  unfold mass unitMass excessMassAt
  ring

variable [Fintype I]

def weakUnitMass (S : ReflectedSpectrum I sigma) : Real :=
  S.weakIndices.sum S.unitMass

def weakExcessMass (S : ReflectedSpectrum I sigma) : Real :=
  S.weakIndices.sum S.excessMassAt

def totalExcessMass (S : ReflectedSpectrum I sigma) : Real :=
  Finset.univ.sum S.excessMassAt

theorem weakExcessMass_nonneg (S : ReflectedSpectrum I sigma) :
    0 <= S.weakExcessMass :=
  Finset.sum_nonneg (fun i _ => S.excessMassAt_nonneg i)

theorem weakExcessMass_le_total (S : ReflectedSpectrum I sigma) :
    S.weakExcessMass <= S.totalExcessMass :=
  Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S.weakIndices)
    (fun i _ _ => S.excessMassAt_nonneg i)

theorem weakMass_eq_unit_add_excess (S : ReflectedSpectrum I sigma) :
    S.weakMass = S.weakUnitMass + S.weakExcessMass := by
  unfold weakMass weakUnitMass weakExcessMass
  rw [<- Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  exact S.mass_eq_unit_add_excess i

theorem reference_unit_mass_le (S : ReflectedSpectrum I sigma)
    (a : Real) (ha : 0 < a) (i : I)
    (hWeak : (S.mult i : Real) <= a * (S.rowOrder a i : Real)) :
    a ^ 2 * S.unitMass i <= S.mass (S.referenceIndex a i) := by
  have hp := S.point_referenceIndex a i hWeak
  have hIm : (S.point (S.referenceIndex a i)).im = (S.point i).im / a := by
    rw [hp]
    exact (eq_div_iff ha.ne').mpr (powerMap_im_identity a ha (S.point i))
  have hm : (1 : Real) <= (S.mult (S.referenceIndex a i) : Real) := by
    exact_mod_cast Nat.succ_le_of_lt (S.mult_pos (S.referenceIndex a i))
  unfold unitMass mass
  rw [hIm]
  calc
    a ^ 2 * (1 / (S.point i).im ^ 2) = 1 / ((S.point i).im / a) ^ 2 := by
      field_simp [ha.ne', (S.im_pos i).ne']
    _ <= (S.mult (S.referenceIndex a i) : Real) / ((S.point i).im / a) ^ 2 :=
      div_le_div_of_nonneg_right hm (sq_nonneg _)

theorem forty_weakUnitMass_le_totalMass (S : ReflectedSpectrum I (7 / 8)) :
    40 * S.weakUnitMass <= S.totalMass := by
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
  have hTwo : 4 * S.weakUnitMass <= (U.image (S.referenceIndex 2)).sum S.mass := by
    change 4 * U.sum S.unitMass <= _
    rw [Finset.mul_sum, Finset.sum_image
      (fun i hi j hj h => S.referenceIndex_injOn U 2 (by norm_num) hWeak2 hi hj h)]
    apply Finset.sum_le_sum
    intro i hi
    have h := S.reference_unit_mass_le 2 (by norm_num) i (hWeak2 i hi)
    norm_num at h
    exact h
  have hFour : 16 * S.weakUnitMass <= (U.image (S.referenceIndex 4)).sum S.mass := by
    change 16 * U.sum S.unitMass <= _
    rw [Finset.mul_sum, Finset.sum_image
      (fun i hi j hj h => S.referenceIndex_injOn U 4 (by norm_num) hWeak4 hi hj h)]
    apply Finset.sum_le_sum
    intro i hi
    have h := S.reference_unit_mass_le 4 (by norm_num) i (hWeak4 i hi)
    norm_num at h
    exact h
  have hDisjoint : Disjoint (U.image (S.referenceIndex 2))
      (U.image (S.referenceIndex 4)) := S.weak_reference_images_disjoint
  have hB : 20 * S.weakUnitMass <= B.sum S.mass := by
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

theorem carrier_excess_bound (S : ReflectedSpectrum I (7 / 8)) :
    (39 / 40 : Real) * S.totalMass <= S.carrierMass + S.weakExcessMass := by
  have hp := S.forty_weakUnitMass_le_totalMass
  have hw := S.weakMass_eq_unit_add_excess
  have hs := S.totalMass_eq_weakMass_add_carrierMass
  linarith

theorem carrier_excess_bound_total (S : ReflectedSpectrum I (7 / 8)) :
    (39 / 40 : Real) * S.totalMass <= S.carrierMass + S.totalExcessMass := by
  have h := S.carrier_excess_bound
  have he := S.weakExcessMass_le_total
  linarith

theorem carrier_max_bound (S : ReflectedSpectrum I (7 / 8)) :
    max ((11 / 12 : Real) * S.totalMass)
      ((39 / 40 : Real) * S.totalMass - S.weakExcessMass) <= S.carrierMass := by
  apply max_le S.eleven_twelfths_carrier_bound
  have h := S.carrier_excess_bound
  linarith

theorem simple_carrier_bound (S : ReflectedSpectrum I (7 / 8))
    (hSimple : forall i : I, S.mult i = 1) :
    (39 / 40 : Real) * S.totalMass <= S.carrierMass := by
  have hZero : S.weakExcessMass = 0 := by
    unfold weakExcessMass
    apply Finset.sum_eq_zero
    intro i hi
    simp only [excessMassAt, hSimple i, Nat.cast_one, sub_self, zero_div]
  have h := S.carrier_excess_bound
  simpa only [hZero, add_zero] using h

theorem repeated_weak_atom_of_deficit (S : ReflectedSpectrum I (7 / 8))
    (hDeficit : S.carrierMass < (39 / 40 : Real) * S.totalMass) :
    exists i : I, Membership.mem S.weakIndices i /\ 2 <= S.mult i := by
  classical
  by_contra hNot
  have hSimpleWeak : forall i, Membership.mem S.weakIndices i -> S.mult i = 1 := by
    intro i hi
    have hSmall : S.mult i < 2 := by
      by_contra hn
      exact hNot (Exists.intro i (And.intro hi (le_of_not_gt hn)))
    have hPos := S.mult_pos i
    omega
  have hZero : S.weakExcessMass = 0 := by
    unfold weakExcessMass
    apply Finset.sum_eq_zero
    intro i hi
    simp only [excessMassAt, hSimpleWeak i hi, Nat.cast_one, sub_self, zero_div]
  have h := S.carrier_excess_bound
  rw [hZero, add_zero] at h
  exact (not_le_of_gt hDeficit) h

end PrimeFactorOscillations.CarmichaelDyadicSharpness.ReflectedSpectrum

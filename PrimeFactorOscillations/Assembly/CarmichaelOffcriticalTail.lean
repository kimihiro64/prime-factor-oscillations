/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.CarmichaelFifthSupport

/-!
# Signed offcritical triple charges

Both original half charges remain in the symmetric weight. Subtracting half
of the offcritical triple pair preserves the right unit floor. Adding three
halves instead gives three units at every right atom of order at least three.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations.CarmichaelDyadicSharpness.ReflectedSpectrum

open DirichletCompensatedProbe CarmichaelWeightedSignal

variable {I : Type*} {sigma : Real} [Fintype I]

theorem unitMass_mirror (S : ReflectedSpectrum I sigma) (i : I) :
    S.unitMass (S.mirror i) = S.unitMass i := by
  unfold unitMass
  rw [S.point_mirror i, zeroReflection_im]

def offTripleUnitAt (S : ReflectedSpectrum I sigma) (i : I) : Real := by
  classical
  exact if Membership.mem S.weakIndices i /\
      (S.point i).re < 1 / 2 /\ 3 <= S.mult i then S.unitMass i else 0

def weakOffTripleUnitMass (S : ReflectedSpectrum I sigma) : Real :=
  Finset.univ.sum S.offTripleUnitAt

def offTripleAdjustedWeight (S : ReflectedSpectrum I sigma) (k : Real) (i : I) : Real :=
  S.multiplicitySupportWeight i +
    k / 2 * (S.offTripleUnitAt i + S.offTripleUnitAt (S.mirror i))

theorem offTripleUnitAt_nonneg (S : ReflectedSpectrum I sigma) (i : I) :
    0 <= S.offTripleUnitAt i := by
  classical
  unfold offTripleUnitAt
  split_ifs
  . exact S.unitMass_nonneg i
  . exact le_refl 0

theorem offTripleUnitAt_le (S : ReflectedSpectrum I sigma) (i : I) :
    S.offTripleUnitAt i <= S.unitMass i := by
  classical
  unfold offTripleUnitAt
  split_ifs
  . exact le_refl _
  . exact S.unitMass_nonneg i

theorem weakOffTripleUnitMass_nonneg (S : ReflectedSpectrum I sigma) :
    0 <= S.weakOffTripleUnitMass :=
  Finset.sum_nonneg (fun i _ => S.offTripleUnitAt_nonneg i)

theorem offTripleUnitAt_eq_zero_of_half_le (S : ReflectedSpectrum I sigma)
    (i : I) (h : 1 / 2 <= (S.point i).re) : S.offTripleUnitAt i = 0 := by
  classical
  unfold offTripleUnitAt
  apply if_neg
  intro ht
  exact (not_lt_of_ge h) ht.2.1

theorem offTripleAdjustedWeight_mirror (S : ReflectedSpectrum I sigma)
    (k : Real) (i : I) :
    S.offTripleAdjustedWeight k (S.mirror i) = S.offTripleAdjustedWeight k i := by
  unfold offTripleAdjustedWeight
  rw [S.multiplicitySupportWeight_mirror, S.mirror_involutive]
  ring

theorem sum_offTripleAdjustedWeight (S : ReflectedSpectrum I sigma) (k : Real) :
    Finset.univ.sum (S.offTripleAdjustedWeight k) =
      S.totalMass - S.weakExcessMass - S.weakRepeatedUnitMass +
        k * S.weakOffTripleUnitMass := by
  classical
  have hUniv : Finset.univ.image S.mirror = (Finset.univ : Finset I) := by
    apply Finset.ext
    intro i
    constructor
    . intro _
      exact Finset.mem_univ i
    . intro _
      exact Finset.mem_image.mpr (Exists.intro (S.mirror i)
        (And.intro (Finset.mem_univ _) (S.mirror_involutive i)))
  have hPerm : Finset.univ.sum (fun i => S.offTripleUnitAt (S.mirror i)) =
      Finset.univ.sum S.offTripleUnitAt := by
    rw [<- Finset.sum_image (fun i _ j _ h => S.mirror_injective h), hUniv]
  unfold offTripleAdjustedWeight
  rw [Finset.sum_add_distrib, <- Finset.mul_sum, Finset.sum_add_distrib,
    hPerm, S.sum_multiplicitySupportWeight]
  unfold weakOffTripleUnitMass
  ring

theorem three_unit_le_mass (S : ReflectedSpectrum I sigma)
    (i : I) (h : 3 <= S.mult i) : 3 * S.unitMass i <= S.mass i := by
  have hm : (3 : Real) <= (S.mult i : Real) := by exact_mod_cast h
  unfold unitMass mass
  have hd := div_le_div_of_nonneg_right hm (sq_nonneg (S.point i).im)
  simpa only [div_eq_mul_inv, one_mul] using hd

theorem offTripleMinusWeight_right (S : ReflectedSpectrum I (7 / 8))
    (i : I) (hRight : 1 / 2 < (S.point i).re) :
    S.unitMass i <= S.offTripleAdjustedWeight (-1) i := by
  classical
  have hz := S.offTripleUnitAt_eq_zero_of_half_le i hRight.le
  have ht := S.offTripleUnitAt_le (S.mirror i)
  rw [S.unitMass_mirror i] at ht
  by_cases h3 : 3 <= S.mult i
  . have hm := S.three_unit_le_mass i h3
    have hw := S.multiplicitySupportWeight_right_half_mass i hRight
    unfold offTripleAdjustedWeight
    rw [hz]
    linarith
  . have hzMirror : S.offTripleUnitAt (S.mirror i) = 0 := by
      unfold offTripleUnitAt
      apply if_neg
      intro ht
      exact h3 (by simpa only [S.mult_mirror i] using ht.2.2)
    have hw := S.multiplicitySupportWeight_right i hRight
    unfold offTripleAdjustedWeight
    rw [hz, hzMirror]
    linarith

theorem offTripleMinusWeight_nonneg (S : ReflectedSpectrum I (7 / 8)) (i : I) :
    0 <= S.offTripleAdjustedWeight (-1) i := by
  have hRe := congrArg Complex.re (S.point_mirror i)
  rw [zeroReflection_re] at hRe
  by_cases hRight : 1 / 2 < (S.point i).re
  . exact (S.unitMass_nonneg i).trans (S.offTripleMinusWeight_right i hRight)
  . by_cases hLeft : (S.point i).re < 1 / 2
    . have hr : 1 / 2 < (S.point (S.mirror i)).re := by linarith
      have h := (S.unitMass_nonneg (S.mirror i)).trans
        (S.offTripleMinusWeight_right (S.mirror i) hr)
      simpa only [S.offTripleAdjustedWeight_mirror] using h
    . have hi : 1 / 2 <= (S.point i).re := le_of_not_gt hLeft
      have hj : 1 / 2 <= (S.point (S.mirror i)).re := by linarith
      unfold offTripleAdjustedWeight
      rw [S.offTripleUnitAt_eq_zero_of_half_le i hi,
        S.offTripleUnitAt_eq_zero_of_half_le (S.mirror i) hj]
      simpa using S.multiplicitySupportWeight_nonneg i

theorem offTriplePlusWeight_nonneg (S : ReflectedSpectrum I sigma) (i : I) :
    0 <= S.offTripleAdjustedWeight 3 i := by
  unfold offTripleAdjustedWeight
  have hf := S.multiplicitySupportWeight_nonneg i
  have hi := S.offTripleUnitAt_nonneg i
  have hj := S.offTripleUnitAt_nonneg (S.mirror i)
  linarith

theorem offTriplePlusWeight_right (S : ReflectedSpectrum I (7 / 8))
    (i : I) (hRight : 1 / 2 < (S.point i).re) :
    S.unitMass i <= S.offTripleAdjustedWeight 3 i := by
  unfold offTripleAdjustedWeight
  have hf := S.multiplicitySupportWeight_right i hRight
  have hi := S.offTripleUnitAt_nonneg i
  have hj := S.offTripleUnitAt_nonneg (S.mirror i)
  linarith

theorem offTriplePlusWeight_right_triple (S : ReflectedSpectrum I (7 / 8))
    (i : I) (hRight : 1 / 2 < (S.point i).re) (h3 : 3 <= S.mult i) :
    3 * S.unitMass i <= S.offTripleAdjustedWeight 3 i := by
  classical
  have hz := S.offTripleUnitAt_eq_zero_of_half_le i hRight.le
  have hm := S.three_unit_le_mass i h3
  have hNot : Not (Membership.mem S.weakIndices i) := by
    intro hi
    exact (not_lt_of_ge (S.weak_re_le_half i hi)) hRight
  by_cases hWeak : Membership.mem S.weakIndices (S.mirror i)
  . have hRe := congrArg Complex.re (S.point_mirror i)
    rw [zeroReflection_re] at hRe
    have hLeft : (S.point (S.mirror i)).re < 1 / 2 := by linarith
    have h3Mirror : 3 <= S.mult (S.mirror i) := by
      simpa only [S.mult_mirror i] using h3
    have ht : S.offTripleUnitAt (S.mirror i) = S.unitMass i := by
      simp only [offTripleUnitAt, if_pos (And.intro hWeak (And.intro hLeft h3Mirror)),
        S.unitMass_mirror i]
    have hf := S.multiplicitySupportWeight_right_half_mass i hRight
    unfold offTripleAdjustedWeight
    rw [hz, ht]
    linarith
  . have hf : S.multiplicitySupportWeight i = S.mass i := by
      simp only [multiplicitySupportWeight, multiplicitySupportCharge,
        if_neg hNot, if_neg hWeak, sub_zero]
    have ht := S.offTripleUnitAt_nonneg (S.mirror i)
    unfold offTripleAdjustedWeight
    rw [hz, hf]
    linarith

end PrimeFactorOscillations.CarmichaelDyadicSharpness.ReflectedSpectrum

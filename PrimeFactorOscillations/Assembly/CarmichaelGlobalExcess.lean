/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.CarmichaelOffcriticalTail

/-!
# The full offcritical multiplicity excess above three

The excess is taken over every strict left-half atom, independently of weak
membership. Its symmetric half charge preserves the unit floor and the
three-half floor at every right atom of order at least three.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations.CarmichaelDyadicSharpness.ReflectedSpectrum

open CarmichaelWeightedSignal

variable {I : Type*} [Fintype I] {sigma : Real}

def offcriticalExcessAt (S : ReflectedSpectrum I sigma) (i : I) : Real :=
  if (S.point i).re < 1 / 2 then
    ((S.mult i - 3 : Nat) : Real) * S.unitMass i else 0

def globalOffcriticalExcess (S : ReflectedSpectrum I sigma) : Real :=
  Finset.univ.sum S.offcriticalExcessAt

def globalExcessWeight (S : ReflectedSpectrum I sigma) (i : I) : Real :=
  S.multiplicitySupportWeight i -
    (1 / 2) * (S.offcriticalExcessAt i + S.offcriticalExcessAt (S.mirror i))

omit [Fintype I] in
theorem offcriticalExcessAt_nonneg (S : ReflectedSpectrum I sigma) (i : I) :
    0 <= S.offcriticalExcessAt i := by
  unfold offcriticalExcessAt
  split_ifs
  . exact mul_nonneg (Nat.cast_nonneg _) (S.unitMass_nonneg i)
  . exact le_refl _

theorem globalOffcriticalExcess_nonneg (S : ReflectedSpectrum I sigma) :
    0 <= S.globalOffcriticalExcess :=
  Finset.sum_nonneg (fun i _ => S.offcriticalExcessAt_nonneg i)

omit [Fintype I] in
theorem offcriticalExcessAt_eq_zero_of_half_le (S : ReflectedSpectrum I sigma)
    (i : I) (h : 1 / 2 <= (S.point i).re) :
    S.offcriticalExcessAt i = 0 := by
  unfold offcriticalExcessAt
  exact ite_eq_right (not_lt_of_ge h)

omit [Fintype I] in
theorem offcriticalExcessAt_eq_zero_of_order_le_three (S : ReflectedSpectrum I sigma)
    (i : I) (h : S.mult i <= 3) : S.offcriticalExcessAt i = 0 := by
  unfold offcriticalExcessAt
  rw [Nat.sub_eq_zero_of_le h]
  simp

theorem offcriticalExcessAt_mirror_right (S : ReflectedSpectrum I sigma)
    (i : I) (hRight : 1 / 2 < (S.point i).re) :
    S.offcriticalExcessAt (S.mirror i) =
      ((S.mult i - 3 : Nat) : Real) * S.unitMass i := by
  have hp := congrArg Complex.re (S.point_mirror i)
  rw [zeroReflection_re] at hp
  have hLeft : (S.point (S.mirror i)).re < 1 / 2 := by linarith
  simp only [offcriticalExcessAt, ite_eq_left hLeft, S.mult_mirror i, S.unitMass_mirror i]

theorem globalExcessWeight_mirror (S : ReflectedSpectrum I sigma) (i : I) :
    S.globalExcessWeight (S.mirror i) = S.globalExcessWeight i := by
  unfold globalExcessWeight
  rw [S.multiplicitySupportWeight_mirror, S.mirror_involutive]
  ring

theorem sum_globalExcessWeight (S : ReflectedSpectrum I sigma) :
    Finset.univ.sum S.globalExcessWeight =
      S.totalMass - S.weakExcessMass - S.weakRepeatedUnitMass -
        S.globalOffcriticalExcess := by
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
  have hPerm : Finset.univ.sum (fun i => S.offcriticalExcessAt (S.mirror i)) =
      Finset.univ.sum S.offcriticalExcessAt := by
    rw [<- Finset.sum_image (fun i _ j _ h => S.mirror_injective h), hUniv]
  unfold globalExcessWeight
  rw [Finset.sum_sub_distrib, <- Finset.mul_sum, Finset.sum_add_distrib,
    hPerm, S.sum_multiplicitySupportWeight]
  unfold globalOffcriticalExcess
  ring

theorem globalExcessWeight_right_three (S : ReflectedSpectrum I (7 / 8))
    (i : I) (hRight : 1 / 2 < (S.point i).re) (hThree : 3 <= S.mult i) :
    (3 / 2) * S.unitMass i <= S.globalExcessWeight i := by
  have hz := S.offcriticalExcessAt_eq_zero_of_half_le i hRight.le
  have hm := S.offcriticalExcessAt_mirror_right i hRight
  have hn := Nat.sub_add_cancel hThree
  have hr : ((S.mult i - 3 : Nat) : Real) + 3 = (S.mult i : Real) := by
    exact_mod_cast hn
  have hMass : S.mass i =
      (3 + ((S.mult i - 3 : Nat) : Real)) * S.unitMass i := by
    unfold mass unitMass
    rw [div_eq_mul_inv, <- hr]
    ring
  have hHalf := S.multiplicitySupportWeight_right_half_mass i hRight
  unfold globalExcessWeight
  rw [hz, hm]
  linarith

theorem globalExcessWeight_right (S : ReflectedSpectrum I (7 / 8))
    (i : I) (hRight : 1 / 2 < (S.point i).re) :
    S.unitMass i <= S.globalExcessWeight i := by
  by_cases hThree : 3 <= S.mult i
  . have hf := S.globalExcessWeight_right_three i hRight hThree
    linarith [S.unitMass_nonneg i]
  . have hSmall : S.mult i <= 3 := by omega
    have hMirror : S.mult (S.mirror i) <= 3 := by rwa [S.mult_mirror i]
    unfold globalExcessWeight
    rw [S.offcriticalExcessAt_eq_zero_of_order_le_three i hSmall,
      S.offcriticalExcessAt_eq_zero_of_order_le_three (S.mirror i) hMirror]
    simpa using S.multiplicitySupportWeight_right i hRight

theorem globalExcessWeight_nonneg (S : ReflectedSpectrum I (7 / 8)) (i : I) :
    0 <= S.globalExcessWeight i := by
  have hRe := congrArg Complex.re (S.point_mirror i)
  rw [zeroReflection_re] at hRe
  by_cases hRight : 1 / 2 < (S.point i).re
  . exact (S.unitMass_nonneg i).trans (S.globalExcessWeight_right i hRight)
  . by_cases hLeft : (S.point i).re < 1 / 2
    . have hr : 1 / 2 < (S.point (S.mirror i)).re := by linarith
      have h := (S.unitMass_nonneg (S.mirror i)).trans
        (S.globalExcessWeight_right (S.mirror i) hr)
      simpa only [S.globalExcessWeight_mirror] using h
    . have hi : 1 / 2 <= (S.point i).re := le_of_not_gt hLeft
      have hj : 1 / 2 <= (S.point (S.mirror i)).re := by linarith
      unfold globalExcessWeight
      rw [S.offcriticalExcessAt_eq_zero_of_half_le i hi,
        S.offcriticalExcessAt_eq_zero_of_half_le (S.mirror i) hj]
      simpa using S.multiplicitySupportWeight_nonneg i

end PrimeFactorOscillations.CarmichaelDyadicSharpness.ReflectedSpectrum


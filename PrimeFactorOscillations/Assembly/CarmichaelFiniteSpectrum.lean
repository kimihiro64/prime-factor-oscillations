/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.CarmichaelTraceAtoms

/-!
# Finite reflected spectra and their complete compensation references

The data contain points, positive natural multiplicities and their reflection
symmetry. Reference existence and reference mass comparisons are proved from
the actual finite atomic order; no carrier estimate is a structure field.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations.CarmichaelDyadicSharpness

open DirichletCompensatedProbe CarmichaelWeightedSignal CarmichaelTraceSharpness

structure ReflectedSpectrum (I : Type*) (sigma : Real) where
  point : I -> Complex
  mult : I -> Nat
  point_injective : Function.Injective point
  mult_pos : forall i, 0 < mult i
  im_pos : forall i, 0 < (point i).im
  re_lower : forall i, 1 - sigma <= (point i).re
  re_upper : forall i, (point i).re <= sigma
  mirror : I -> I
  mirror_involutive : Function.Involutive mirror
  point_mirror : forall i, point (mirror i) = zeroReflection (point i)
  mult_mirror : forall i, mult (mirror i) = mult i

namespace ReflectedSpectrum

variable {I : Type*} [Fintype I] {sigma : Real}

def mass (S : ReflectedSpectrum I sigma) (i : I) : Real :=
  (S.mult i : Real) / (S.point i).im ^ 2

def rowOrder (S : ReflectedSpectrum I sigma) (a : Real) (i : I) : Nat :=
  atomicOrder S.point S.mult (powerMap a (S.point i))

def weakIndices (S : ReflectedSpectrum I sigma) : Finset I := by
  classical
  exact Finset.univ.filter (fun i =>
    (S.mult i : Real) <= 2 * (S.rowOrder 2 i : Real) /\
    (S.mult i : Real) <= 4 * (S.rowOrder 4 i : Real))

def carrierIndices (S : ReflectedSpectrum I sigma) : Finset I := by
  classical
  exact Finset.univ.filter (fun i =>
    2 * (S.rowOrder 2 i : Real) < (S.mult i : Real) \/
    4 * (S.rowOrder 4 i : Real) < (S.mult i : Real))

def totalMass (S : ReflectedSpectrum I sigma) : Real :=
  Finset.univ.sum S.mass

def weakMass (S : ReflectedSpectrum I sigma) : Real :=
  S.weakIndices.sum S.mass

def carrierMass (S : ReflectedSpectrum I sigma) : Real :=
  S.carrierIndices.sum S.mass

omit [Fintype I] in
theorem mass_nonneg (S : ReflectedSpectrum I sigma) (i : I) : 0 <= S.mass i :=
  div_nonneg (Nat.cast_nonneg _) (sq_nonneg _)

omit [Fintype I] in
theorem mass_pos (S : ReflectedSpectrum I sigma) (i : I) : 0 < S.mass i :=
  div_pos (by exact_mod_cast S.mult_pos i) (pow_pos (S.im_pos i) 2)

omit [Fintype I] in
theorem mirror_injective (S : ReflectedSpectrum I sigma) : Function.Injective S.mirror := by
  intro i j h
  have hh := congrArg S.mirror h
  rw [S.mirror_involutive i, S.mirror_involutive j] at hh
  exact hh

omit [Fintype I] in
theorem mass_mirror (S : ReflectedSpectrum I sigma) (i : I) :
    S.mass (S.mirror i) = S.mass i := by
  simp only [mass, S.mult_mirror, S.point_mirror, zeroReflection_im]

theorem reference_exists (S : ReflectedSpectrum I sigma) (a : Real) (i : I)
    (hWeak : (S.mult i : Real) <= a * (S.rowOrder a i : Real)) :
    exists j : I, S.point j = powerMap a (S.point i) := by
  by_contra hNot
  have hNone : forall j : I, Not (S.point j = powerMap a (S.point i)) := by
    intro j hj
    exact hNot (Exists.intro j hj)
  have hZero : S.rowOrder a i = 0 := atomicOrder_zero S.point S.mult _ hNone
  have hSource : (0 : Real) < (S.mult i : Real) := by exact_mod_cast S.mult_pos i
  simp only [hZero, Nat.cast_zero, mul_zero] at hWeak
  exact (not_le_of_gt hSource) hWeak

def referenceIndex (S : ReflectedSpectrum I sigma) (a : Real) (i : I) : I := by
  classical
  exact if h : exists j : I, S.point j = powerMap a (S.point i) then
    Classical.choose h else i

theorem point_referenceIndex (S : ReflectedSpectrum I sigma) (a : Real) (i : I)
    (hWeak : (S.mult i : Real) <= a * (S.rowOrder a i : Real)) :
    S.point (S.referenceIndex a i) = powerMap a (S.point i) := by
  classical
  have h := S.reference_exists a i hWeak
  unfold referenceIndex
  rw [dite_eq_left h]
  exact Classical.choose_spec h

theorem rowOrder_referenceIndex (S : ReflectedSpectrum I sigma) (a : Real) (i : I)
    (hWeak : (S.mult i : Real) <= a * (S.rowOrder a i : Real)) :
    S.rowOrder a i = S.mult (S.referenceIndex a i) := by
  unfold rowOrder
  rw [<- S.point_referenceIndex a i hWeak]
  exact atomicOrder_at S.point S.mult S.point_injective _

theorem referenceIndex_injOn (S : ReflectedSpectrum I sigma)
    (U : Finset I) (a : Real) (ha : 0 < a)
    (hWeak : forall i, Membership.mem U i ->
      (S.mult i : Real) <= a * (S.rowOrder a i : Real)) :
    Set.InjOn (S.referenceIndex a) U := by
  intro i hi j hj heq
  apply S.point_injective
  apply powerMap_injective a ha
  calc
    powerMap a (S.point i) = S.point (S.referenceIndex a i) :=
      (S.point_referenceIndex a i (hWeak i hi)).symm
    _ = S.point (S.referenceIndex a j) := congrArg S.point heq
    _ = powerMap a (S.point j) := S.point_referenceIndex a j (hWeak j hj)

theorem mass_le_reference (S : ReflectedSpectrum I sigma) (a : Real) (ha : 0 < a)
    (i : I) (hWeak : (S.mult i : Real) <= a * (S.rowOrder a i : Real)) :
    a * S.mass i <= S.mass (S.referenceIndex a i) := by
  have hPoint := S.point_referenceIndex a i hWeak
  have hIm : (S.point (S.referenceIndex a i)).im = (S.point i).im / a := by
    rw [hPoint]
    exact (eq_div_iff ha.ne').mpr (powerMap_im_identity a ha (S.point i))
  have hOrder := S.rowOrder_referenceIndex a i hWeak
  rw [hOrder] at hWeak
  have hWeight : 0 <= a / (S.point i).im ^ 2 := div_nonneg ha.le (sq_nonneg _)
  unfold mass
  rw [hIm]
  calc
    a * ((S.mult i : Real) / (S.point i).im ^ 2) =
        (a / (S.point i).im ^ 2) * (S.mult i : Real) := by ring
    _ <= (a / (S.point i).im ^ 2) *
        (a * (S.mult (S.referenceIndex a i) : Real)) :=
      mul_le_mul_of_nonneg_left hWeak hWeight
    _ = (S.mult (S.referenceIndex a i) : Real) / ((S.point i).im / a) ^ 2 := by
      field_simp [ha.ne', (S.im_pos i).ne']

end ReflectedSpectrum
end PrimeFactorOscillations.CarmichaelDyadicSharpness

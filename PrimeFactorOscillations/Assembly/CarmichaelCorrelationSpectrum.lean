/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import PrimeFactorOscillations.Assembly.CarmichaelCorrelation

/-!
# The exact Dirichlet spectrum of the return correlation kernel

Every coefficient is nonnegative. Inversion retains the actual unit-group
kernel and its complete spectral mass is the reciprocal vacancy.
The principal coefficient is one; odd packets have no quadratic mode.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations.CarmichaelCorrelationSpectrum

open CarmichaelCorrelation

local instance (q : Nat) : DecidableEq (DirichletCharacter Complex q) :=
  Classical.typeDecidableEq _

def unitCharacter {q : Nat} (chi : DirichletCharacter Complex q) :
    MonoidHom (Units (ZMod q)) Complex :=
  chi.toMonoidHom.comp (Units.coeHom (ZMod q))

theorem unitCharacter_one (q : Nat) :
    unitCharacter (1 : DirichletCharacter Complex q) = 1 := by
  ext u
  change (1 : DirichletCharacter Complex q) (u : ZMod q) = 1
  exact MulChar.one_apply_coe u

theorem unitCharacter_ne_one {q : Nat} (chi : DirichletCharacter Complex q)
    (hchi : Not (chi = 1)) : Not (unitCharacter chi = 1) := by
  intro h
  apply hchi
  apply MulChar.eq_one_iff.mpr
  intro u
  have hv := congrArg (fun f : MonoidHom (Units (ZMod q)) Complex => f u) h
  change chi (u : ZMod q) = 1 at hv
  exact hv

theorem sum_unit_characters (q : Nat) [NeZero q] (u : Units (ZMod q)) :
    Finset.univ.sum (fun chi : DirichletCharacter Complex q => unitCharacter chi u) =
      if u = 1 then (q.totient : Complex) else 0 := by
  classical
  change Finset.univ.sum (fun chi : DirichletCharacter Complex q => chi (u : ZMod q)) = _
  rw [DirichletCharacter.sum_characters_eq Complex]
  by_cases hu : u = 1
  . subst u
    simp
  . have hv : Not ((u : ZMod q) = 1) := by
      intro h
      apply hu
      exact Units.ext h
    simp only [ite_eq_right hu, ite_eq_right hv]

theorem unit_character_pair (q : Nat) [NeZero q] (u v : Units (ZMod q)) :
    Finset.univ.sum (fun chi : DirichletCharacter Complex q =>
      unitCharacter chi (Inv.inv u) * unitCharacter chi v) =
        if v = u then (q.totient : Complex) else 0 := by
  classical
  calc
    _ = Finset.univ.sum (fun chi : DirichletCharacter Complex q =>
        unitCharacter chi (Inv.inv u * v)) := by
      apply Finset.sum_congr rfl
      intro chi _
      rw [map_mul]
    _ = _ := by
      rw [sum_unit_characters]
      by_cases h : v = u
      . subst v
        simp
      . have hn : Not (Inv.inv u * v = 1) := by
          intro hEq
          apply h
          have ht := congrArg (fun z : Units (ZMod q) => u * z) hEq
          simpa only [<- mul_assoc, mul_inv_cancel, one_mul, mul_one] using ht
        simp only [ite_eq_right h, ite_eq_right hn]

/-- Complete inversion on the actual unit group, with no discarded character. -/
theorem unit_fourier_inversion (q : Nat) [NeZero q]
    (f : Units (ZMod q) -> Real) (u : Units (ZMod q)) :
    Finset.univ.sum (fun chi : DirichletCharacter Complex q =>
      characterSum f (unitCharacter chi) * unitCharacter chi (Inv.inv u)) =
        ((Fintype.card (Units (ZMod q)) : Real) : Complex) * (f u : Complex) := by
  classical
  calc
    _ = Finset.univ.sum (fun v : Units (ZMod q) => (f v : Complex) *
        Finset.univ.sum (fun chi : DirichletCharacter Complex q =>
          unitCharacter chi (Inv.inv u) * unitCharacter chi v)) := by
      unfold characterSum
      simp_rw [Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro v _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro chi _
      ring
    _ = (q.totient : Complex) * (f u : Complex) := by
      simp_rw [unit_character_pair]
      simp [mul_ite, mul_comm]
    _ = _ := by rw [ZMod.card_units_eq_totient]; norm_cast

def coefficient {q : Nat} [NeZero q] (w : Units (ZMod q) -> Real)
    (chi : DirichletCharacter Complex q) : Real :=
  Complex.normSq (characterSum w (unitCharacter chi)) / weightSum w ^ 2

theorem coefficient_nonneg {q : Nat} [NeZero q] (w : Units (ZMod q) -> Real)
    (chi : DirichletCharacter Complex q) : 0 <= coefficient w chi :=
  div_nonneg (Complex.normSq_nonneg _) (sq_nonneg _)

theorem coefficient_principal {q : Nat} [NeZero q] (w : Units (ZMod q) -> Real)
    (hSum : 0 < weightSum w) : coefficient w 1 = 1 := by
  have hChar : characterSum w (unitCharacter (1 : DirichletCharacter Complex q)) =
      (weightSum w : Complex) := by
    rw [unitCharacter_one]
    simp only [characterSum, MonoidHom.one_apply, mul_one, weightSum, Complex.ofReal_sum]
  unfold coefficient
  rw [hChar, Complex.normSq_ofReal]
  field_simp [ne_of_gt hSum]

theorem kernel_expansion {q : Nat} [NeZero q] (w : Units (ZMod q) -> Real)
    (u : Units (ZMod q)) :
    (kernel w u : Complex) =
      Finset.univ.sum (fun chi : DirichletCharacter Complex q =>
        (coefficient w chi : Complex) * unitCharacter chi (Inv.inv u)) := by
  classical
  let n : Complex := ((Fintype.card (Units (ZMod q)) : Real) : Complex)
  have hn : Not (n = 0) := by
    dsimp [n]
    exact_mod_cast Fintype.card_ne_zero
  have hCoeff (chi : DirichletCharacter Complex q) :
      characterSum (kernel w) (unitCharacter chi) = n * (coefficient w chi : Complex) := by
    rw [kernel_character_sum]
    unfold coefficient
    dsimp only [n]
    push_cast
    ring
  have hInv := unit_fourier_inversion q (kernel w) u
  let T : Complex := Finset.univ.sum (fun chi : DirichletCharacter Complex q =>
    (coefficient w chi : Complex) * unitCharacter chi (Inv.inv u))
  have hScale : n * T = n * (kernel w u : Complex) := by
    calc
      _ = Finset.univ.sum (fun chi : DirichletCharacter Complex q =>
          characterSum (kernel w) (unitCharacter chi) *
            unitCharacter chi (Inv.inv u)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro chi _
        rw [hCoeff]
        ring
      _ = _ := hInv
  have hProduct : n * (T - (kernel w u : Complex)) = 0 := by
    rw [mul_sub, hScale, sub_self]
  have hDiff : T - (kernel w u : Complex) = 0 := (mul_eq_zero.mp hProduct).resolve_left hn
  exact (sub_eq_zero.mp hDiff).symm

theorem coefficient_sum {q : Nat} [NeZero q] (w : Units (ZMod q) -> Real)
    (hSum : 0 < weightSum w) (hIdem : forall u, w u * w u = w u) :
    Finset.univ.sum (coefficient w) = 1 / weightMean w := by
  have h := kernel_expansion w (1 : Units (ZMod q))
  simp only [inv_one, map_one, mul_one, <- Complex.ofReal_sum] at h
  rw [kernel_at_one w hSum hIdem] at h
  exact_mod_cast h.symm

theorem nonprincipal_coefficient_sum {q : Nat} [NeZero q]
    (w : Units (ZMod q) -> Real) (hSum : 0 < weightSum w)
    (hIdem : forall u, w u * w u = w u) :
    (Finset.univ.erase (1 : DirichletCharacter Complex q)).sum (coefficient w) =
      1 / weightMean w - 1 := by
  classical
  have h := Finset.sum_erase_add (Finset.univ : Finset (DirichletCharacter Complex q))
    (coefficient w) (Finset.mem_univ 1)
  rw [coefficient_principal w hSum, coefficient_sum w hSum hIdem] at h
  linarith

/-- The arithmetic density, not the number of ambient characters, controls the spectrum. -/
theorem canonical_vacancy_spectral_cost (q : Nat) [NeZero q] (S : Finset Nat.Primes)
    (hDiv : forall p : S,
      Dvd.dvd (p.val : Nat) (Monoid.exponent (Units (ZMod q)))) :
    And (coefficient (vacancyWeight (G := Units (ZMod q)) (Monoid.exponent (Units (ZMod q))) S) 1 = 1)
      (Finset.univ.sum (coefficient (vacancyWeight (G := Units (ZMod q)) (Monoid.exponent (Units (ZMod q))) S)) =
        1 / Finset.univ.prod (fun p : S =>
          1 - 1 / (PrimeOrderReturnLaw.returnIndex (G := Units (ZMod q))
            (Monoid.exponent (Units (ZMod q))) (p.val : Nat) : Real))) := by
  have hPos := canonical_vacancy_weightSum_pos (G := Units (ZMod q)) S hDiv
  refine And.intro (coefficient_principal _ hPos) ?_
  rw [coefficient_sum _ hPos (vacancyWeight_idempotent _ S)]
  exact congrArg (fun z : Real => 1 / z)
    (OddReturnCharacterSupport.vacancy_mean_eq_product _ S hDiv
      (fun g : Units (ZMod q) => Monoid.pow_exponent_eq_one g))

/-- Exact removal of every nonprincipal quadratic character from the positive spectrum. -/
theorem odd_vacancy_coefficient_zero (q : Nat) [NeZero q] (S : Finset Nat.Primes)
    (hDiv : forall p : S,
      Dvd.dvd (p.val : Nat) (Monoid.exponent (Units (ZMod q))))
    (hOdd : forall p : S, Not ((p.val : Nat) = 2))
    (chi : DirichletCharacter Complex q) (hchi : Not (chi = 1))
    (hSquare : forall u : Units (ZMod q), (chi (u : ZMod q)) ^ 2 = 1) :
    coefficient (vacancyWeight (G := Units (ZMod q)) (Monoid.exponent (Units (ZMod q))) S) chi = 0 := by
  have hZero := odd_vacancy_kernel_quadratic_sum_eq_zero
    (Monoid.exponent (Units (ZMod q))) S hDiv hOdd
    (fun g => Monoid.pow_exponent_eq_one g) (unitCharacter chi)
    (unitCharacter_ne_one chi hchi) hSquare
  have hCoeff := kernel_coefficient_eq
    (vacancyWeight (G := Units (ZMod q)) (Monoid.exponent (Units (ZMod q))) S) (unitCharacter chi)
  rw [hZero, zero_div] at hCoeff
  exact_mod_cast hCoeff.symm

end PrimeFactorOscillations.CarmichaelCorrelationSpectrum

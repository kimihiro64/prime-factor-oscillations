/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.ZMod.Basic
import PrimeFactorOscillations.Mathlib.NumberTheory.GaussSum.QuadraticEnergy

/-!
# Joint energy of a ramified Gauss permutation block

This is the finite-field block underlying the tame ramified case of
Szpruch, On Shahidi local coefficients matrix, arXiv:1609.08122v4,
Proposition 4.17. The actual p-adic intertwiner identification and its
spectral conductor factor are not asserted by these finite statements.

If the m-th power of chi is nonprincipal, multiplying chi by any power of
an m-torsion character cannot create a principal entry. Every entry on the
permutation support has the same exact Gauss energy. Summing the entire
matrix action preserves the energy after square-root normalization.
-/

set_option autoImplicit false
set_option Elab.async false

namespace MulChar

variable {F : Type*} [Field F] [Fintype F]

omit [Fintype F] in
/-- The ramification test prevents every torsion twist from becoming principal. -/
theorem mul_pow_ne_one_of_pow_ne_one (chi kappa : MulChar F Complex)
    (m c : Nat) (hk : kappa ^ m = 1) (hc : Not (chi ^ m = 1)) :
    Not (chi * kappa ^ c = 1) := by
  have hm : (chi * kappa ^ c) ^ m = chi ^ m := by
    rw [mul_pow, <- pow_mul, Nat.mul_comm c m, pow_mul, hk, one_pow, mul_one]
  intro h
  rw [h, one_pow] at hm
  exact hc hm.symm

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- Complete Gauss matrix on a specified permutation support, including all indices. -/
noncomputable def gaussPermutation (chi kappa : MulChar F Complex) (psi : AddChar F Complex)
    (p : Equiv.Perm I) (c : I -> Nat) (i j : I) : Complex :=
  if j = p i then gaussSum (chi * kappa ^ c i) psi else 0

/-- Exact energy of the full matrix action, with no entrywise triangle bound. -/
theorem sum_normSq_gaussPermutation (chi kappa : MulChar F Complex)
    (m : Nat) (hk : kappa ^ m = 1) (hc : Not (chi ^ m = 1))
    (psi : AddChar F Complex) (hpsi : Not (psi = 1))
    (p : Equiv.Perm I) (c : I -> Nat) (v : I -> Complex) :
    Finset.univ.sum (fun i => Complex.normSq
      (Finset.univ.sum (fun j => gaussPermutation chi kappa psi p c i j * v j))) =
      (Fintype.card F : Real) * Finset.univ.sum (fun i => Complex.normSq (v i)) := by
  have hrow (i : I) : Finset.univ.sum
      (fun j => gaussPermutation chi kappa psi p c i j * v j) =
      gaussSum (chi * kappa ^ c i) psi * v (p i) := by
    simp [gaussPermutation, ite_mul]
  simp_rw [hrow, map_mul, normSq_gaussSum_eq_card _
    (mul_pow_ne_one_of_pow_ne_one chi kappa m _ hk hc) _ hpsi]
  rw [<- Finset.mul_sum]
  congr 1
  exact Fintype.sum_equiv p _ _ (fun _ => rfl)

/-- The square-root-normalized full block is an exact isometry. -/
theorem sum_normSq_normalized_gaussPermutation (chi kappa : MulChar F Complex)
    (m : Nat) (hk : kappa ^ m = 1) (hc : Not (chi ^ m = 1))
    (psi : AddChar F Complex) (hpsi : Not (psi = 1))
    (p : Equiv.Perm I) (c : I -> Nat) (v : I -> Complex) :
    Finset.univ.sum (fun i => Complex.normSq
      ((Finset.univ.sum (fun j => gaussPermutation chi kappa psi p c i j * v j)) /
        (Real.sqrt (Fintype.card F) : Complex))) =
      Finset.univ.sum (fun i => Complex.normSq (v i)) := by
  have hq : (0 : Real) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  have hs : (Real.sqrt (Fintype.card F)) ^ 2 = (Fintype.card F : Real) :=
    Real.sq_sqrt hq.le
  simp only [Complex.normSq_div, Complex.normSq_ofReal, <- pow_two, hs]
  rw [<- Finset.sum_div, sum_normSq_gaussPermutation chi kappa m hk hc psi hpsi p c v]
  field_simp

/-- The complete five-by-five tame block, with the source support i-j=1
written equivalently as j=i-1. All five Whittaker indices are retained. -/
theorem sum_normSq_quintic_ramified_block (chi kappa : MulChar F Complex)
    (hk : kappa ^ 5 = 1) (hc : Not (chi ^ 5 = 1))
    (psi : AddChar F Complex) (hpsi : Not (psi = 1)) (v : ZMod 5 -> Complex) :
    Finset.univ.sum (fun i : ZMod 5 => Complex.normSq
      ((Finset.univ.sum (fun j : ZMod 5 =>
        (if j = i - 1 then gaussSum (chi * kappa ^ (i + j).val) psi else 0) * v j)) /
        (Real.sqrt (Fintype.card F) : Complex))) =
      Finset.univ.sum (fun i : ZMod 5 => Complex.normSq (v i)) := by
  let p : Equiv.Perm (ZMod 5) := Equiv.addRight (-1)
  have h := sum_normSq_normalized_gaussPermutation chi kappa 5 hk hc psi hpsi
    p (fun i => (i + (i - 1)).val) v
  rw [<- h]
  apply Finset.sum_congr rfl
  intro i _
  congr 2
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : j = i - 1
  case pos => subst j; simp [gaussPermutation, p, sub_eq_add_neg]
  case neg =>
    simp only [sub_eq_add_neg] at hj
    simp [gaussPermutation, p, sub_eq_add_neg, hj]

end MulChar

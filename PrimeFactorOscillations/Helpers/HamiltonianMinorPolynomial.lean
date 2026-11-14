/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.Tactic.Ring

/-! # Signed principal-minor moments

The determinant generating polynomial is expanded into its actual principal
minors. The Euler derivative retains the signs and cardinality weights before
evaluation. The parity-root identities are the size-moment part of the signed
compensated-minor comparison; no permanent asymptotic is assumed here.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

variable {Iota R : Type*} [DecidableEq Iota] [Fintype Iota] [CommRing R]

def principalMinorGeneratingPolynomial (M : Matrix Iota Iota R) : Polynomial R :=
  Matrix.det (1 + HSMul.hSMul (Polynomial.X : Polynomial R) (M.map Polynomial.C))

def principalMinorDet (M : Matrix Iota Iota R) (S : Finset Iota) : R :=
  Matrix.det (M.submatrix (Subtype.val : S -> Iota) (Subtype.val : S -> Iota))

theorem principalMinorGeneratingPolynomial_eq (M : Matrix Iota Iota R) :
    principalMinorGeneratingPolynomial M =
      Finset.sum Finset.univ (fun S : Finset Iota =>
        Polynomial.monomial S.card (principalMinorDet M S)) := by
  classical
  apply Polynomial.ext
  intro k
  change (Matrix.det (1 + HSMul.hSMul (Polynomial.X : Polynomial R)
    (M.map Polynomial.C))).coeff k = _
  rw [Matrix.coeff_det_one_add_X_smul_eq_sum_minors (R := R) (n := Iota) M k]
  simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_monomial]
  rw [<- Finset.sum_filter]
  refine Finset.sum_congr ?_ (fun S hS => rfl)
  ext S
  simp [Finset.mem_powersetCard]

def polynomialEuler (p : Polynomial R) : Polynomial R :=
  Polynomial.X * p.derivative

theorem polynomialEuler_monomial (k : Nat) (a : R) :
    polynomialEuler (Polynomial.monomial k a) =
      Polynomial.monomial k ((k : R) * a) := by
  cases k with
  | zero => simp [polynomialEuler]
  | succ k =>
      simp only [polynomialEuler, Polynomial.derivative_monomial,
        Nat.add_sub_cancel]
      rw [<- Polynomial.C_mul_X_pow_eq_monomial,
        <- Polynomial.C_mul_X_pow_eq_monomial]
      simp only [pow_succ, mul_comm a]
      ring

theorem polynomialEuler_sum {J : Type*} (S : Finset J) (p : J -> Polynomial R) :
    polynomialEuler (Finset.sum S p) =
      Finset.sum S (fun j => polynomialEuler (p j)) := by
  simp only [polynomialEuler, Polynomial.derivative_sum, Finset.mul_sum]

theorem principalMinor_euler_eval (M : Matrix Iota Iota R) (t : R) :
    Polynomial.eval t (polynomialEuler (principalMinorGeneratingPolynomial M)) =
      Finset.sum Finset.univ (fun S : Finset Iota =>
        (S.card : R) * principalMinorDet M S * t ^ S.card) := by
  rw [principalMinorGeneratingPolynomial_eq, polynomialEuler_sum]
  simp only [polynomialEuler_monomial, Polynomial.eval_finsetSum,
    Polynomial.eval_monomial]

def parityRootMoment (d : Polynomial R) : Polynomial R :=
  -polynomialEuler ((1 - Polynomial.X) * d)

theorem parityRootMoment_eval_one (d : Polynomial R) :
    Polynomial.eval 1 (parityRootMoment d) = Polynomial.eval 1 d := by
  simp [parityRootMoment, polynomialEuler, Polynomial.derivative_mul]

theorem parityRootMoment_secondDerivative_eval_one (d : Polynomial R) :
    Polynomial.eval 1 (parityRootMoment d).derivative.derivative =
      4 * Polynomial.eval 1 d.derivative +
        3 * Polynomial.eval 1 d.derivative.derivative := by
  simp [parityRootMoment, polynomialEuler, Polynomial.derivative_mul]
  ring

end PrimeFactorOscillations

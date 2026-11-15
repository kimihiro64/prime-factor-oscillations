/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianMinorPolynomial

/-! # Actual coordinate-marked principal-minor polynomials

Deleting a row selects exactly the supports avoiding its coordinate.
The two-coordinate polynomial keeps the complete inclusion-exclusion
cross term, including coincident coordinates. Its Euler readout is
the actual signed occupancy sum over every finite support.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

variable {Iota R : Type*} [Fintype Iota] [DecidableEq Iota] [CommRing R]

def hamiltonianRowScaledMatrix (M : Matrix Iota Iota R) (w : Iota -> R) : Matrix Iota Iota R :=
  fun i j => w i * M i j

def hamiltonianZeroRow (M : Matrix Iota Iota R) (a : Iota) : Matrix Iota Iota R :=
  fun i j => if i = a then 0 else M i j

theorem principalMinorDet_row_scaled (M : Matrix Iota Iota R) (w : Iota -> R) (S : Finset Iota) :
    principalMinorDet (hamiltonianRowScaledMatrix M w) S =
      Finset.univ.prod (fun i : S => w i.val) * principalMinorDet M S := by
  have hMatrix : (hamiltonianRowScaledMatrix M w).submatrix
      (Subtype.val : S -> Iota) (Subtype.val : S -> Iota) =
        Matrix.diagonal (fun i : S => w i.val) *
          M.submatrix (Subtype.val : S -> Iota) (Subtype.val : S -> Iota) := by
    apply Matrix.ext
    intro i j
    simp [hamiltonianRowScaledMatrix, Matrix.mul_apply, Matrix.diagonal_apply]
  dsimp only [principalMinorDet]
  rw [hMatrix, Matrix.det_mul, Matrix.det_diagonal]

theorem principalMinorDet_zero_row (M : Matrix Iota Iota R) (a : Iota) (S : Finset Iota) :
    principalMinorDet (hamiltonianZeroRow M a) S =
      if Membership.mem S a then 0 else principalMinorDet M S := by
  have hMatrix : hamiltonianZeroRow M a =
      hamiltonianRowScaledMatrix M (fun i => if i = a then 0 else 1) := by
    apply Matrix.ext
    intro i j
    by_cases h : i = a <;> simp [hamiltonianZeroRow, hamiltonianRowScaledMatrix, h]
  rw [hMatrix, principalMinorDet_row_scaled]
  by_cases hMem : Membership.mem S a
  case pos =>
    rw [if_pos hMem]
    have hZero : Finset.univ.prod (fun i : S => if i.val = a then (0 : R) else 1) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ (Subtype.mk a hMem)) (by simp)
    rw [hZero, zero_mul]
  case neg =>
    rw [if_neg hMem]
    have hOne : Finset.univ.prod (fun i : S => if i.val = a then (0 : R) else 1) = 1 := by
      apply Finset.prod_eq_one
      intro i hi
      have hNe : Not (i.val = a) := by
        intro h
        apply hMem
        rw [<- h]
        exact i.property
      exact if_neg hNe
    rw [hOne, one_mul]

def hamiltonianCoordinateMinorPolynomial (M : Matrix Iota Iota R) (a : Iota) : Polynomial R :=
  principalMinorGeneratingPolynomial M -
    principalMinorGeneratingPolynomial (hamiltonianZeroRow M a)

def hamiltonianCoordinatePairMinorPolynomial (M : Matrix Iota Iota R) (a b : Iota) : Polynomial R :=
  hamiltonianCoordinateMinorPolynomial M a -
    hamiltonianCoordinateMinorPolynomial (hamiltonianZeroRow M b) a

theorem hamiltonian_coordinate_minor_polynomial_eq (M : Matrix Iota Iota R) (a : Iota) :
    hamiltonianCoordinateMinorPolynomial M a =
      Finset.univ.sum (fun S : Finset Iota =>
        if Membership.mem S a then Polynomial.monomial S.card (principalMinorDet M S) else 0) := by
  unfold hamiltonianCoordinateMinorPolynomial
  rw [principalMinorGeneratingPolynomial_eq M,
    principalMinorGeneratingPolynomial_eq (hamiltonianZeroRow M a), <- Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro S hS
  rw [principalMinorDet_zero_row]
  by_cases h : Membership.mem S a <;> simp [h]

theorem hamiltonian_coordinate_pair_minor_polynomial_eq (M : Matrix Iota Iota R) (a b : Iota) :
    hamiltonianCoordinatePairMinorPolynomial M a b =
      Finset.univ.sum (fun S : Finset Iota =>
        if Membership.mem S a /\ Membership.mem S b then
          Polynomial.monomial S.card (principalMinorDet M S) else 0) := by
  unfold hamiltonianCoordinatePairMinorPolynomial
  rw [hamiltonian_coordinate_minor_polynomial_eq M a,
    hamiltonian_coordinate_minor_polynomial_eq (hamiltonianZeroRow M b) a,
    <- Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro S hS
  rw [principalMinorDet_zero_row]
  by_cases hA : Membership.mem S a <;> by_cases hB : Membership.mem S b <;> simp [hA, hB]

theorem hamiltonian_coordinate_minor_euler_eval (M : Matrix Iota Iota R) (a : Iota) (t : R) :
    Polynomial.eval t (polynomialEuler (hamiltonianCoordinateMinorPolynomial M a)) =
      Finset.univ.sum (fun S : Finset Iota => if Membership.mem S a then
        (S.card : R) * principalMinorDet M S * t ^ S.card else 0) := by
  rw [hamiltonian_coordinate_minor_polynomial_eq, polynomialEuler_sum, Polynomial.eval_finsetSum]
  apply Finset.sum_congr rfl
  intro S hS
  have hZero : polynomialEuler (0 : Polynomial R) = 0 := by simp [polynomialEuler]
  by_cases h : Membership.mem S a <;>
    simp [h, polynomialEuler_monomial, Polynomial.eval_monomial, hZero]

theorem hamiltonian_coordinate_pair_minor_euler_eval (M : Matrix Iota Iota R) (a b : Iota) (t : R) :
    Polynomial.eval t (polynomialEuler (hamiltonianCoordinatePairMinorPolynomial M a b)) =
      Finset.univ.sum (fun S : Finset Iota =>
        if Membership.mem S a /\ Membership.mem S b then
          (S.card : R) * principalMinorDet M S * t ^ S.card else 0) := by
  rw [hamiltonian_coordinate_pair_minor_polynomial_eq, polynomialEuler_sum, Polynomial.eval_finsetSum]
  apply Finset.sum_congr rfl
  intro S hS
  have hZero : polynomialEuler (0 : Polynomial R) = 0 := by simp [polynomialEuler]
  by_cases hA : Membership.mem S a <;> by_cases hB : Membership.mem S b <;>
    simp [hA, hB, polynomialEuler_monomial, Polynomial.eval_monomial, hZero]

theorem principalMinorGeneratingPolynomial_eval (M : Matrix Iota Iota R) (t : R) :
    Polynomial.eval t (principalMinorGeneratingPolynomial M) =
      Matrix.det ((1 : Matrix Iota Iota R) + HSMul.hSMul t M) := by
  unfold principalMinorGeneratingPolynomial
  change (Polynomial.evalRingHom t) (Matrix.det _) = _
  rw [RingHom.map_det]
  congr 1
  apply Matrix.ext
  intro i j
  by_cases h : i = j <;>
    simp [Matrix.map_apply, Matrix.one_apply, Matrix.smul_apply, smul_eq_mul, h] <;> ring

theorem hamiltonian_coordinate_minor_polynomial_eval (M : Matrix Iota Iota R) (a : Iota) (t : R) :
    Polynomial.eval t (hamiltonianCoordinateMinorPolynomial M a) =
      Matrix.det ((1 : Matrix Iota Iota R) + HSMul.hSMul t M) -
        Matrix.det ((1 : Matrix Iota Iota R) + HSMul.hSMul t (hamiltonianZeroRow M a)) := by
  rw [hamiltonianCoordinateMinorPolynomial, Polynomial.eval_sub,
    principalMinorGeneratingPolynomial_eval, principalMinorGeneratingPolynomial_eval]

theorem hamiltonian_coordinate_pair_minor_polynomial_eval
    (M : Matrix Iota Iota R) (a b : Iota) (t : R) :
    Polynomial.eval t (hamiltonianCoordinatePairMinorPolynomial M a b) =
      Matrix.det ((1 : Matrix Iota Iota R) + HSMul.hSMul t M) -
        Matrix.det ((1 : Matrix Iota Iota R) + HSMul.hSMul t (hamiltonianZeroRow M a)) -
        Matrix.det ((1 : Matrix Iota Iota R) + HSMul.hSMul t (hamiltonianZeroRow M b)) +
        Matrix.det ((1 : Matrix Iota Iota R) +
          HSMul.hSMul t (hamiltonianZeroRow (hamiltonianZeroRow M b) a)) := by
  rw [hamiltonianCoordinatePairMinorPolynomial, Polynomial.eval_sub,
    hamiltonian_coordinate_minor_polynomial_eval, hamiltonian_coordinate_minor_polynomial_eval]
  ring

end PrimeFactorOscillations

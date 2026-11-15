/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianCoordinateMinorPolynomial
import PrimeFactorOscillations.Helpers.HamiltonianParityResolventSplit
import PrimeFactorOscillations.Helpers.HamiltonianTwoRowDeterminant

/-! # Actual signed coordinate occupancy and its cleared physical formula

The coordinate-marked polynomials are the full finite-support sums.
Their determinant row replacements give the complete physical resolvent
coefficients. Rank-one cancellation is then applied to these actual
observables, with no independent coordinate model substituted.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

variable {Iota : Type*} [Fintype Iota] [DecidableEq Iota]

def hamiltonianCoordinateMinorMoment (M : Matrix Iota Iota Real) (a : Iota) : Real :=
  -(1 / 2 : Real) * Polynomial.eval 1
    (polynomialEuler (hamiltonianCoordinateMinorPolynomial M a))

def hamiltonianCoordinatePairMinorMoment (M : Matrix Iota Iota Real) (a b : Iota) : Real :=
  -(1 / 2 : Real) * Polynomial.eval 1
    (polynomialEuler (hamiltonianCoordinatePairMinorPolynomial M a b))

theorem hamiltonian_coordinate_minor_moment_sum (M : Matrix Iota Iota Real) (a : Iota) :
    hamiltonianCoordinateMinorMoment M a =
      Finset.univ.sum (fun S : Finset Iota => if Membership.mem S a then
        -((S.card : Real) / 2) * principalMinorDet M S else 0) := by
  rw [hamiltonianCoordinateMinorMoment, hamiltonian_coordinate_minor_euler_eval, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro S hS
  by_cases h : Membership.mem S a <;> simp [h] <;> ring

theorem hamiltonian_coordinate_pair_minor_moment_sum (M : Matrix Iota Iota Real) (a b : Iota) :
    hamiltonianCoordinatePairMinorMoment M a b =
      Finset.univ.sum (fun S : Finset Iota =>
        if Membership.mem S a /\ Membership.mem S b then
          -((S.card : Real) / 2) * principalMinorDet M S else 0) := by
  rw [hamiltonianCoordinatePairMinorMoment, hamiltonian_coordinate_pair_minor_euler_eval, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro S hS
  by_cases hA : Membership.mem S a <;> by_cases hB : Membership.mem S b <;>
    simp [hA, hB] <;> ring

theorem hamiltonian_coordinate_minor_polynomial_row
    (M : Matrix Iota Iota Real) (a : Iota) (t : Real) :
    Polynomial.eval t (hamiltonianCoordinateMinorPolynomial M a) =
      Matrix.det (Matrix.updateRow ((1 : Matrix Iota Iota Real) + HSMul.hSMul t M)
        a ((HSMul.hSMul t M) a)) := by
  let A := (1 : Matrix Iota Iota Real) + HSMul.hSMul t M
  let w := (HSMul.hSMul t M) a
  have hZero : (1 : Matrix Iota Iota Real) + HSMul.hSMul t (hamiltonianZeroRow M a) =
      Matrix.updateRow A a ((1 : Matrix Iota Iota Real) a) := by
    apply Matrix.ext
    intro i j
    by_cases h : i = a <;>
      simp [A, hamiltonianZeroRow, Matrix.updateRow_apply, Matrix.add_apply,
        Matrix.smul_apply, smul_eq_mul, h]
  have hRow : A a = (1 : Matrix Iota Iota Real) a + w := rfl
  have hAdd := Matrix.det_updateRow_add A a ((1 : Matrix Iota Iota Real) a) w
  rw [<- hRow, Matrix.updateRow_eq_self] at hAdd
  rw [hamiltonian_coordinate_minor_polynomial_eval, hZero]
  change Matrix.det A - Matrix.det (Matrix.updateRow A a ((1 : Matrix Iota Iota Real) a)) =
    Matrix.det (Matrix.updateRow A a w)
  linarith only [hAdd]

theorem hamiltonian_coordinate_pair_minor_polynomial_rows
    (M : Matrix Iota Iota Real) (a b : Iota) (hAB : Not (a = b)) (t : Real) :
    Polynomial.eval t (hamiltonianCoordinatePairMinorPolynomial M a b) =
      Matrix.det (Matrix.updateRow
        (Matrix.updateRow ((1 : Matrix Iota Iota Real) + HSMul.hSMul t M)
          a ((HSMul.hSMul t M) a)) b ((HSMul.hSMul t M) b)) := by
  let A := (1 : Matrix Iota Iota Real) + HSMul.hSMul t M
  let A1 := Matrix.updateRow A a ((HSMul.hSMul t M) a)
  have hSecond : Matrix.updateRow
      ((1 : Matrix Iota Iota Real) + HSMul.hSMul t (hamiltonianZeroRow M b))
      a ((HSMul.hSMul t (hamiltonianZeroRow M b)) a) =
        Matrix.updateRow A1 b ((1 : Matrix Iota Iota Real) b) := by
    apply Matrix.ext
    intro i j
    by_cases hiB : i = b
    case pos =>
      subst i
      simp [A1, A, hamiltonianZeroRow, Matrix.updateRow_apply, Matrix.add_apply,
        Matrix.smul_apply, smul_eq_mul, hAB, Ne.symm hAB]
    case neg =>
      by_cases hiA : i = a
      case pos =>
        subst i
        simp [A1, A, hamiltonianZeroRow, Matrix.updateRow_apply, Matrix.add_apply,
          Matrix.smul_apply, smul_eq_mul, hAB, Ne.symm hAB]
      case neg =>
        simp [A1, A, hamiltonianZeroRow, Matrix.updateRow_apply, Matrix.add_apply,
          Matrix.smul_apply, smul_eq_mul, hiA, hiB]
  have hRowB : A1 b = (1 : Matrix Iota Iota Real) b + (HSMul.hSMul t M) b := by
    dsimp only [A1]
    rw [Matrix.updateRow_ne (Ne.symm hAB)]
    rfl
  have hAdd := Matrix.det_updateRow_add A1 b ((1 : Matrix Iota Iota Real) b)
    ((HSMul.hSMul t M) b)
  rw [<- hRowB, Matrix.updateRow_eq_self] at hAdd
  rw [hamiltonianCoordinatePairMinorPolynomial, Polynomial.eval_sub,
    hamiltonian_coordinate_minor_polynomial_row, hamiltonian_coordinate_minor_polynomial_row,
    hSecond]
  change Matrix.det A1 - Matrix.det (Matrix.updateRow A1 b ((1 : Matrix Iota Iota Real) b)) =
    Matrix.det (Matrix.updateRow A1 b ((HSMul.hSMul t M) b))
  linarith only [hAdd]

theorem hamiltonian_resolvent_row_combination (M : Matrix Iota Iota Real)
    (t : Real) (hUnit : IsUnit ((1 : Matrix Iota Iota Real) + HSMul.hSMul t M)) (a : Iota) :
    Finset.univ.sum (fun k => HSMul.hSMul
      (resolventCovariance (HSMul.hSMul t M) a k)
        (((1 : Matrix Iota Iota Real) + HSMul.hSMul t M) k)) = (HSMul.hSMul t M) a := by
  let A := (1 : Matrix Iota Iota Real) + HSMul.hSMul t M
  let L := resolventCovariance (HSMul.hSMul t M)
  have hProduct : L * A = HSMul.hSMul t M := by
    change (HSMul.hSMul t M * Ring.inverse A) * A = _
    rw [mul_assoc, Ring.inverse_mul_cancel A hUnit, mul_one]
  funext j
  have h := congrFun (congrFun hProduct a) j
  simpa only [Matrix.mul_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using h

theorem hamiltonian_coordinate_minor_polynomial_resolvent
    (M : Matrix Iota Iota Real) (a : Iota) (t : Real)
    (hUnit : IsUnit ((1 : Matrix Iota Iota Real) + HSMul.hSMul t M)) :
    Polynomial.eval t (hamiltonianCoordinateMinorPolynomial M a) =
      Matrix.det ((1 : Matrix Iota Iota Real) + HSMul.hSMul t M) *
        resolventCovariance (HSMul.hSMul t M) a a := by
  let A := (1 : Matrix Iota Iota Real) + HSMul.hSMul t M
  let L := resolventCovariance (HSMul.hSMul t M)
  have hDet := Matrix.det_updateRow_sum A a (L a)
  rw [hamiltonian_resolvent_row_combination M t hUnit a] at hDet
  calc
    _ = Matrix.det (Matrix.updateRow A a ((HSMul.hSMul t M) a)) :=
      hamiltonian_coordinate_minor_polynomial_row M a t
    _ = L a a * Matrix.det A := hDet
    _ = _ := mul_comm _ _

theorem hamiltonian_coordinate_pair_minor_polynomial_resolvent
    (M : Matrix Iota Iota Real) (a b : Iota) (hAB : Not (a = b)) (t : Real)
    (hUnit : IsUnit ((1 : Matrix Iota Iota Real) + HSMul.hSMul t M)) :
    let L := resolventCovariance (HSMul.hSMul t M)
    Polynomial.eval t (hamiltonianCoordinatePairMinorPolynomial M a b) =
      Matrix.det ((1 : Matrix Iota Iota Real) + HSMul.hSMul t M) *
        (L a a * L b b - L a b * L b a) := by
  let A := (1 : Matrix Iota Iota Real) + HSMul.hSMul t M
  let L := resolventCovariance (HSMul.hSMul t M)
  have hDet := hamiltonian_two_row_linear_combination_det A a b hAB (L a) (L b)
  rw [hamiltonian_resolvent_row_combination M t hUnit a,
    hamiltonian_resolvent_row_combination M t hUnit b] at hDet
  calc
    _ = Matrix.det (Matrix.updateRow (Matrix.updateRow A a ((HSMul.hSMul t M) a))
        b ((HSMul.hSMul t M) b)) := hamiltonian_coordinate_pair_minor_polynomial_rows M a b hAB t
    _ = (L a a * L b b - L a b * L b a) * Matrix.det A := hDet
    _ = _ := mul_comm _ _

variable [Nonempty Iota]

theorem stochastic_coordinate_minor_polynomial_cleared
    (T : Matrix Iota Iota Real) (q tau : Real)
    (hq : (Fintype.card Iota : Real) * q = 1)
    (hRow : forall i, Finset.univ.sum (fun j => T i j) = 1)
    (hCol : forall j, Finset.univ.sum (fun i => T i j) = 1)
    (hTau0 : Not (tau = 0)) (hTau1 : Not (1 + tau = 0))
    (hUnit : IsUnit (hamiltonianParityRegularizedKernel T q tau)) (a : Sum Iota Iota) :
    let M := hamiltonianParityRegularizedKernel T q tau
    let A := (1 : Matrix (Sum Iota Iota) (Sum Iota Iota) Real) - Ring.inverse M
    Polynomial.eval (1 - tau) (hamiltonianCoordinateMinorPolynomial (bipartiteLift T) a) =
      Matrix.det M * (tau / (1 + tau) * A a a -
        hamiltonianParityProjection q a a / (1 + tau) ^ 2) := by
  have hSplit := stochastic_parity_resolvent_split T q tau hq hRow hCol hTau0 hTau1 hUnit
  rw [hamiltonian_coordinate_minor_polynomial_resolvent (bipartiteLift T) a (1 - tau) hSplit.1]
  exact stochastic_parity_one_coordinate_cleared T q tau hq hRow hCol hTau0 hTau1 hUnit a

theorem stochastic_coordinate_pair_minor_polynomial_cleared
    (T : Matrix Iota Iota Real) (q tau : Real)
    (hq : (Fintype.card Iota : Real) * q = 1)
    (hRow : forall i, Finset.univ.sum (fun j => T i j) = 1)
    (hCol : forall j, Finset.univ.sum (fun i => T i j) = 1)
    (hTau0 : Not (tau = 0)) (hTau1 : Not (1 + tau = 0))
    (hUnit : IsUnit (hamiltonianParityRegularizedKernel T q tau))
    (a b : Sum Iota Iota) (hAB : Not (a = b)) :
    let M := hamiltonianParityRegularizedKernel T q tau
    let A := (1 : Matrix (Sum Iota Iota) (Sum Iota Iota) Real) - Ring.inverse M
    Polynomial.eval (1 - tau) (hamiltonianCoordinatePairMinorPolynomial (bipartiteLift T) a b) =
      Matrix.det M * (tau / (1 + tau) * (A a a * A b b - A a b * A b a) -
        hamiltonianParityCrossForm q A a b / (1 + tau) ^ 2) := by
  have hSplit := stochastic_parity_resolvent_split T q tau hq hRow hCol hTau0 hTau1 hUnit
  rw [hamiltonian_coordinate_pair_minor_polynomial_resolvent (bipartiteLift T) a b hAB (1 - tau) hSplit.1]
  exact stochastic_parity_two_coordinate_cleared T q tau hq hRow hCol hTau0 hTau1 hUnit a b

end PrimeFactorOscillations

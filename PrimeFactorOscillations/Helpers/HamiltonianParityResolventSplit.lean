/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianParityRootRegularization

/-! # Exact signed clearing of the physical parity resolvent

The complete resolvent, regular inverse and parity pole are retained.
The apparent squared pole cancels by rank one, with both ordered
off-diagonal cross terms present. No bound replaces this identity.
-/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations

variable {Iota : Type*} [Fintype Iota] [DecidableEq Iota]

def hamiltonianParityCrossForm (q : Real)
    (A : Matrix (Sum Iota Iota) (Sum Iota Iota) Real) (a b : Sum Iota Iota) : Real :=
  hamiltonianParityProjection q a a * A b b +
    hamiltonianParityProjection q b b * A a a -
      hamiltonianParityProjection q a b * A b a -
        hamiltonianParityProjection q b a * A a b

theorem hamiltonian_parity_quadratic_cancellation (q c : Real)
    (A : Matrix (Sum Iota Iota) (Sum Iota Iota) Real) (a b : Sum Iota Iota) :
    (A a a - c * hamiltonianParityProjection q a a) *
        (A b b - c * hamiltonianParityProjection q b b) -
      (A a b - c * hamiltonianParityProjection q a b) *
        (A b a - c * hamiltonianParityProjection q b a) =
      A a a * A b b - A a b * A b a - c * hamiltonianParityCrossForm q A a b := by
  have hRankOne : hamiltonianParityProjection q a a * hamiltonianParityProjection q b b -
      hamiltonianParityProjection q a b * hamiltonianParityProjection q b a = 0 := by
    dsimp only [hamiltonianParityProjection]
    ring
  calc
    _ = A a a * A b b - A a b * A b a - c * hamiltonianParityCrossForm q A a b +
        c ^ 2 * (hamiltonianParityProjection q a a * hamiltonianParityProjection q b b -
          hamiltonianParityProjection q a b * hamiltonianParityProjection q b a) := by
      dsimp only [hamiltonianParityCrossForm]
      ring
    _ = _ := by rw [hRankOne, mul_zero, add_zero]

variable [Nonempty Iota]

theorem stochastic_regularized_left_parity_eigen (T : Matrix Iota Iota Real)
    (q tau : Real) (hq : (Fintype.card Iota : Real) * q = 1)
    (hRow : forall i, Finset.univ.sum (fun j => T i j) = 1)
    (hCol : forall j, Finset.univ.sum (fun i => T i j) = 1) :
    hamiltonianParityProjection q * hamiltonianParityRegularizedKernel T q tau =
      HSMul.hSMul (1 + tau) (hamiltonianParityProjection q) := by
  have hP := stochastic_parity_projection_mul_kernel T q hRow hCol
  have hS := hamiltonian_parity_projection_idempotent (Iota := Iota) q hq
  dsimp only [hamiltonianParityRegularizedKernel]
  simp only [mul_sub, mul_add, mul_one, Matrix.mul_smul, hP, hS]
  apply Matrix.ext
  intro i j
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.neg_apply,
    Matrix.smul_apply, smul_eq_mul]
  ring

theorem stochastic_regularized_inverse_parity (T : Matrix Iota Iota Real)
    (q tau : Real) (hq : (Fintype.card Iota : Real) * q = 1)
    (hRow : forall i, Finset.univ.sum (fun j => T i j) = 1)
    (hCol : forall j, Finset.univ.sum (fun i => T i j) = 1)
    (hTau : Not (1 + tau = 0)) (hUnit : IsUnit (hamiltonianParityRegularizedKernel T q tau)) :
    Ring.inverse (hamiltonianParityRegularizedKernel T q tau) * hamiltonianParityProjection q =
        HSMul.hSMul (1 / (1 + tau)) (hamiltonianParityProjection q) /\
    hamiltonianParityProjection q * Ring.inverse (hamiltonianParityRegularizedKernel T q tau) =
        HSMul.hSMul (1 / (1 + tau)) (hamiltonianParityProjection q) := by
  let M := hamiltonianParityRegularizedKernel T q tau
  let S := hamiltonianParityProjection (Iota := Iota) q
  let R := Ring.inverse M
  have hRight := stochastic_regularized_parity_eigen T q tau hq hRow hCol
  have hLeft := stochastic_regularized_left_parity_eigen T q tau hq hRow hCol
  have hDiv : (1 / (1 + tau)) * (1 + tau) = 1 := by field_simp [hTau]
  have hRightScale : HSMul.hSMul (1 + tau) (R * S) = S := by
    calc
      _ = R * HSMul.hSMul (1 + tau) S := by rw [Matrix.mul_smul]
      _ = R * (M * S) := by rw [hRight]
      _ = S := by rw [<- mul_assoc, Ring.inverse_mul_cancel M hUnit, one_mul]
  have hLeftScale : HSMul.hSMul (1 + tau) (S * R) = S := by
    calc
      _ = HSMul.hSMul (1 + tau) S * R := by rw [Matrix.smul_mul]
      _ = (S * M) * R := by rw [hLeft]
      _ = S := by rw [mul_assoc, Ring.mul_inverse_cancel M hUnit, mul_one]
  constructor
  case left =>
    change R * S = HSMul.hSMul (1 / (1 + tau)) S
    calc
      _ = HSMul.hSMul (1 / (1 + tau)) (HSMul.hSMul (1 + tau) (R * S)) := by
        rw [smul_smul, hDiv, one_smul]
      _ = _ := by rw [hRightScale]
  case right =>
    change S * R = HSMul.hSMul (1 / (1 + tau)) S
    calc
      _ = HSMul.hSMul (1 / (1 + tau)) (HSMul.hSMul (1 + tau) (S * R)) := by
        rw [smul_smul, hDiv, one_smul]
      _ = _ := by rw [hLeftScale]

theorem stochastic_parity_resolvent_split (T : Matrix Iota Iota Real)
    (q tau : Real) (hq : (Fintype.card Iota : Real) * q = 1)
    (hRow : forall i, Finset.univ.sum (fun j => T i j) = 1)
    (hCol : forall j, Finset.univ.sum (fun i => T i j) = 1)
    (hTau0 : Not (tau = 0)) (hTau1 : Not (1 + tau = 0))
    (hUnit : IsUnit (hamiltonianParityRegularizedKernel T q tau)) :
    let H : Matrix (Sum Iota Iota) (Sum Iota Iota) Real :=
      1 + HSMul.hSMul (1 - tau) (bipartiteLift T)
    IsUnit H /\
    Ring.inverse H = Ring.inverse (hamiltonianParityRegularizedKernel T q tau) +
      HSMul.hSMul (1 / (tau * (1 + tau))) (hamiltonianParityProjection q) /\
    resolventCovariance (HSMul.hSMul (1 - tau) (bipartiteLift T)) =
      1 - Ring.inverse (hamiltonianParityRegularizedKernel T q tau) -
        HSMul.hSMul (1 / (tau * (1 + tau))) (hamiltonianParityProjection q) := by
  let M := hamiltonianParityRegularizedKernel T q tau
  let S := hamiltonianParityProjection (Iota := Iota) q
  let R := Ring.inverse M
  let C := HSMul.hSMul (1 - tau) (bipartiteLift T)
  let H := (1 : Matrix (Sum Iota Iota) (Sum Iota Iota) Real) + C
  let c := 1 / (tau * (1 + tau))
  have hEigen := stochastic_regularized_parity_eigen T q tau hq hRow hCol
  have hSS := hamiltonian_parity_projection_idempotent (Iota := Iota) q hq
  have hInverseParity := stochastic_regularized_inverse_parity T q tau hq hRow hCol hTau1 hUnit
  have hHM : H = M - S := by
    apply Matrix.ext
    intro i j
    simp only [H, C, M, S, hamiltonianParityRegularizedKernel, Matrix.add_apply,
      Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
    ring
  have hHS : H * S = HSMul.hSMul tau S := by
    rw [hHM, sub_mul, hEigen, hSS]
    apply Matrix.ext
    intro i j
    simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
    ring
  have hScalar : c * tau = 1 / (1 + tau) := by dsimp only [c]; field_simp [hTau0, hTau1]
  have hProduct : H * (R + HSMul.hSMul c S) = 1 := by
    calc
      _ = H * R + HSMul.hSMul c (H * S) := by rw [mul_add, Matrix.mul_smul]
      _ = (M - S) * R + HSMul.hSMul c (HSMul.hSMul tau S) := by rw [hHS, hHM]
      _ = 1 - HSMul.hSMul (1 / (1 + tau)) S + HSMul.hSMul (c * tau) S := by
        rw [sub_mul, Ring.mul_inverse_cancel M hUnit, hInverseParity.2, smul_smul]
      _ = 1 := by rw [hScalar, sub_add_cancel]
  have hOther : (R + HSMul.hSMul c S) * H = 1 := _root_.mul_eq_one_comm.mp hProduct
  have hHUnit : IsUnit H := by
    refine Exists.intro
      ({ val := H, inv := R + HSMul.hSMul c S, val_inv := hProduct, inv_val := hOther } :
        Units (Matrix (Sum Iota Iota) (Sum Iota Iota) Real)) ?_
    rfl
  have hInverse : Ring.inverse H = R + HSMul.hSMul c S := by
    calc
      _ = ((R + HSMul.hSMul c S) * H) * Ring.inverse H := by rw [hOther, one_mul]
      _ = (R + HSMul.hSMul c S) * (H * Ring.inverse H) := mul_assoc _ _ _
      _ = _ := by rw [Ring.mul_inverse_cancel H hHUnit, mul_one]
  have hCov : resolventCovariance C = 1 - R - HSMul.hSMul c S := by
    change C * Ring.inverse H = _
    calc
      _ = (H - 1) * Ring.inverse H := by simp only [H, add_sub_cancel_left]
      _ = 1 - Ring.inverse H := by rw [sub_mul, Ring.mul_inverse_cancel H hHUnit, one_mul]
      _ = _ := by rw [hInverse]; abel
  exact And.intro hHUnit (And.intro hInverse hCov)

theorem stochastic_parity_one_coordinate_cleared (T : Matrix Iota Iota Real)
    (q tau : Real) (hq : (Fintype.card Iota : Real) * q = 1)
    (hRow : forall i, Finset.univ.sum (fun j => T i j) = 1)
    (hCol : forall j, Finset.univ.sum (fun i => T i j) = 1)
    (hTau0 : Not (tau = 0)) (hTau1 : Not (1 + tau = 0))
    (hUnit : IsUnit (hamiltonianParityRegularizedKernel T q tau)) (a : Sum Iota Iota) :
    let M := hamiltonianParityRegularizedKernel T q tau
    let A := (1 : Matrix (Sum Iota Iota) (Sum Iota Iota) Real) - Ring.inverse M
    let L := resolventCovariance (HSMul.hSMul (1 - tau) (bipartiteLift T))
    Matrix.det ((1 : Matrix (Sum Iota Iota) (Sum Iota Iota) Real) +
      HSMul.hSMul (1 - tau) (bipartiteLift T)) * L a a =
        Matrix.det M * (tau / (1 + tau) * A a a -
          hamiltonianParityProjection q a a / (1 + tau) ^ 2) := by
  let M := hamiltonianParityRegularizedKernel T q tau
  let A := (1 : Matrix (Sum Iota Iota) (Sum Iota Iota) Real) - Ring.inverse M
  let L := resolventCovariance (HSMul.hSMul (1 - tau) (bipartiteLift T))
  have hSplit := (stochastic_parity_resolvent_split T q tau hq hRow hCol hTau0 hTau1 hUnit).2.2
  have hEntry : L a a = A a a -
      (1 / (tau * (1 + tau))) * hamiltonianParityProjection q a a := by
    exact congrFun (congrFun hSplit a) a
  change _ * L a a = Matrix.det M * _
  rw [stochastic_parity_regularization_det T q tau hq hRow hCol hTau1, hEntry]
  field_simp [hTau0, hTau1]
  <;> ring

theorem stochastic_parity_two_coordinate_cleared (T : Matrix Iota Iota Real)
    (q tau : Real) (hq : (Fintype.card Iota : Real) * q = 1)
    (hRow : forall i, Finset.univ.sum (fun j => T i j) = 1)
    (hCol : forall j, Finset.univ.sum (fun i => T i j) = 1)
    (hTau0 : Not (tau = 0)) (hTau1 : Not (1 + tau = 0))
    (hUnit : IsUnit (hamiltonianParityRegularizedKernel T q tau)) (a b : Sum Iota Iota) :
    let M := hamiltonianParityRegularizedKernel T q tau
    let A := (1 : Matrix (Sum Iota Iota) (Sum Iota Iota) Real) - Ring.inverse M
    let L := resolventCovariance (HSMul.hSMul (1 - tau) (bipartiteLift T))
    Matrix.det ((1 : Matrix (Sum Iota Iota) (Sum Iota Iota) Real) +
      HSMul.hSMul (1 - tau) (bipartiteLift T)) * (L a a * L b b - L a b * L b a) =
        Matrix.det M * (tau / (1 + tau) * (A a a * A b b - A a b * A b a) -
          hamiltonianParityCrossForm q A a b / (1 + tau) ^ 2) := by
  let M := hamiltonianParityRegularizedKernel T q tau
  let A := (1 : Matrix (Sum Iota Iota) (Sum Iota Iota) Real) - Ring.inverse M
  let L := resolventCovariance (HSMul.hSMul (1 - tau) (bipartiteLift T))
  have hSplit := (stochastic_parity_resolvent_split T q tau hq hRow hCol hTau0 hTau1 hUnit).2.2
  have hEntry (i j : Sum Iota Iota) : L i j = A i j -
      (1 / (tau * (1 + tau))) * hamiltonianParityProjection q i j :=
    congrFun (congrFun hSplit i) j
  change _ * (L a a * L b b - L a b * L b a) = Matrix.det M * _
  rw [stochastic_parity_regularization_det T q tau hq hRow hCol hTau1]
  simp only [hEntry]
  rw [hamiltonian_parity_quadratic_cancellation]
  field_simp [hTau0, hTau1]
  <;> ring

end PrimeFactorOscillations

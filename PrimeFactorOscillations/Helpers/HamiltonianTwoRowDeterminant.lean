/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianRectangularMinors

/-! # Complete one- and two-row determinant coefficients

These exact coefficients retain the off-diagonal subtraction. They
are the row-occupancy factors used before taking the parity-root limit.
No invertibility or positivity hypothesis is needed here.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

variable {Iota R : Type*} [Fintype Iota] [DecidableEq Iota] [CommRing R]

theorem hamiltonian_one_row_identity_det (a : Iota) (c : Iota -> R) :
    Matrix.det (Matrix.updateRow (1 : Matrix Iota Iota R) a c) = c a := by
  have hVector : Finset.univ.sum (fun k => HSMul.hSMul (c k) ((1 : Matrix Iota Iota R) k)) = c := by
    funext j
    simp [Finset.sum_apply, Pi.smul_apply, Matrix.one_apply, smul_eq_mul, mul_ite]
  have h := Matrix.det_updateRow_sum (1 : Matrix Iota Iota R) a c
  rw [hVector, Matrix.det_one] at h
  simpa only [smul_eq_mul, mul_one] using h

theorem hamiltonian_two_row_identity_det (a b : Iota) (hAB : Not (a = b))
    (c d : Iota -> R) :
    Matrix.det (Matrix.updateRow (Matrix.updateRow (1 : Matrix Iota Iota R) a c) b d) =
      c a * d b - c b * d a := by
  let E : Matrix Iota (Fin 2) R := fun i k =>
    if k = 0 then (if i = a then 1 else 0) else (if i = b then 1 else 0)
  let V : Matrix (Fin 2) Iota R := fun k j =>
    if k = 0 then c j - (1 : Matrix Iota Iota R) a j
    else d j - (1 : Matrix Iota Iota R) b j
  have hJ : Matrix.updateRow (Matrix.updateRow (1 : Matrix Iota Iota R) a c) b d =
      1 + E * V := by
    apply Matrix.ext
    intro i j
    simp only [Matrix.add_apply, Matrix.mul_apply, Fin.sum_univ_two]
    by_cases hiB : i = b
    case pos =>
      subst i
      simp [E, V, Matrix.updateRow_apply,
        Matrix.one_apply, hAB, Ne.symm hAB]
    case neg =>
      by_cases hiA : i = a
      case pos =>
        subst i
        simp [E, V, Matrix.updateRow_apply,
          Matrix.one_apply, hAB, Ne.symm hAB]
      case neg =>
        simp [E, V, Matrix.updateRow_apply,
          Matrix.one_apply, hiB, hiA]
  have hSmall : Matrix.det ((1 : Matrix (Fin 2) (Fin 2) R) + V * E) =
      c a * d b - c b * d a := by
    rw [Matrix.det_fin_two]
    simp only [Matrix.add_apply, Matrix.mul_apply]
    simp [E, V, Matrix.one_apply, mul_ite, hAB, Ne.symm hAB]
  rw [hJ, Matrix.det_one_add_mul_comm, hSmall]

theorem hamiltonian_two_row_linear_combination_det
    (A : Matrix Iota Iota R) (a b : Iota) (hAB : Not (a = b)) (c d : Iota -> R) :
    Matrix.det (Matrix.updateRow
      (Matrix.updateRow A a (Finset.univ.sum (fun k => HSMul.hSMul (c k) (A k))))
      b (Finset.univ.sum (fun k => HSMul.hSMul (d k) (A k)))) =
        (c a * d b - c b * d a) * Matrix.det A := by
  let J := Matrix.updateRow (Matrix.updateRow (1 : Matrix Iota Iota R) a c) b d
  have hFactor : Matrix.updateRow
      (Matrix.updateRow A a (Finset.univ.sum (fun k => HSMul.hSMul (c k) (A k))))
      b (Finset.univ.sum (fun k => HSMul.hSMul (d k) (A k))) = J * A := by
    apply Matrix.ext
    intro i j
    by_cases hiB : i = b
    case pos =>
      subst i
      simp [J, Matrix.mul_apply, Matrix.updateRow_apply, Finset.sum_apply,
        Pi.smul_apply, smul_eq_mul]
    case neg =>
      by_cases hiA : i = a
      case pos =>
        subst i
        simp [J, Matrix.mul_apply, Matrix.updateRow_apply, Finset.sum_apply,
          Pi.smul_apply, smul_eq_mul, hAB]
      case neg =>
        simp [J, Matrix.mul_apply, Matrix.updateRow_apply, Matrix.one_apply,
          hiA, hiB, mul_ite]
  rw [hFactor, Matrix.det_mul]
  change Matrix.det (Matrix.updateRow (Matrix.updateRow (1 : Matrix Iota Iota R) a c) b d) *
    Matrix.det A = _
  rw [hamiltonian_two_row_identity_det a b hAB c d]

end PrimeFactorOscillations

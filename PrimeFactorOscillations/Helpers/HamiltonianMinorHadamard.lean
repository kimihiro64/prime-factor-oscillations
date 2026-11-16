/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Tactic.FieldSimp
import PrimeFactorOscillations.Helpers.HamiltonianTiltedMinorMass

/-! # Local determinant control for the aperiodic ratio error

These estimates are applied to the residual after the signed principal
minor sum has been evaluated. They do not replace its leading determinant.
The Gram spectrum is kept whole before the positive exponential estimate.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

variable {Iota : Type*} [Fintype Iota] [DecidableEq Iota]

theorem hamiltonian_gram_scaled_det_exp_bound
    (M : Matrix Iota Iota Real) (t : Real) (ht : 0 <= t) :
    t ^ Fintype.card Iota * Matrix.det M ^ 2 <=
      Real.exp (t * Finset.univ.sum
        (fun i => Finset.univ.sum (fun j => M i j ^ 2))) := by
  let G := M.transpose * M
  let hG := realGramHermitian M
  have hEigen (i : Iota) : 0 <= t * hG.eigenvalues i :=
    mul_nonneg ht (realGramEigenvalues_nonnegative M i)
  have hProd :
      t ^ Fintype.card Iota * Matrix.det M ^ 2 =
        Finset.univ.prod (fun i => t * hG.eigenvalues i) := by
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
    congr 1
    have hDet : Matrix.det G = Matrix.det M ^ 2 := by
      dsimp only [G]
      rw [Matrix.det_mul, Matrix.det_transpose]
      ring
    rw [<- hDet]
    exact hG.det_eq_prod_eigenvalues
  have hTrace : Matrix.trace G =
      Finset.univ.sum (fun i => Finset.univ.sum (fun j => M i j ^ 2)) := by
    rw [hG.trace_eq_sum_eigenvalues]
    exact realGramEigenvalues_sum_eq_energy M
  calc
    _ = Finset.univ.prod (fun i => t * hG.eigenvalues i) := hProd
    _ <= Finset.univ.prod (fun i => 1 + t * hG.eigenvalues i) := by
      have hPoint (i : Iota) : t * hG.eigenvalues i <= 1 + t * hG.eigenvalues i := by
        linarith
      gcongr with i hi
      all_goals first
        | exact fun i _ => hEigen i
        | exact fun i _ => hPoint i
        | exact hEigen _
        | exact hPoint _
    _ = Matrix.det ((1 : Matrix Iota Iota Real) + HSMul.hSMul t G) := by
      simpa only [neg_smul, sub_neg_eq_add, neg_mul, neg_neg] using
        (hermitian_det_one_sub_smul G hG (-t)).symm
    _ <= Real.exp (t * Matrix.trace G) :=
      hamiltonian_hermitian_positive_det_exp_bound G hG
        (fun i => realGramEigenvalues_nonnegative M i) t ht
    _ = _ := by rw [hTrace]

theorem hamiltonian_local_minor_hadamard_budget
    (M : Matrix Iota Iota Real) (c : Real)
    (hc : 0 < c) (hr : 0 < Fintype.card Iota)
    (hEntry : forall i j, abs (M i j) <= c) :
    Matrix.det M ^ 2 <=
      Real.exp (Fintype.card Iota : Real) *
        ((Fintype.card Iota : Real) * c ^ 2) ^ Fintype.card Iota := by
  let r : Real := Fintype.card Iota
  let k : Real := r * c ^ 2
  have hr0 : 0 < r := by dsimp [r]; exact_mod_cast hr
  have hk : 0 < k := mul_pos hr0 (sq_pos_of_pos hc)
  have hEnergy :
      Finset.univ.sum (fun i => Finset.univ.sum (fun j => M i j ^ 2)) <= r * k := by
    calc
      _ <= Finset.univ.sum (fun _ : Iota =>
        Finset.univ.sum (fun _ : Iota => c ^ 2)) := by
          apply Finset.sum_le_sum
          intro i hi
          apply Finset.sum_le_sum
          intro j hj
          have h := hEntry i j
          have hAbs := abs_nonneg (M i j)
          nlinarith only [sq_abs (M i j), h, hAbs, hc]
      _ = r * k := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        dsimp [r, k]
  have h := hamiltonian_gram_scaled_det_exp_bound M (1 / k)
    (le_of_lt (one_div_pos.mpr hk))
  have hExp : Real.exp ((1 / k) *
      Finset.univ.sum (fun i => Finset.univ.sum (fun j => M i j ^ 2))) <=
      Real.exp r := by
    apply Real.exp_le_exp.mpr
    calc
      _ <= (1 / k) * (r * k) :=
        mul_le_mul_of_nonneg_left hEnergy (le_of_lt (one_div_pos.mpr hk))
      _ = r := by field_simp
  have hScaled := mul_le_mul_of_nonneg_right (h.trans hExp)
    (pow_nonneg hk.le (Fintype.card Iota))
  have hCancel : (1 / k) ^ Fintype.card Iota *
      Matrix.det M ^ 2 * k ^ Fintype.card Iota = Matrix.det M ^ 2 := by
    calc
      _ = ((1 / k) * k) ^ Fintype.card Iota * Matrix.det M ^ 2 := by
        rw [mul_pow]
        ring
      _ = _ := by rw [one_div_mul_cancel (ne_of_gt hk), one_pow, one_mul]
  rw [hCancel] at hScaled
  exact hScaled

end PrimeFactorOscillations

/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianMatrixSpectralAverage

/-! # The exact symmetric determinant factor in graph entropy

Both determinant signs are proved from the actual spectral gap.
The square-root quotient is used only on that positive domain.
-/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations

variable {Iota : Type*} [Fintype Iota] [DecidableEq Iota] [Nonempty Iota]

theorem hamiltonian_symmetric_gap_determinants
    (B : Matrix Iota Iota Real) (hSym : B.transpose = B)
    (rho : Real) (hRho : rho < 1) (hNorm : norm B <= rho) :
    0 < Matrix.det ((1 : Matrix Iota Iota Real) - B) /\
      0 < Matrix.det ((1 : Matrix Iota Iota Real) + B) := by
  have hHermitian : B.IsHermitian := by
    change B.conjTranspose = B
    ext i j
    change B j i = B i j
    exact congrArg (fun M : Matrix Iota Iota Real => M i j) hSym
  have hEigen (i : Iota) : abs (hHermitian.eigenvalues i) <= rho := by
    have hMem := hHermitian.eigenvalues_mem_spectrum_real i
    have h := _root_.spectrum.norm_le_norm_of_mem hMem
    change norm (hHermitian.eigenvalues i) <= norm B at h
    simpa only [Real.norm_eq_abs] using h.trans hNorm
  have hMinus : Matrix.det ((1 : Matrix Iota Iota Real) - B) =
      Finset.univ.prod (fun i => 1 - hHermitian.eigenvalues i) := by
    simpa only [one_smul, one_mul] using hermitian_det_one_sub_smul B hHermitian 1
  have hPlus : Matrix.det ((1 : Matrix Iota Iota Real) + B) =
      Finset.univ.prod (fun i => 1 + hHermitian.eigenvalues i) := by
    simpa only [neg_one_smul, sub_neg_eq_add, neg_one_mul] using
      hermitian_det_one_sub_smul B hHermitian (-1)
  constructor
  case left =>
    rw [hMinus]
    apply Finset.prod_pos
    intro i hi
    have h := (abs_le.mp (hEigen i)).2
    linarith only [h, hRho]
  case right =>
    rw [hPlus]
    apply Finset.prod_pos
    intro i hi
    have h := (abs_le.mp (hEigen i)).1
    linarith only [h, hRho]

theorem hamiltonian_symmetric_gram_determinant
    (B : Matrix Iota Iota Real) (hSym : B.transpose = B) :
    Matrix.det ((1 : Matrix Iota Iota Real) - B.transpose * B) =
      Matrix.det ((1 : Matrix Iota Iota Real) - B) *
        Matrix.det ((1 : Matrix Iota Iota Real) + B) := by
  have hFactor : ((1 : Matrix Iota Iota Real) - B) * (1 + B) = 1 - B * B := by
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_add, Matrix.mul_one]
    abel
  rw [hSym, <- hFactor, Matrix.det_mul]

theorem hamiltonian_symmetric_gram_factor_quotient
    (B : Matrix Iota Iota Real) (hSym : B.transpose = B)
    (rho : Real) (hRho : rho < 1) (hNorm : norm B <= rho) :
    Matrix.det ((1 : Matrix Iota Iota Real) - B) * realGramDeterminantFactor B 1 =
      Real.sqrt (Matrix.det ((1 : Matrix Iota Iota Real) - B) /
        Matrix.det ((1 : Matrix Iota Iota Real) + B)) := by
  have hData := hamiltonian_symmetric_gap_determinants B hSym rho hRho hNorm
  have hGram := hamiltonian_symmetric_gram_determinant B hSym
  have hGramPos : 0 < Matrix.det ((1 : Matrix Iota Iota Real) - B.transpose * B) := by
    rw [hGram]
    exact mul_pos hData.1 hData.2
  unfold realGramDeterminantFactor
  simp only [one_pow, one_smul]
  change Matrix.det ((1 : Matrix Iota Iota Real) - B) *
    (Matrix.det ((1 : Matrix Iota Iota Real) - B.transpose * B)) ^ (-(1 / 2 : Real)) = _
  rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos (div_pos hData.1 hData.2),
    Real.rpow_def_of_pos hGramPos]
  calc
    _ = Real.exp
        (Real.log (Matrix.det ((1 : Matrix Iota Iota Real) - B)) +
          Real.log (Matrix.det ((1 : Matrix Iota Iota Real) - B.transpose * B)) *
            (-(1 / 2 : Real))) := by
      rw [Real.exp_add, Real.exp_log hData.1]
    _ = _ := by
      congr 1
      rw [hGram, Real.log_mul (ne_of_gt hData.1) (ne_of_gt hData.2),
        Real.log_div (ne_of_gt hData.1) (ne_of_gt hData.2)]
      ring

end PrimeFactorOscillations

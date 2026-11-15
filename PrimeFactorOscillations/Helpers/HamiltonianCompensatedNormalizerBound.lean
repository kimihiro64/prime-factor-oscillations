/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianCompensatedGaussianNormalizer

/-! # Trace-cancelled complex normalizer and full rook circle bound

The complete linear spectral term cancels by the zero trace of the actual
bipartite block before the normalizer is bounded. Its cost is quadratic
spectral energy, not the absolute sum of eigenvalues.
-/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations

variable {Iota : Type*} [Fintype Iota] [DecidableEq Iota]

theorem complex_one_add_norm_exp_bound (z : Complex) :
    norm (1 + z) <= Real.exp (z.re + norm z ^ 2 / 2) := by
  have hSq : norm (1 + z) ^ 2 = 1 + 2 * z.re + norm z ^ 2 := by
    simp only [<- Complex.normSq_eq_norm_sq, Complex.normSq_apply,
      Complex.add_re, Complex.add_im, Complex.one_re, Complex.one_im]
    ring
  have hExpSq : Real.exp (z.re + norm z ^ 2 / 2) ^ 2 =
      Real.exp (2 * z.re + norm z ^ 2) := by
    rw [pow_two, <- Real.exp_add]
    congr 1
    ring
  have hBound : norm (1 + z) ^ 2 <= Real.exp (2 * z.re + norm z ^ 2) := by
    rw [hSq]
    have h := Real.add_one_le_exp (2 * z.re + norm z ^ 2)
    linarith only [h]
  rw [<- hExpSq] at hBound
  nlinarith [norm_nonneg (1 + z), (Real.exp_pos (z.re + norm z ^ 2 / 2))]

theorem complex_one_add_product_bound (z : Iota -> Complex) :
    Finset.prod Finset.univ (fun j => norm (1 + z j)) <=
      Real.exp (Finset.sum Finset.univ (fun j => (z j).re) +
        Finset.sum Finset.univ (fun j => norm (z j) ^ 2) / 2) := by
  have hAll : forall S : Finset Iota,
      Finset.prod S (fun j => norm (1 + z j)) <=
        Real.exp (Finset.sum S (fun j => (z j).re) +
          Finset.sum S (fun j => norm (z j) ^ 2) / 2) := by
    intro S
    induction S using Finset.induction_on with
    | empty => simp
    | @insert j S hj ih =>
      rw [Finset.prod_insert hj, Finset.sum_insert hj, Finset.sum_insert hj]
      calc
        _ <= Real.exp ((z j).re + norm (z j) ^ 2 / 2) *
            Real.exp (Finset.sum S (fun i => (z i).re) +
              Finset.sum S (fun i => norm (z i) ^ 2) / 2) :=
          mul_le_mul (complex_one_add_norm_exp_bound (z j)) ih
            (Finset.prod_nonneg (fun i _ => norm_nonneg _)) (Real.exp_pos _).le
        _ = _ := by rw [<- Real.exp_add]; congr 1; ring
  exact hAll Finset.univ

theorem gaussianTensorTiltNormalizer_ratio_bound (z : Iota -> Complex)
    (hz : forall j, norm (z j) < 1) :
    norm (gaussianTensorTiltNormalizer z /
        ((realStandardGaussianNormalizer ^ Fintype.card Iota : Real) : Complex)) <=
      Real.exp (Finset.sum Finset.univ (fun j => (z j).re) / 2 +
        Finset.sum Finset.univ (fun j => norm (z j) ^ 2) / 4) := by
  let Z := gaussianTensorTiltNormalizer z /
    ((realStandardGaussianNormalizer ^ Fintype.card Iota : Real) : Complex)
  have hSq : norm Z ^ 2 = Finset.prod Finset.univ (fun j => norm (1 + z j)) := by
    have h := congrArg norm (gaussianTensorTiltNormalizer_ratio_sq z hz)
    simpa only [norm_pow, norm_prod] using h
  have hBound := complex_one_add_product_bound z
  rw [<- hSq] at hBound
  have hExpSq : Real.exp
      (Finset.sum Finset.univ (fun j => (z j).re) / 2 +
        Finset.sum Finset.univ (fun j => norm (z j) ^ 2) / 4) ^ 2 =
      Real.exp (Finset.sum Finset.univ (fun j => (z j).re) +
        Finset.sum Finset.univ (fun j => norm (z j) ^ 2) / 2) := by
    rw [pow_two, <- Real.exp_add]
    congr 1
    ring
  rw [<- hExpSq] at hBound
  nlinarith [norm_nonneg Z, Real.exp_pos
    (Finset.sum Finset.univ (fun j => (z j).re) / 2 +
      Finset.sum Finset.univ (fun j => norm (z j) ^ 2) / 4)]

theorem realGaussianTiltNormalizer_trace_bound (M : Matrix Iota Iota Real)
    (hM : M.IsHermitian) (s : Complex) (E : Real)
    (hDisk : forall j, norm (s * realGaussianEigenVariances M hM j) < 1)
    (hTrace : Finset.sum Finset.univ hM.eigenvalues = 0)
    (hEnergy : Finset.sum Finset.univ (fun j => hM.eigenvalues j ^ 2) <= E) :
    norm (gaussianTensorTiltNormalizer (fun j => s * realGaussianEigenVariances M hM j) /
        ((realStandardGaussianNormalizer ^ Fintype.card Iota : Real) : Complex)) <=
      Real.exp (norm s ^ 2 * E / 4) := by
  have hLinear : Finset.sum Finset.univ
      (fun j => (s * realGaussianEigenVariances M hM j).re) = 0 := by
    simp only [realGaussianEigenVariances, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    rw [<- Finset.mul_sum, hTrace, mul_zero]
  have hSquare : Finset.sum Finset.univ
      (fun j => norm (s * realGaussianEigenVariances M hM j) ^ 2) =
        norm s ^ 2 * Finset.sum Finset.univ (fun j => hM.eigenvalues j ^ 2) := by
    simp only [realGaussianEigenVariances, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, mul_pow, sq_abs, Finset.mul_sum]
  have h := gaussianTensorTiltNormalizer_ratio_bound
    (fun j => s * realGaussianEigenVariances M hM j) hDisk
  rw [hLinear, hSquare, zero_div, zero_add] at h
  exact le_trans h (Real.exp_le_exp.mpr
    (by nlinarith only [mul_le_mul_of_nonneg_left hEnergy (sq_nonneg (norm s))]))

theorem bipartite_eigenvalue_sum_zero (B : Matrix Iota Iota Real) :
    Finset.sum Finset.univ (bipartiteLift_hermitian B).eigenvalues = 0 := by
  have hTrace : Matrix.trace (bipartiteLift B) =
      Finset.sum Finset.univ (bipartiteLift_hermitian B).eigenvalues := by
    simpa using (bipartiteLift_hermitian B).trace_eq_sum_eigenvalues
  rw [<- hTrace]
  unfold Matrix.trace
  apply Finset.sum_eq_zero
  intro i hi
  cases i <;> simp [bipartiteLift, Matrix.fromBlocks]

theorem bipartite_square_energy (B : Matrix Iota Iota Real) :
    matrixSquareEnergy (bipartiteLift B) = 2 * matrixSquareEnergy B := by
  unfold matrixSquareEnergy
  simp only [Fintype.sum_sum_type]
  have hTransposeEnergy :
      Finset.sum Finset.univ (fun i => Finset.sum Finset.univ (fun j => B j i ^ 2)) =
        Finset.sum Finset.univ (fun i => Finset.sum Finset.univ (fun j => B i j ^ 2)) :=
    Finset.sum_comm
  simp [bipartiteLift, Matrix.fromBlocks, Matrix.transpose_apply]
  linarith only [hTransposeEnergy]

theorem bipartite_eigen_disk (B : Matrix Iota Iota Real) (rho : Real) (s : Complex)
    (hNorm : norm B <= rho) (hGap : 0 < 1 - norm s * rho)
    (j : Sum Iota Iota) :
    norm (s * realGaussianEigenVariances (bipartiteLift B)
      (bipartiteLift_hermitian B) j) < 1 := by
  have hEigen := le_trans
    (realGaussianEigenvalue_abs_le_norm (bipartiteLift B) (bipartiteLift_hermitian B) j)
    (le_trans (bipartiteLift_l2_norm_le B) hNorm)
  simp only [realGaussianEigenVariances, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have h := mul_le_mul_of_nonneg_left hEigen (norm_nonneg s)
  linarith only [h, hGap]

theorem stochastic_complex_normalizer_bound {n : Nat}
    (T : Matrix (Fin n) (Fin n) Real) (q a rho : Real) (s : Complex)
    (hq : (n : Real) * q = 1)
    (hRow : forall i, Finset.sum Finset.univ (fun j => T i j) = 1)
    (hNonneg : forall i j, 0 <= T i j) (hUpper : forall i j, T i j <= a * q)
    (hNorm : norm (centeredKernel T q) <= rho) (hGap : 0 < 1 - norm s * rho) :
    norm (gaussianTensorTiltNormalizer (fun j => s *
        realGaussianEigenVariances (bipartiteLift (centeredKernel T q))
          (bipartiteLift_hermitian (centeredKernel T q)) j) /
        ((realStandardGaussianNormalizer ^
          Fintype.card (Sum (Fin n) (Fin n)) : Real) : Complex)) <=
      Real.exp (norm s ^ 2 * (a - 1) / 2) := by
  have hEnergy : Finset.sum Finset.univ
      (fun j => (bipartiteLift_hermitian (centeredKernel T q)).eigenvalues j ^ 2) <=
        2 * (a - 1) := by
    rw [realGaussianEigenvalue_square_energy, bipartite_square_energy]
    exact mul_le_mul_of_nonneg_left
      (stochastic_total_energy T q a
        (by simpa only [Fintype.card_fin] using hq) hRow hNonneg hUpper) (by norm_num)
  have h := realGaussianTiltNormalizer_trace_bound
    (bipartiteLift (centeredKernel T q)) (bipartiteLift_hermitian (centeredKernel T q))
    s (2 * (a - 1)) (bipartite_eigen_disk _ rho s hNorm hGap)
    (bipartite_eigenvalue_sum_zero _) hEnergy
  convert! h using 1 <;> congr 1 <;> ring

def hamiltonianCompensatedRook {n : Nat} (B : Matrix (Fin n) (Fin n) Real)
    (s : Complex) : Complex :=
  hamiltonianComplexRookPolynomial B s *
    (gaussianTensorTiltNormalizer (fun j => s *
      realGaussianEigenVariances (bipartiteLift B) (bipartiteLift_hermitian B) j) /
      ((realStandardGaussianNormalizer ^ Fintype.card (Sum (Fin n) (Fin n)) : Real) : Complex))

theorem stochastic_compensated_rook_circle_bound {n : Nat}
    (T : Matrix (Fin n) (Fin n) Real) (q a rho : Real) (s : Complex)
    (hq : (n : Real) * q = 1) (ha : 1 <= a)
    (hRow : forall i, Finset.sum Finset.univ (fun j => T i j) = 1)
    (hCol : forall j, Finset.sum Finset.univ (fun i => T i j) = 1)
    (hNonneg : forall i j, 0 <= T i j) (hUpper : forall i j, T i j <= a * q)
    (hNorm : norm (centeredKernel T q) <= rho) (hGap : 0 < 1 - norm s * rho) :
    norm (hamiltonianCompensatedRook (centeredKernel T q) s) <=
      Real.exp (2 * norm s / (1 - norm s * rho) * Real.sqrt ((n : Real) * (a - 1)) +
        norm s ^ 2 * (a - 1) / 2) := by
  unfold hamiltonianCompensatedRook
  rw [norm_mul, Real.exp_add]
  exact mul_le_mul
    (hamiltonianComplexRookPolynomial_stochastic_bound T q a rho s
      hq ha hRow hCol hNonneg hUpper hNorm hGap)
    (stochastic_complex_normalizer_bound T q a rho s
      hq hRow hNonneg hUpper hNorm hGap)
    (norm_nonneg _) (Real.exp_pos _).le


theorem hamiltonianCompensatedRook_eq_average {n : Nat}
    (B : Matrix (Fin n) (Fin n) Real) (s : Complex)
    (hCol : forall j, Finset.sum Finset.univ (fun i => bipartiteLift B i j) = 0)
    (hDisk : forall j, norm (s * realGaussianEigenVariances (bipartiteLift B)
      (bipartiteLift_hermitian B) j) < 1) :
    hamiltonianCompensatedRook B s =
      realGaussianCompensatedAverage (bipartiteLift B) (bipartiteLift_hermitian B) s := by
  have hId := realGaussianCompensatedAverage_rook B s hCol hDisk
  have hZ := gaussianTensorTiltNormalizer_nonzero
    (fun j => s * realGaussianEigenVariances (bipartiteLift B)
      (bipartiteLift_hermitian B) j) hDisk
  have hStd : Not (((realStandardGaussianNormalizer ^
      Fintype.card (Sum (Fin n) (Fin n)) : Real) : Complex) = 0) := by
    exact_mod_cast (pow_ne_zero (Fintype.card (Sum (Fin n) (Fin n)))
      (ne_of_gt realStandardGaussianNormalizer_positive))
  unfold hamiltonianCompensatedRook
  rw [hId]
  field_simp

theorem hamiltonianComplexRookPolynomial_at_zero {n : Nat}
    (B : Matrix (Fin n) (Fin n) Real) :
    hamiltonianComplexRookPolynomial B 0 = 1 := by
  have hId := realGaussianAffinePolynomial_rook B (0 : Complex)
  have hPoly : realGaussianAffinePolynomial (bipartiteLift B)
      (bipartiteLift_hermitian B) 0 = 1 := by
    simp [realGaussianAffinePolynomial]
  rw [hPoly, gaussianPolynomialState_one] at hId
  have hPower : (0 : Complex) ^ 2 = 0 := by ring
  rw [hPower] at hId
  exact hId.symm

theorem hamiltonianCompensatedRook_at_zero {n : Nat}
    (B : Matrix (Fin n) (Fin n) Real) : hamiltonianCompensatedRook B 0 = 1 := by
  unfold hamiltonianCompensatedRook
  simp only [hamiltonianComplexRookPolynomial_at_zero, zero_mul, one_mul]
  rw [standardGaussianTensor_normalizer_real]
  have hStd : Not (((realStandardGaussianNormalizer ^
      Fintype.card (Sum (Fin n) (Fin n)) : Real) : Complex) = 0) := by
    exact_mod_cast (pow_ne_zero (Fintype.card (Sum (Fin n) (Fin n)))
      (ne_of_gt realStandardGaussianNormalizer_positive))
  field_simp

theorem stochastic_compensated_rook_gaussian_identity {n : Nat}
    (T : Matrix (Fin n) (Fin n) Real) (q rho : Real) (s : Complex)
    (hq : (n : Real) * q = 1)
    (hRow : forall i, Finset.sum Finset.univ (fun j => T i j) = 1)
    (hCol : forall j, Finset.sum Finset.univ (fun i => T i j) = 1)
    (hNorm : norm (centeredKernel T q) <= rho) (hGap : 0 < 1 - norm s * rho) :
    hamiltonianCompensatedRook (centeredKernel T q) s =
      realGaussianCompensatedAverage (bipartiteLift (centeredKernel T q))
        (bipartiteLift_hermitian (centeredKernel T q)) s := by
  apply hamiltonianCompensatedRook_eq_average
  exact centered_bipartite_column_sum_zero T q
    (by simpa only [Fintype.card_fin] using hq) hRow hCol
  exact bipartite_eigen_disk _ rho s hNorm hGap

end PrimeFactorOscillations

/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianGaussianTiltNormalizer

/-! # Positive determinant normalization of the actual compensated integral

The real normalizer is identified by its positive sign and exact square.
The stochastic window consumer discharges the complete eigenvalue disk.
-/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations

variable {Iota : Type*} [Fintype Iota] [DecidableEq Iota]

theorem hermitian_det_one_add_smul (M : Matrix Iota Iota Real)
    (hM : M.IsHermitian) (s : Real) :
    Matrix.det ((1 : Matrix Iota Iota Real) + HSMul.hSMul s M) =
      Finset.prod Finset.univ (fun j => 1 + s * hM.eigenvalues j) := by
  have h := hermitian_det_one_sub_smul M hM (-s)
  have hMat : (1 : Matrix Iota Iota Real) - HSMul.hSMul (-s) M =
      (1 : Matrix Iota Iota Real) + HSMul.hSMul s M := by
    ext i j
    simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    ring
  rw [hMat] at h
  simpa only [neg_mul, sub_neg_eq_add] using h

def realGaussianCompensationFactor (M : Matrix Iota Iota Real)
    (hM : M.IsHermitian) (s : Real) : Real :=
  realStandardGaussianNormalizer ^ Fintype.card Iota /
    realGaussianTiltTensorNormalizer (fun j => s * hM.eigenvalues j)

theorem realGaussianCompensationFactor_positive (M : Matrix Iota Iota Real)
    (hM : M.IsHermitian) (s : Real)
    (hDisk : forall j, abs (s * hM.eigenvalues j) < 1) :
    0 < realGaussianCompensationFactor M hM s :=
  div_pos (pow_pos realStandardGaussianNormalizer_positive _)
    (realGaussianTiltTensorNormalizer_positive _ hDisk)

theorem realGaussianCompensationFactor_sq (M : Matrix Iota Iota Real)
    (hM : M.IsHermitian) (s : Real)
    (hDisk : forall j, abs (s * hM.eigenvalues j) < 1) :
    realGaussianCompensationFactor M hM s ^ 2 =
      1 / Matrix.det ((1 : Matrix Iota Iota Real) + HSMul.hSMul s M) := by
  have hNumer : Not (realStandardGaussianNormalizer ^ Fintype.card Iota = 0) :=
    ne_of_gt (pow_pos realStandardGaussianNormalizer_positive _)
  have hDenom : Not (realGaussianTiltTensorNormalizer
      (fun j => s * hM.eigenvalues j) = 0) :=
    ne_of_gt (realGaussianTiltTensorNormalizer_positive _ hDisk)
  have hSq := realGaussianTiltTensorNormalizer_ratio_sq _ hDisk
  rw [hermitian_det_one_add_smul M hM]
  unfold realGaussianCompensationFactor
  calc
    _ = 1 / (realGaussianTiltTensorNormalizer (fun j => s * hM.eigenvalues j) /
        realStandardGaussianNormalizer ^ Fintype.card Iota) ^ 2 := by field_simp
    _ = _ := by rw [hSq]

theorem positive_inverse_half_power_unique (d a : Real)
    (hd : 0 < d) (ha : 0 < a) (hSq : a ^ 2 = 1 / d) :
    a = Real.rpow d (-(1 / 2 : Real)) := by
  have hPos : 0 < Real.rpow d (-(1 / 2 : Real)) := by
    change 0 < d ^ (-(1 / 2 : Real))
    rw [Real.rpow_def_of_pos hd]
    exact Real.exp_pos _
  have hPower : Real.rpow d (-(1 / 2 : Real)) ^ 2 = 1 / d := by
    change (d ^ (-(1 / 2 : Real))) ^ 2 = 1 / d
    rw [Real.rpow_def_of_pos hd, pow_two, <- Real.exp_add]
    have hExp : Real.log d * (-(1 / 2 : Real)) +
        Real.log d * (-(1 / 2 : Real)) = -Real.log d := by ring
    rw [hExp, Real.exp_neg, Real.exp_log hd, one_div]
  have hEqual := (sq_eq_sq_iff_eq_or_eq_neg).mp (hSq.trans hPower.symm)
  rcases hEqual with h | h
  exact h
  exfalso
  linarith

theorem realGaussianCompensationFactor_bipartite (B : Matrix Iota Iota Real)
    (s : Real)
    (hDisk : forall j,
      abs (s * (bipartiteLift_hermitian B).eigenvalues j) < 1) :
    realGaussianCompensationFactor (bipartiteLift B) (bipartiteLift_hermitian B) s =
      realGramDeterminantFactor B s := by
  have hDet : 0 < Matrix.det ((1 : Matrix (Sum Iota Iota) (Sum Iota Iota) Real) +
      HSMul.hSMul s (bipartiteLift B)) := by
    rw [hermitian_det_one_add_smul _ (bipartiteLift_hermitian B)]
    apply Finset.prod_pos
    intro j hj
    have hLower := (abs_lt.mp (hDisk j)).1
    linarith
  have hSq := realGaussianCompensationFactor_sq (bipartiteLift B)
    (bipartiteLift_hermitian B) s hDisk
  rw [det_one_add_bipartiteLift] at hDet hSq
  exact positive_inverse_half_power_unique _ _
    hDet (realGaussianCompensationFactor_positive _ _ s hDisk) hSq

theorem realGaussianCompensatedAverage_state_real (M : Matrix Iota Iota Real)
    (hM : M.IsHermitian) (s : Real)
    (hCol : forall j, Finset.sum Finset.univ (fun i => M i j) = 0)
    (hDisk : forall j, abs (s * hM.eigenvalues j) < 1) :
    gaussianPolynomialState
        (fun j => (s : Complex) * realGaussianEigenVariances M hM j)
        (realGaussianAffinePolynomial M hM 1) =
      (realGaussianCompensationFactor M hM s : Complex) *
        realGaussianCompensatedAverage M hM (s : Complex) := by
  have hCDisk : forall j,
      norm ((s : Complex) * realGaussianEigenVariances M hM j) < 1 := by
    intro j
    change norm ((s : Complex) * (hM.eigenvalues j : Complex)) < 1
    rw [<- Complex.ofReal_mul, Complex.norm_real, Real.norm_eq_abs]
    exact hDisk j
  have hState := realGaussianCompensatedAverage_state M hM (s : Complex) hCol hCDisk
  have hFun : (fun j => (s : Complex) * realGaussianEigenVariances M hM j) =
      (fun j => ((s * hM.eigenvalues j : Real) : Complex)) := by
    funext j
    simp only [realGaussianEigenVariances, Complex.ofReal_mul]
  rw [hFun, realGaussianTiltTensorNormalizer_cast] at hState
  rw [hFun]
  simpa only [realGaussianCompensationFactor, Complex.ofReal_div, Complex.ofReal_pow]
    using hState

theorem realGaussianCompensatedAverage_rook_real {n : Nat}
    (B : Matrix (Fin n) (Fin n) Real) (s : Real)
    (hCol : forall j, Finset.sum Finset.univ (fun i => bipartiteLift B i j) = 0)
    (hDisk : forall j, abs (s * (bipartiteLift_hermitian B).eigenvalues j) < 1) :
    (hamiltonianRookPolynomial B s : Complex) =
      (realGramDeterminantFactor B s : Complex) *
        realGaussianCompensatedAverage (bipartiteLift B)
          (bipartiteLift_hermitian B) (s : Complex) := by
  rw [<- hamiltonianComplexRookPolynomial_ofReal, <- realGaussianAffinePolynomial_scaled_rook]
  rw [realGaussianCompensatedAverage_state_real _ _ s hCol hDisk,
    realGaussianCompensationFactor_bipartite B s hDisk]

theorem stochastic_compensated_eigen_disk (T : Matrix Iota Iota Real)
    (q delta s : Real) (hDelta0 : 0 < delta) (hDelta1 : delta <= 1)
    (hNorm : norm (centeredKernel T q) <= 1 - delta)
    (hWindow : abs (s - 1) <= delta / 4)
    (j : Sum Iota Iota) :
    abs (s * (bipartiteLift_hermitian (centeredKernel T q)).eigenvalues j) < 1 := by
  have hEigen : abs ((bipartiteLift_hermitian (centeredKernel T q)).eigenvalues j) <=
      1 - delta :=
    le_trans (realGaussianEigenvalue_abs_le_norm _ _ j)
      (le_trans (bipartiteLift_l2_norm_le _) hNorm)
  have hS : abs s <= 1 + delta / 4 := by
    apply abs_le.mpr
    have hBounds := abs_le.mp hWindow
    constructor <;> linarith
  rw [abs_mul]
  have hProduct := mul_le_mul hS hEigen (abs_nonneg _) (by linarith : 0 <= 1 + delta / 4)
  have hDeltaSq : 0 <= delta ^ 2 := sq_nonneg delta
  nlinarith

theorem stochastic_compensated_rook_identity {n : Nat}
    (T : Matrix (Fin n) (Fin n) Real) (q delta s : Real)
    (hq : (n : Real) * q = 1)
    (hRow : forall i, Finset.sum Finset.univ (fun j => T i j) = 1)
    (hCol : forall j, Finset.sum Finset.univ (fun i => T i j) = 1)
    (hDelta0 : 0 < delta) (hDelta1 : delta <= 1)
    (hNorm : norm (centeredKernel T q) <= 1 - delta)
    (hWindow : abs (s - 1) <= delta / 4) :
    (hamiltonianRookPolynomial (centeredKernel T q) s : Complex) =
      (realGramDeterminantFactor (centeredKernel T q) s : Complex) *
        realGaussianCompensatedAverage (bipartiteLift (centeredKernel T q))
          (bipartiteLift_hermitian (centeredKernel T q)) (s : Complex) := by
  apply realGaussianCompensatedAverage_rook_real
  exact centered_bipartite_column_sum_zero T q
    (by simpa only [Fintype.card_fin] using hq) hRow hCol
  exact stochastic_compensated_eigen_disk T q delta s hDelta0 hDelta1 hNorm hWindow

end PrimeFactorOscillations

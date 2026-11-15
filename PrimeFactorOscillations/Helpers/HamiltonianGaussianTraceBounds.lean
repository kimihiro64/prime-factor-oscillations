/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import PrimeFactorOscillations.Helpers.HamiltonianCovarianceCorrection
import PrimeFactorOscillations.Helpers.HamiltonianGaussianQuadraticMGF

/-! # Actual stochastic Gaussian tail bounds with Frobenius dependence

Orthogonal energy cancellation precedes the positive exponential-moment
estimate. The signed determinant and low-degree correction are not bounded
by this argument. The final stochastic consumer retains square-root
dimension dependence, instead of a dimension-times-maximum envelope.
-/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations

variable {Iota : Type*} [Fintype Iota] [DecidableEq Iota]

theorem realGaussianEigenvalue_abs_le_norm (M : Matrix Iota Iota Real)
    (hM : M.IsHermitian) (i : Iota) :
    abs (hM.eigenvalues i) <= norm M := by
  letI : Nonempty Iota := Nonempty.intro i
  have hMem := hM.eigenvalues_mem_spectrum_real i
  have h := _root_.spectrum.norm_le_norm_of_mem hMem
  change norm (hM.eigenvalues i) <= norm M at h
  simpa only [Real.norm_eq_abs] using h

theorem realGaussianEigenvalue_square_energy (M : Matrix Iota Iota Real)
    (hM : M.IsHermitian) :
    Finset.sum Finset.univ (fun j => hM.eigenvalues j ^ 2) = matrixSquareEnergy M := by
  let U := realGaussianEigenMatrix M hM
  have hOrth := realGaussianEigenMatrix_orthogonal M hM
  have hColumn : forall k, (fun i => M i k) =
      U.mulVec (fun j => hM.eigenvalues j * U k j) := by
    intro k
    funext i
    have hEntry := congrArg (fun A : Matrix Iota Iota Real => A i k)
      (realGaussianEigenMatrix_decomposition M hM)
    rw [Matrix.mul_apply] at hEntry
    simp only [Matrix.mul_diagonal, Matrix.transpose_apply] at hEntry
    rw [hEntry]
    change Finset.sum Finset.univ (fun j =>
      (U i j * hM.eigenvalues j) * U k j) =
      Finset.sum Finset.univ (fun j => U i j * (hM.eigenvalues j * U k j))
    apply Finset.sum_congr rfl
    intro j hj
    ring
  have hColumnEnergy : forall k, Finset.sum Finset.univ (fun i => M i k ^ 2) =
      Finset.sum Finset.univ (fun j => (hM.eigenvalues j * U k j) ^ 2) := by
    intro k
    have h := realOrthogonal_square_energy U hOrth
      (fun j => hM.eigenvalues j * U k j)
    rw [<- hColumn k] at h
    exact h
  have hColumnUnit : forall j, Finset.sum Finset.univ (fun k => U k j ^ 2) = 1 := by
    intro j
    have h := congrArg (fun A : Matrix Iota Iota Real => A j j) hOrth
    simpa [U, Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, pow_two] using h
  symm
  unfold matrixSquareEnergy
  rw [Finset.sum_comm]
  calc
    _ = Finset.sum Finset.univ (fun k =>
        Finset.sum Finset.univ (fun j => (hM.eigenvalues j * U k j) ^ 2)) := by
      apply Finset.sum_congr rfl
      intro k hk
      exact hColumnEnergy k
    _ = Finset.sum Finset.univ (fun j =>
        Finset.sum Finset.univ (fun k => hM.eigenvalues j ^ 2 * U k j ^ 2)) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j hj
      apply Finset.sum_congr rfl
      intro k hk
      ring
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [<- Finset.mul_sum, hColumnUnit j, mul_one]

theorem realGaussianEigenvalue_nuclear_bound (M : Matrix Iota Iota Real)
    (hM : M.IsHermitian) (E : Real) (hEnergy : matrixSquareEnergy M <= E) :
    Finset.sum Finset.univ (fun j => abs (hM.eigenvalues j)) <=
      Real.sqrt ((Fintype.card Iota : Real) * E) := by
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun _ : Iota => (1 : Real)) (fun j => abs (hM.eigenvalues j))
  simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, mul_one, sq_abs] at hCS
  rw [realGaussianEigenvalue_square_energy] at hCS
  have hSq : (Finset.sum Finset.univ (fun j => abs (hM.eigenvalues j))) ^ 2 <=
      (Fintype.card Iota : Real) * E :=
    le_trans hCS (mul_le_mul_of_nonneg_left hEnergy (Nat.cast_nonneg _))
  have hE0 : 0 <= E := le_trans (matrixSquareEnergy_nonnegative M) hEnergy
  have hRoot := Real.sq_sqrt (mul_nonneg (Nat.cast_nonneg (Fintype.card Iota)) hE0)
  have hSum0 : 0 <= Finset.sum Finset.univ (fun j => abs (hM.eigenvalues j)) :=
    Finset.sum_nonneg (fun j _ => abs_nonneg _)
  nlinarith only [hSq, hRoot, hSum0,
    Real.sqrt_nonneg ((Fintype.card Iota : Real) * E)]

def realSpectralGaussianQuadraticKernel (M : Matrix Iota Iota Real)
    (hM : M.IsHermitian) (tau : Real) (x : Iota -> Real) : Real :=
  Real.exp (tau / 2 * Finset.sum Finset.univ
    (fun i => norm (realGaussianVector M hM x i) ^ 2)) *
      Finset.prod Finset.univ (fun i => Real.exp (-(1 / 2 : Real) * x i ^ 2))

def realSpectralGaussianQuadraticMGF (M : Matrix Iota Iota Real)
    (hM : M.IsHermitian) (tau : Real) : Real :=
  MeasureTheory.integral gaussianTensorMeasure (realSpectralGaussianQuadraticKernel M hM tau) /
    realStandardGaussianNormalizer ^ Fintype.card Iota

theorem realSpectralGaussianQuadraticKernel_eq (M : Matrix Iota Iota Real)
    (hM : M.IsHermitian) (tau : Real) :
    realSpectralGaussianQuadraticKernel M hM tau =
      realGaussianQuadraticKernel (fun j => abs (hM.eigenvalues j)) tau := by
  funext x
  unfold realSpectralGaussianQuadraticKernel realGaussianQuadraticKernel
  rw [realGaussianVector_energy]

theorem realSpectralGaussianQuadraticMGF_bound (M : Matrix Iota Iota Real)
    (hM : M.IsHermitian) (tau rho : Real) (hTau : 0 <= tau)
    (hNorm : norm M <= rho) (hGap : 0 < 1 - tau * rho) :
    realSpectralGaussianQuadraticMGF M hM tau <=
      Real.exp (tau / (1 - tau * rho) *
        Finset.sum Finset.univ (fun j => abs (hM.eigenvalues j))) := by
  unfold realSpectralGaussianQuadraticMGF
  rw [realSpectralGaussianQuadraticKernel_eq]
  exact realGaussianQuadraticMGF_bound _ tau rho hTau (fun j => abs_nonneg _)
    (fun j => le_trans (realGaussianEigenvalue_abs_le_norm M hM j) hNorm) hGap

theorem realSpectralGaussianQuadraticMGF_energy_bound (M : Matrix Iota Iota Real)
    (hM : M.IsHermitian) (tau rho E : Real) (hTau : 0 <= tau)
    (hNorm : norm M <= rho) (hGap : 0 < 1 - tau * rho)
    (hEnergy : matrixSquareEnergy M <= E) :
    realSpectralGaussianQuadraticMGF M hM tau <=
      Real.exp (tau / (1 - tau * rho) *
        Real.sqrt ((Fintype.card Iota : Real) * E)) := by
  apply le_trans (realSpectralGaussianQuadraticMGF_bound M hM tau rho hTau hNorm hGap)
  apply Real.exp_le_exp.mpr
  exact mul_le_mul_of_nonneg_left (realGaussianEigenvalue_nuclear_bound M hM E hEnergy)
    (div_nonneg hTau hGap.le)

theorem stochasticGaussianQuadraticMGF_bound (T : Matrix Iota Iota Real) (q a tau rho : Real)
    (hq : (Fintype.card Iota : Real) * q = 1) (ha : 1 <= a)
    (hRow : forall i, Finset.sum Finset.univ (fun j => T i j) = 1)
    (hNonneg : forall i j, 0 <= T i j) (hUpper : forall i j, T i j <= a * q)
    (hTau : 0 <= tau) (hNorm : norm (centeredKernel T q) <= rho)
    (hGap : 0 < 1 - tau * rho) :
    realSpectralGaussianQuadraticMGF (bipartiteLift (centeredKernel T q))
        (bipartiteLift_hermitian (centeredKernel T q)) tau <=
      Real.exp (2 * tau / (1 - tau * rho) *
        Real.sqrt ((Fintype.card Iota : Real) * (a - 1))) := by
  let B := centeredKernel T q
  let M := bipartiteLift B
  let hM := bipartiteLift_hermitian B
  have hBlockEnergy : matrixSquareEnergy M = 2 * matrixSquareEnergy B := by
    unfold matrixSquareEnergy
    simp only [Fintype.sum_sum_type]
    have hTransposeEnergy :
        Finset.sum Finset.univ (fun i => Finset.sum Finset.univ (fun j => B j i ^ 2)) =
          Finset.sum Finset.univ (fun i => Finset.sum Finset.univ (fun j => B i j ^ 2)) :=
      Finset.sum_comm
    simp [M, bipartiteLift, Matrix.fromBlocks, Matrix.transpose_apply]
    linarith only [hTransposeEnergy]
  have hEnergy : matrixSquareEnergy M <= 2 * (a - 1) := by
    rw [hBlockEnergy]
    exact mul_le_mul_of_nonneg_left
      (stochastic_total_energy T q a hq hRow hNonneg hUpper) (by norm_num)
  have hNormM : norm M <= rho := le_trans (bipartiteLift_l2_norm_le B) hNorm
  have h := realSpectralGaussianQuadraticMGF_energy_bound M hM tau rho (2 * (a - 1))
    hTau hNormM hGap hEnergy
  have hSize : (Fintype.card (Sum Iota Iota) : Real) = 2 * (Fintype.card Iota : Real) := by
    simp only [Fintype.card_sum, Nat.cast_add]
    ring
  have hK0 : 0 <= (Fintype.card Iota : Real) * (a - 1) :=
    mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.mpr ha)
  have hRoot : Real.sqrt ((2 * (Fintype.card Iota : Real)) * (2 * (a - 1))) =
      2 * Real.sqrt ((Fintype.card Iota : Real) * (a - 1)) := by
    have hLeftNonneg : 0 <=
        (2 * (Fintype.card Iota : Real)) * (2 * (a - 1)) :=
      mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg (Fintype.card Iota)))
        (mul_nonneg (by norm_num) (sub_nonneg.mpr ha))
    have hLeft := Real.sq_sqrt hLeftNonneg
    have hRight := Real.sq_sqrt hK0
    nlinarith only [hLeft, hRight,
      Real.sqrt_nonneg ((2 * (Fintype.card Iota : Real)) * (2 * (a - 1))),
      Real.sqrt_nonneg ((Fintype.card Iota : Real) * (a - 1))]
  rw [hSize, hRoot] at h
  convert! h using 1 <;> congr 1 <;> ring

end PrimeFactorOscillations

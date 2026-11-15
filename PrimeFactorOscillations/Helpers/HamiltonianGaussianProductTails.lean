/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Tactic.FunProp
import PrimeFactorOscillations.Helpers.HamiltonianCollectiveGaussian
import PrimeFactorOscillations.Helpers.HamiltonianGaussianTraceBounds

/-! # Collective Gaussian affine-product bounds for the analytic tails

The actual stochastic block supplies the zero-sum condition. Every overlap
is retained until the exact orthogonal energy identity has been used.
The resulting absolute product estimate is only a Cauchy/tail input; it
does not replace the signed low-degree determinant or covariance terms.
-/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations

variable {Iota : Type*} [Fintype Iota] [DecidableEq Iota]

def realGaussianAffineProductKernel (M : Matrix Iota Iota Real)
    (hM : M.IsHermitian) (c : Complex) (x : Iota -> Real) : Real :=
  Finset.prod Finset.univ (fun i => norm (1 + c * realGaussianVector M hM x i)) *
    Finset.prod Finset.univ (fun i => Real.exp (-(1 / 2 : Real) * x i ^ 2))

def realGaussianAffineProductAverage (M : Matrix Iota Iota Real)
    (hM : M.IsHermitian) (c : Complex) : Real :=
  MeasureTheory.integral gaussianTensorMeasure (realGaussianAffineProductKernel M hM c) /
    realStandardGaussianNormalizer ^ Fintype.card Iota

theorem realGaussianAffineProductKernel_nonnegative (M : Matrix Iota Iota Real)
    (hM : M.IsHermitian) (c : Complex) (x : Iota -> Real) :
    0 <= realGaussianAffineProductKernel M hM c x :=
  mul_nonneg (Finset.prod_nonneg (fun i _ => norm_nonneg _))
    (Finset.prod_nonneg (fun i _ => (Real.exp_pos _).le))

theorem realGaussianAffineProductKernel_continuous (M : Matrix Iota Iota Real)
    (hM : M.IsHermitian) (c : Complex) :
    Continuous (realGaussianAffineProductKernel M hM c) := by
  unfold realGaussianAffineProductKernel realGaussianVector
  fun_prop

theorem realSpectralGaussianQuadraticKernel_integrable (M : Matrix Iota Iota Real)
    (hM : M.IsHermitian) (tau rho : Real) (hTau : 0 <= tau)
    (hNorm : norm M <= rho) (hGap : 0 < 1 - tau * rho) :
    MeasureTheory.Integrable (realSpectralGaussianQuadraticKernel M hM tau)
      gaussianTensorMeasure := by
  rw [realSpectralGaussianQuadraticKernel_eq]
  apply realGaussianQuadraticKernel_integrable
  intro j
  exact lt_of_lt_of_le hGap (sub_le_sub_left
    (mul_le_mul_of_nonneg_left
      (le_trans (realGaussianEigenvalue_abs_le_norm M hM j) hNorm) hTau) 1)

theorem realGaussianAffineProductKernel_le_envelope [Nonempty Iota]
    (M : Matrix Iota Iota Real) (hM : M.IsHermitian) (c : Complex)
    (hCol : forall j, Finset.sum Finset.univ (fun i => M i j) = 0)
    (x : Iota -> Real) :
    realGaussianAffineProductKernel M hM c x <=
      realSpectralGaussianQuadraticKernel M hM (norm c ^ 2) x := by
  have hZero := realGaussianVector_zero_sum M hM hCol x
  have hProd := collective_zero_sum_exponential_bound (realGaussianVector M hM x) c hZero
  have hExponent : norm c ^ 2 * collectiveSquareMass (realGaussianVector M hM x) / 2 =
      norm c ^ 2 / 2 * Finset.sum Finset.univ
        (fun i => norm (realGaussianVector M hM x i) ^ 2) := by
    unfold collectiveSquareMass
    ring
  rw [hExponent] at hProd
  exact mul_le_mul_of_nonneg_right hProd
    (Finset.prod_nonneg (fun i _ => (Real.exp_pos _).le))

theorem realGaussianAffineProductKernel_integrable [Nonempty Iota]
    (M : Matrix Iota Iota Real) (hM : M.IsHermitian) (c : Complex) (rho : Real)
    (hCol : forall j, Finset.sum Finset.univ (fun i => M i j) = 0)
    (hNorm : norm M <= rho) (hGap : 0 < 1 - norm c ^ 2 * rho) :
    MeasureTheory.Integrable (realGaussianAffineProductKernel M hM c)
      gaussianTensorMeasure := by
  have hEnvelope := realSpectralGaussianQuadraticKernel_integrable M hM
    (norm c ^ 2) rho (sq_nonneg _) hNorm hGap
  apply hEnvelope.mono' (realGaussianAffineProductKernel_continuous M hM c).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro x
  rw [Real.norm_eq_abs, abs_of_nonneg (realGaussianAffineProductKernel_nonnegative M hM c x)]
  exact realGaussianAffineProductKernel_le_envelope M hM c hCol x

theorem realGaussianAffineProductAverage_le_MGF [Nonempty Iota]
    (M : Matrix Iota Iota Real) (hM : M.IsHermitian) (c : Complex) (rho : Real)
    (hCol : forall j, Finset.sum Finset.univ (fun i => M i j) = 0)
    (hNorm : norm M <= rho) (hGap : 0 < 1 - norm c ^ 2 * rho) :
    realGaussianAffineProductAverage M hM c <=
      realSpectralGaussianQuadraticMGF M hM (norm c ^ 2) := by
  have hProduct := realGaussianAffineProductKernel_integrable M hM c rho hCol hNorm hGap
  have hEnvelope := realSpectralGaussianQuadraticKernel_integrable M hM
    (norm c ^ 2) rho (sq_nonneg _) hNorm hGap
  have hIntegral := MeasureTheory.integral_mono hProduct hEnvelope
    (realGaussianAffineProductKernel_le_envelope M hM c hCol)
  have hDen : 0 < realStandardGaussianNormalizer ^ Fintype.card Iota :=
    pow_pos realStandardGaussianNormalizer_positive _
  unfold realGaussianAffineProductAverage realSpectralGaussianQuadraticMGF
  calc
    _ = MeasureTheory.integral gaussianTensorMeasure (realGaussianAffineProductKernel M hM c) *
        (1 / realStandardGaussianNormalizer ^ Fintype.card Iota) := by ring
    _ <= MeasureTheory.integral gaussianTensorMeasure
        (realSpectralGaussianQuadraticKernel M hM (norm c ^ 2)) *
          (1 / realStandardGaussianNormalizer ^ Fintype.card Iota) :=
      mul_le_mul_of_nonneg_right hIntegral (one_div_pos.mpr hDen).le
    _ = _ := by ring

theorem stochasticGaussianAffineProductAverage_bound
    (T : Matrix Iota Iota Real) (q a rho : Real) (c : Complex)
    (hq : (Fintype.card Iota : Real) * q = 1) (ha : 1 <= a)
    (hRow : forall i, Finset.sum Finset.univ (fun j => T i j) = 1)
    (hCol : forall j, Finset.sum Finset.univ (fun i => T i j) = 1)
    (hNonneg : forall i j, 0 <= T i j) (hUpper : forall i j, T i j <= a * q)
    (hNorm : norm (centeredKernel T q) <= rho) (hGap : 0 < 1 - norm c ^ 2 * rho) :
    realGaussianAffineProductAverage (bipartiteLift (centeredKernel T q))
        (bipartiteLift_hermitian (centeredKernel T q)) c <=
      Real.exp (2 * norm c ^ 2 / (1 - norm c ^ 2 * rho) *
        Real.sqrt ((Fintype.card Iota : Real) * (a - 1))) := by
  have hCard : Not (Fintype.card Iota = 0) := by
    intro hZero
    norm_num [hZero] at hq
  letI : Nonempty Iota := Fintype.card_pos_iff.mp (Nat.pos_of_ne_zero hCard)
  have hNormM : norm (bipartiteLift (centeredKernel T q)) <= rho :=
    le_trans (bipartiteLift_l2_norm_le _) hNorm
  apply le_trans (realGaussianAffineProductAverage_le_MGF _ _ c rho
    (centered_bipartite_column_sum_zero T q hq hRow hCol) hNormM hGap)
  exact stochasticGaussianQuadraticMGF_bound T q a (norm c ^ 2) rho hq ha hRow
    hNonneg hUpper (sq_nonneg _) hNorm hGap

theorem stochasticGaussianAffineProductAverage_parameter_bound
    (T : Matrix Iota Iota Real) (q a rho : Real) (t : Complex)
    (hq : (Fintype.card Iota : Real) * q = 1) (ha : 1 <= a)
    (hRow : forall i, Finset.sum Finset.univ (fun j => T i j) = 1)
    (hCol : forall j, Finset.sum Finset.univ (fun i => T i j) = 1)
    (hNonneg : forall i j, 0 <= T i j) (hUpper : forall i j, T i j <= a * q)
    (hNorm : norm (centeredKernel T q) <= rho) (hGap : 0 < 1 - norm t * rho) :
    realGaussianAffineProductAverage (bipartiteLift (centeredKernel T q))
        (bipartiteLift_hermitian (centeredKernel T q)) (complexGaussianSquareRoot t) <=
      Real.exp (2 * norm t / (1 - norm t * rho) *
        Real.sqrt ((Fintype.card Iota : Real) * (a - 1))) := by
  have hRoot : norm (complexGaussianSquareRoot t) ^ 2 = norm t := by
    rw [<- norm_pow, complexGaussianSquareRoot_sq]
  have h := stochasticGaussianAffineProductAverage_bound T q a rho
    (complexGaussianSquareRoot t) hq ha hRow hCol hNonneg hUpper hNorm
      (by simpa only [hRoot] using hGap)
  simpa only [hRoot] using h

end PrimeFactorOscillations

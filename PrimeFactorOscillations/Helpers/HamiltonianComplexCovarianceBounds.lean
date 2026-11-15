/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianAnalyticCoefficientScale
import PrimeFactorOscillations.Helpers.HamiltonianLocalPermanentRemainder

/-! # Actual complex covariance bounds from the full resolvent coefficients

The actual analytic covariance is identified with its convergent Taylor
series before the coefficient majorant is consumed. The entry bound is
uniform on a complex circle and retains the whole matrix resolvent.
-/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations

variable {Iota : Type*} [Fintype Iota] [DecidableEq Iota]

def realGaussianQuotientCovarianceFunction (M : Matrix Iota Iota Real)
    (hM : M.IsHermitian) (i j : Iota) (s : Complex) : Complex :=
  gaussianLinearCovariance
    (fun k => s * realGaussianEigenVariances M hM k /
      (1 + s * realGaussianEigenVariances M hM k))
    (realGaussianEigenRows M hM i) (realGaussianEigenRows M hM j)

theorem realGaussianQuotientCovarianceFunction_analyticAt
    (M : Matrix Iota Iota Real) (hM : M.IsHermitian) (rho : Real)
    (hNorm : norm M <= rho) (s : Complex) (hs : norm s * rho < 1) (i j : Iota) :
    AnalyticAt Complex (realGaussianQuotientCovarianceFunction M hM i j) s := by
  unfold realGaussianQuotientCovarianceFunction
  apply gaussianLinearCovariance_analyticAt
  intro k
  have hEigen : norm (realGaussianEigenVariances M hM k) <= rho := by
    simpa only [realGaussianEigenVariances, Complex.norm_real, Real.norm_eq_abs] using
      le_trans (realGaussianEigenvalue_abs_le_norm M hM k) hNorm
  have hSmall : norm (s * realGaussianEigenVariances M hM k) < 1 := by
    rw [norm_mul]
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left hEigen (norm_nonneg s)) hs
  have hUnit : IsUnit (1 - -(s * realGaussianEigenVariances M hM k)) :=
    isUnit_one_sub_of_norm_lt_one (by simpa only [norm_neg] using hSmall)
  have hNe : Not (1 + s * realGaussianEigenVariances M hM k = 0) := by
    simpa only [sub_neg_eq_add] using hUnit.ne_zero
  exact (analyticAt_id.mul analyticAt_const).div
    (analyticAt_const.add (analyticAt_id.mul analyticAt_const)) hNe

theorem covarianceFormalSeries_real_smul_coeff_norm
    (M : Matrix Iota Iota Real) (b : Real) (hb : 0 <= b) (k : Nat) (i j : Iota) :
    norm (PowerSeries.coeff k (covarianceFormalSeries (HSMul.hSMul b M) i j)) =
      b ^ k * norm (PowerSeries.coeff k (covarianceFormalSeries M i j)) := by
  cases k with
  | zero =>
    rw [covarianceFormalSeries_coeff_zero, covarianceFormalSeries_coeff_zero]
    simp only [norm_zero, mul_zero]
  | succ k =>
    rw [covarianceFormalSeries_coeff_succ, covarianceFormalSeries_coeff_succ,
      covarianceSeriesCoefficient_real_smul]
    simp only [Matrix.smul_apply, smul_eq_mul, Complex.norm_real, norm_mul,
      Real.norm_eq_abs, abs_pow, abs_of_nonneg hb]

variable [Nonempty Iota]

theorem realGaussianQuotientCovarianceFunction_hasSum
    (M : Matrix Iota Iota Real) (hM : M.IsHermitian) (rho : Real)
    (R : NNReal) (hNorm : norm M <= rho) (hR : 0 < R)
    (hGap : (R : Real) * rho < 1) (s : Complex)
    (hs : Membership.mem (Metric.eball (0 : Complex) (R : ENNReal)) s) (i j : Iota) :
    HasSum (fun k => s ^ k * PowerSeries.coeff k (covarianceFormalSeries M i j))
      (realGaussianQuotientCovarianceFunction M hM i j s) := by
  let f := realGaussianQuotientCovarianceFunction M hM i j
  have hRho : 0 <= rho := le_trans (norm_nonneg M) hNorm
  have hSeries : HasFPowerSeriesOnBall f (cauchyPowerSeries f 0 R) 0 R := by
    apply DifferentiableOn.hasFPowerSeriesOnBall _ hR
    intro z hz
    have hSize : norm z <= (R : Real) := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hz
    have hDisk : norm z * rho < 1 :=
      lt_of_le_of_lt (mul_le_mul_of_nonneg_right hSize hRho) hGap
    exact (realGaussianQuotientCovarianceFunction_analyticAt M hM rho hNorm
      z hDisk i j).differentiableAt.differentiableWithinAt
  have hCoeff : forall k, PowerSeries.coeff k (wickTaylorSeries f) =
      PowerSeries.coeff k (covarianceFormalSeries M i j) := by
    intro k
    exact congrArg (fun A : Matrix Iota Iota (PowerSeries Complex) =>
      PowerSeries.coeff k (A i j)) (realGaussianCovarianceTaylorSeries_eq M hM)
  have h := wickTaylorSeries_hasSum f (cauchyPowerSeries f 0 R) R hSeries s hs
  simp_rw [hCoeff] at h
  exact h

theorem realGaussianQuotientCovarianceFunction_norm_bound
    (M : Matrix Iota Iota Real) (hM : M.IsHermitian) (rho b C : Real)
    (R : NNReal) (hNorm : norm M <= rho) (hR : 0 < R)
    (hGap : (R : Real) * rho < 1) (hb : 0 <= b) (hbR : b < (R : Real))
    (s : Complex) (hs : norm s <= b) (i j : Iota)
    (hMass : forall H, finitePowerSeriesMass H
      (covarianceFormalSeries (HSMul.hSMul b M) i j) <= C) :
    norm (realGaussianQuotientCovarianceFunction M hM i j s) <= C := by
  have hsR : Membership.mem (Metric.eball (0 : Complex) (R : ENNReal)) s := by
    rw [mem_eball_zero_iff, enorm_lt_coe]
    exact_mod_cast lt_of_le_of_lt hs hbR
  have hSum := realGaussianQuotientCovarianceFunction_hasSum M hM rho R
    hNorm hR hGap s hsR i j
  have hCoeff : forall k,
      norm (s ^ k * PowerSeries.coeff k (covarianceFormalSeries M i j)) <=
        norm (PowerSeries.coeff k (covarianceFormalSeries (HSMul.hSMul b M) i j)) := by
    intro k
    rw [norm_mul, norm_pow, covarianceFormalSeries_real_smul_coeff_norm M b hb]
    exact mul_le_mul_of_nonneg_right
      (wick_nonnegative_power_le (norm s) b (norm_nonneg s) hs k) (norm_nonneg _)
  have hPartial : forall H : Nat,
      norm (Finset.sum (Finset.range H) (fun k =>
        s ^ k * PowerSeries.coeff k (covarianceFormalSeries M i j))) <= C := by
    intro H
    calc
      _ <= Finset.sum (Finset.range H) (fun k =>
        norm (s ^ k * PowerSeries.coeff k (covarianceFormalSeries M i j))) := norm_sum_le _ _
      _ <= Finset.sum (Finset.range H) (fun k =>
        norm (PowerSeries.coeff k
          (covarianceFormalSeries (HSMul.hSMul b M) i j))) :=
            Finset.sum_le_sum (fun k hk => hCoeff k)
      _ <= finitePowerSeriesMass H
          (covarianceFormalSeries (HSMul.hSMul b M) i j) := by
        unfold finitePowerSeriesMass
        exact Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.range_mono (Nat.le_succ H)) (fun k hk hNot => norm_nonneg _)
      _ <= _ := hMass H
  exact le_of_tendsto hSum.tendsto_sum_nat.norm (Filter.Eventually.of_forall hPartial)

theorem stochastic_complex_covariance_entry_bound {n : Nat}
    (T : Matrix (Fin n) (Fin n) Real) (q a delta b : Real) (R : NNReal)
    (hn : 0 < n) (hq : (n : Real) * q = 1) (ha : 1 <= a)
    (hRow : forall i, Finset.sum Finset.univ (fun j => T i j) = 1)
    (hCol : forall j, Finset.sum Finset.univ (fun i => T i j) = 1)
    (hNonneg : forall i j, 0 <= T i j) (hUpper : forall i j, T i j <= a * q)
    (hDelta0 : 0 < delta) (hDelta1 : delta <= 1)
    (hNorm : norm (centeredKernel T q) <= 1 - delta)
    (hb : 1 <= b) (hbR : b < (R : Real))
    (hGap : (R : Real) * (1 - delta) < 1) (hTheta : b * (1 - delta / 2) < 1)
    (s : Complex) (hs : norm s <= b) (i j : Sum (Fin n) (Fin n)) :
    norm (realGaussianQuotientCovarianceFunction
      (bipartiteLift (centeredKernel T q)) (bipartiteLift_hermitian (centeredKernel T q))
        i j s) <= 2 * b ^ 2 * a * q / (1 - b * (1 - delta / 2)) := by
  have : Nonempty (Fin n) := Nonempty.intro (Fin.mk 0 hn)
  have hMNorm : norm (bipartiteLift (centeredKernel T q)) <= 1 - delta :=
    le_trans (bipartiteLift_l2_norm_le _) hNorm
  have hR : 0 < R := by
    exact_mod_cast lt_trans (lt_of_lt_of_le (by norm_num : (0 : Real) < 1) hb) hbR
  apply realGaussianQuotientCovarianceFunction_norm_bound _ _ (1 - delta) b _ R
    hMNorm hR hGap (le_trans (by norm_num) hb) hbR s hs i j
  intro H
  exact stochastic_covarianceFormalSeries_mass_bound T q a delta b b H
    (by simpa only [Fintype.card_fin] using hq) ha hRow hCol hNonneg hUpper
    hDelta0 hDelta1 hNorm hb (le_of_eq (abs_of_nonneg (le_trans (by norm_num) hb)))
    hTheta i j

end PrimeFactorOscillations

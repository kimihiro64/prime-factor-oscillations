/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianLowWickAnalytic
import PrimeFactorOscillations.Helpers.HamiltonianWickSeriesRescale

/-! # The actual full low-correction tail throughout the physical window

Every circle and analyticity hypothesis is discharged from the actual
stochastic kernel. The auxiliary covariance radius is explicit.
-/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations

theorem stochastic_lowWick_window_tail {n : Nat}
    (T : Matrix (Fin n) (Fin n) Real) (q a delta b s : Real)
    (R : NNReal) (H : Nat)
    (hn : 3 <= n) (hq : (n : Real) * q = 1) (ha : 1 <= a)
    (hRow : forall i, Finset.sum Finset.univ (fun j => T i j) = 1)
    (hCol : forall j, Finset.sum Finset.univ (fun i => T i j) = 1)
    (hNonneg : forall i j, 0 <= T i j) (hUpper : forall i j, T i j <= a * q)
    (hDelta0 : 0 < delta) (hDelta1 : delta <= 1)
    (hNorm : norm (centeredKernel T q) <= 1 - delta)
    (hb : 1 <= b) (hs : abs s <= b) (hR : 1 < (R : Real))
    (hTheta : b * (R : Real) * (1 - delta / 2) < 1) :
    norm (gaussianWickLowValue
      (fun j => (s : Complex) *
          realGaussianEigenVariances (bipartiteLift (centeredKernel T q))
            (bipartiteLift_hermitian (centeredKernel T q)) j /
        (1 + (s : Complex) *
          realGaussianEigenVariances (bipartiteLift (centeredKernel T q))
            (bipartiteLift_hermitian (centeredKernel T q)) j))
      (realGaussianEigenRows (bipartiteLift (centeredKernel T q))
        (bipartiteLift_hermitian (centeredKernel T q))) -
      hamiltonianFiniteSeriesValue H (wickSeriesLowDiagrams
        (covarianceFormalSeries (HSMul.hSMul s (bipartiteLift (centeredKernel T q)))))) <=
      10 * (1 + 16 * Real.exp 1 *
        (2 * (b * (R : Real)) ^ 2 * a /
          (1 - b * (R : Real) * (1 - delta / 2)))) ^ 3 *
        (Inv.inv (R : Real)) ^ (H + 1) / (1 - (Inv.inv (R : Real))) := by
  have hnPos : 0 < n := by omega
  have : Nonempty (Fin n) := Nonempty.intro (Fin.mk 0 hnPos)
  let M := bipartiteLift (centeredKernel T q)
  let hM := bipartiteLift_hermitian (centeredKernel T q)
  let row := realGaussianEigenRows M hM
  let z := fun w : Complex => fun j =>
    ((s : Complex) * w) * realGaussianEigenVariances M hM j /
      (1 + ((s : Complex) * w) * realGaussianEigenVariances M hM j)
  let g : Real := 1 - delta / 2
  have hg : 0 < g := by dsimp only [g]; linarith
  let S : NNReal := Subtype.mk (1 / g) (by positivity)
  have hSPos : 0 < (S : Real) := by
    change 0 < (1 / g : Real)
    exact one_div_pos.mpr hg
  have hSMul : (S : Real) * g = 1 := by
    change (1 / g) * g = 1
    field_simp [ne_of_gt hg]
  have hR0 : 0 < (R : Real) := lt_trans (by norm_num) hR
  have hBig : 1 <= b * (R : Real) := by
    have h := mul_le_mul hb hR.le (by norm_num : (0 : Real) <= 1)
      (le_trans (by norm_num) hb)
    simpa only [one_mul] using h
  have hBig0 : 0 <= b * (R : Real) := le_trans (by norm_num) hBig
  have hBigS : b * (R : Real) < (S : Real) := by
    by_contra hNot
    have hLe : (S : Real) <= b * (R : Real) := le_of_not_gt hNot
    have h := mul_le_mul_of_nonneg_right hLe hg.le
    rw [hSMul] at h
    exact not_lt_of_ge h hTheta
  have hSGap : (S : Real) * (1 - delta) < 1 := by
    have hStrict : 1 - delta < g := by dsimp only [g]; linarith
    have h := mul_lt_mul_of_pos_left hStrict hSPos
    rw [hSMul] at h
    exact h
  have hMNorm : norm M <= 1 - delta := le_trans (bipartiteLift_l2_norm_le _) hNorm
  have hRho : 0 <= 1 - delta := sub_nonneg.mpr hDelta1
  have hBigGap : b * (R : Real) * (1 - delta) < 1 := by
    exact lt_of_le_of_lt
      (mul_le_mul_of_nonneg_left
        (show 1 - delta <= 1 - delta / 2 by linarith) hBig0) hTheta
  let kappa : Real := 2 * (b * (R : Real)) ^ 2 * a /
    (1 - b * (R : Real) * (1 - delta / 2))
  have hKappa : 0 <= kappa := by
    dsimp only [kappa]
    exact div_nonneg (by positivity) (sub_pos.mpr hTheta).le
  have hn0 : Not ((n : Real) = 0) := ne_of_gt (Nat.cast_pos.mpr hnPos)
  have hqEq : q = 1 / (n : Real) := by
    apply (eq_div_iff hn0).mpr
    simpa only [mul_comm] using hq
  have hCard : Fintype.card (Sum (Fin n) (Fin n)) = 2 * n := by
    simp only [Fintype.card_sum, Fintype.card_fin]
    omega
  have hZ : forall w, Membership.mem (Metric.closedBall (0 : Complex) (R : Real)) w ->
      forall j, AnalyticAt Complex (fun t => z t j) w := by
    intro w hw j
    have hSize : norm w <= (R : Real) := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hw
    have hC : norm ((s : Complex) * w) <= b * (R : Real) := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul hs hSize (norm_nonneg w) (le_trans (by norm_num) hb)
    have hEigen : norm (realGaussianEigenVariances M hM j) <= 1 - delta := by
      simpa only [realGaussianEigenVariances, Complex.norm_real, Real.norm_eq_abs] using
        le_trans (realGaussianEigenvalue_abs_le_norm M hM j) hMNorm
    have hSmall : norm (((s : Complex) * w) * realGaussianEigenVariances M hM j) < 1 := by
      rw [norm_mul]
      exact lt_of_le_of_lt
        (mul_le_mul hC hEigen (norm_nonneg _) hBig0) hBigGap
    have hUnit : IsUnit (1 - -(((s : Complex) * w) * realGaussianEigenVariances M hM j)) :=
      isUnit_one_sub_of_norm_lt_one (by simpa only [norm_neg] using hSmall)
    have hNe : Not (1 + ((s : Complex) * w) * realGaussianEigenVariances M hM j = 0) := by
      simpa only [sub_neg_eq_add] using hUnit.ne_zero
    exact ((analyticAt_const.mul analyticAt_id).mul analyticAt_const).div
      (analyticAt_const.add ((analyticAt_const.mul analyticAt_id).mul analyticAt_const)) hNe
  have hCov : forall w, Membership.mem (Metric.sphere (0 : Complex) (R : Real)) w ->
      forall i j, norm (gaussianLinearCovariance (z w) (row i) (row j)) <=
        kappa / (n : Real) := by
    intro w hw i j
    have hSize : norm w = (R : Real) := by
      simpa only [Metric.mem_sphere, dist_zero_right] using hw
    have hC : norm ((s : Complex) * w) <= b * (R : Real) := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, hSize]
      exact mul_le_mul_of_nonneg_right hs R.property
    have h := stochastic_complex_covariance_entry_bound T q a delta
      (b * (R : Real)) S hnPos hq ha hRow hCol hNonneg hUpper hDelta0 hDelta1
      hNorm hBig hBigS hSGap hTheta ((s : Complex) * w) hC i j
    calc
      _ <= _ := h
      _ = _ := by rw [hqEq]; dsimp only [kappa]; ring
  have hG : gaussianCovarianceTaylorSeries z row =
      covarianceFormalSeries (HSMul.hSMul s M) := by
    rw [covarianceFormalSeries_real_smul, <- realGaussianCovarianceTaylorSeries_eq M hM]
    funext i j
    change wickTaylorSeries
        (fun w => realGaussianQuotientCovarianceFunction M hM i j ((s : Complex) * w)) =
      PowerSeries.rescale (s : Complex)
        (wickTaylorSeries (realGaussianQuotientCovarianceFunction M hM i j))
    exact wickTaylorSeries_comp_mul _
      (realGaussianQuotientCovarianceFunction_analyticAt M hM (1 - delta) hMNorm
        0 (by simp) i j) (s : Complex)
  have h := gaussianWickLowValue_cauchy_remainder z row n H kappa R
    hCard hn hKappa hR hZ hCov
  rw [hG] at h
  simpa only [z, row, M, hM, kappa, mul_one] using h

end PrimeFactorOscillations

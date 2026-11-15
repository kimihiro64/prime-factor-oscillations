/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianWickAnalyticSeries

/-! # The actual covariance Taylor series is the full signed resolvent series

The finite geometric remainder retains Q*(-Q)^k in full. Its explicit
Neumann bound is used only to identify Taylor coefficients on a positive
real ray. This is an exact series adapter, not an estimate replacing the
signed Wick main terms.
-/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations

variable {Iota : Type*} [Fintype Iota] [DecidableEq Iota]

theorem resolventCovariance_finite_remainder
    (Q : Matrix Iota Iota Real) (H : Nat)
    (hUnit : IsUnit (1 + Q)) :
    resolventCovariance Q - Finset.sum (Finset.range H) (covarianceSeriesCoefficient Q) =
      Q * (-Q) ^ H * Ring.inverse (1 + Q) := by
  let S := Finset.sum (Finset.range H) (fun k => (-Q) ^ k)
  let A := Ring.inverse (1 + Q)
  have hGeom : S * (1 + Q) = 1 - (-Q) ^ H := by
    simpa only [S, sub_neg_eq_add] using geom_sum_mul_neg (-Q) H
  have hRight : (1 + Q) * A = 1 := Ring.mul_inverse_cancel _ hUnit
  have hS : S = (1 - (-Q) ^ H) * A := by
    calc
      _ = S * ((1 + Q) * A) := by rw [hRight, mul_one]
      _ = (S * (1 + Q)) * A := (mul_assoc _ _ _).symm
      _ = _ := by rw [hGeom]
  have hDifference : A - S = (-Q) ^ H * A := by
    rw [hS, sub_mul, one_mul, sub_sub_cancel]
  change Q * A - Finset.sum (Finset.range H) (fun k => Q * (-Q) ^ k) =
    Q * (-Q) ^ H * A
  rw [<- Finset.mul_sum]
  change Q * A - Q * S = Q * (-Q) ^ H * A
  rw [<- mul_sub, hDifference, mul_assoc]

theorem l2_matrix_entry_le_norm (M : Matrix Iota Iota Real) (i j : Iota) :
    norm (M i j) <= norm M := by
  let u : EuclideanSpace Real Iota := WithLp.toLp 2
    (fun k => (1 : Matrix Iota Iota Real) i k)
  let v : EuclideanSpace Real Iota := WithLp.toLp 2
    (fun k => (1 : Matrix Iota Iota Real) k j)
  have hUSquare : norm u ^ 2 = 1 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    change Finset.sum Finset.univ (fun k => ((1 : Matrix Iota Iota Real) i k) ^ 2) = 1
    simp [Matrix.one_apply]
  have hVSquare : norm v ^ 2 = 1 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    change Finset.sum Finset.univ (fun k => ((1 : Matrix Iota Iota Real) k j) ^ 2) = 1
    simp [Matrix.one_apply]
  have hU : norm u = 1 := by nlinarith [norm_nonneg u]
  have hV : norm v = 1 := by nlinarith [norm_nonneg v]
  have h := l2_sandwich_entry_bound (1 : Matrix Iota Iota Real) M 1 i j
  change norm (((1 : Matrix Iota Iota Real) * M *
    (1 : Matrix Iota Iota Real)) i j) <= norm u * norm M * norm v at h
  simpa only [one_mul, mul_one, hU, hV] using h

variable [Nonempty Iota]

theorem resolventCovariance_finite_remainder_bound
    (Q : Matrix Iota Iota Real) (H : Nat) (hNorm : norm Q <= 1 / 2) :
    norm (resolventCovariance Q -
      Finset.sum (Finset.range H) (covarianceSeriesCoefficient Q)) <=
        2 * norm Q ^ (H + 1) := by
  have hNeg : norm (-Q) <= 1 / 2 := by simpa only [norm_neg] using hNorm
  have hSmall : norm (-Q) < 1 := by linarith only [hNeg]
  have hUnit : IsUnit (1 + Q) := by
    simpa only [sub_neg_eq_add] using isUnit_one_sub_of_norm_lt_one hSmall
  have hCertificate := l2_neumann_certificate (-Q) (1 / 2) hNeg (by norm_num)
  have hInv : norm (Ring.inverse (1 + Q)) <= 2 := by
    simp only [sub_neg_eq_add] at hCertificate
    nlinarith only [hCertificate]
  rw [resolventCovariance_finite_remainder Q H hUnit]
  calc
    _ <= norm (Q * (-Q) ^ H) * norm (Ring.inverse (1 + Q)) := norm_mul_le _ _
    _ <= (norm Q * norm ((-Q) ^ H)) * 2 :=
      mul_le_mul (norm_mul_le _ _) hInv (norm_nonneg _)
        (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _ <= (norm Q * norm (-Q) ^ H) * 2 :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (norm_pow_le (-Q) H) (norm_nonneg Q)) (by norm_num)
    _ = _ := by rw [norm_neg, pow_succ]; ring

omit [Nonempty Iota] in
theorem covarianceSeriesCoefficient_real_smul
    (M : Matrix Iota Iota Real) (t : Real) (k : Nat) :
    covarianceSeriesCoefficient (HSMul.hSMul t M) k =
      HSMul.hSMul (t ^ (k + 1)) (covarianceSeriesCoefficient M k) := by
  unfold covarianceSeriesCoefficient
  rw [<- smul_neg, smul_pow, smul_mul_smul_comm]
  congr 1
  rw [pow_succ]
  ring


omit [Nonempty Iota] in
theorem realGaussianQuotientCovariance_add_ne_zero
    (M : Matrix Iota Iota Real) (hM : M.IsHermitian) (t : Real)
    (ht : 0 <= t) (hSmall : t * norm M <= 1 / 2) :
    forall j, Not (1 + t * hM.eigenvalues j = 0) := by
  intro j hZero
  have hAbs : abs (t * hM.eigenvalues j) <= 1 / 2 := by
    calc
      _ = t * abs (hM.eigenvalues j) := by rw [abs_mul, abs_of_nonneg ht]
      _ <= t * norm M :=
        mul_le_mul_of_nonneg_left (realGaussianEigenvalue_abs_le_norm M hM j) ht
      _ <= _ := hSmall
  have hLower := (abs_le.mp hAbs).1
  linarith only [hZero, hLower]

def covarianceTaylorPolynomial (M : Matrix Iota Iota Real)
    (H : Nat) (i j : Iota) (s : Complex) : Complex :=
  Finset.sum (Finset.range H) (fun k =>
    s ^ (k + 1) * (covarianceSeriesCoefficient M k i j : Complex))

omit [Nonempty Iota] in
theorem covarianceTaylorPolynomial_analyticAt
    (M : Matrix Iota Iota Real) (H : Nat) (i j : Iota) :
    AnalyticAt Complex (covarianceTaylorPolynomial M H i j) 0 := by
  unfold covarianceTaylorPolynomial
  apply Finset.analyticAt_fun_sum
  intro k hk
  exact (analyticAt_id.pow _).mul analyticAt_const

omit [Nonempty Iota] in
theorem covarianceTaylorPolynomial_real
    (M : Matrix Iota Iota Real) (t : Real) (H : Nat) (i j : Iota) :
    covarianceTaylorPolynomial M H i j (t : Complex) =
      (Finset.sum (Finset.range H)
        (fun k => covarianceSeriesCoefficient (HSMul.hSMul t M) k i j) : Real) := by
  unfold covarianceTaylorPolynomial
  push_cast
  apply Finset.sum_congr rfl
  intro k hk
  rw [covarianceSeriesCoefficient_real_smul]
  simp only [Matrix.smul_apply, smul_eq_mul, Complex.ofReal_mul, Complex.ofReal_pow]

theorem realGaussianQuotientCovariance_polynomial_bound
    (M : Matrix Iota Iota Real) (hM : M.IsHermitian)
    (t : Real) (H : Nat) (i j : Iota)
    (ht : 0 <= t) (hSmall : t * norm M <= 1 / 2) :
    norm (gaussianLinearCovariance
        (fun k => (t : Complex) * realGaussianEigenVariances M hM k /
          (1 + (t : Complex) * realGaussianEigenVariances M hM k))
        (realGaussianEigenRows M hM i) (realGaussianEigenRows M hM j) -
      covarianceTaylorPolynomial M H i j (t : Complex)) <=
        (2 * norm M ^ (H + 1)) * t ^ (H + 1) := by
  have hQ : norm (HSMul.hSMul t M) <= 1 / 2 := by
    simpa only [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht] using hSmall
  have hBound := resolventCovariance_finite_remainder_bound (HSMul.hSMul t M) H hQ
  have hEntry := l2_matrix_entry_le_norm
    (resolventCovariance (HSMul.hSMul t M) -
      Finset.sum (Finset.range H) (covarianceSeriesCoefficient (HSMul.hSMul t M))) i j
  rw [realGaussianQuotientCovariance_entry_resolvent M hM t
    (realGaussianQuotientCovariance_add_ne_zero M hM t ht hSmall),
    covarianceTaylorPolynomial_real]
  rw [<- Complex.ofReal_sub, Complex.norm_real]
  have h := le_trans hEntry hBound
  simpa only [Matrix.sub_apply, Matrix.sum_apply, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg ht, mul_pow, mul_assoc, mul_comm, mul_left_comm] using h


omit [Nonempty Iota] in
theorem covarianceTaylorPolynomial_series
    (M : Matrix Iota Iota Real) (H : Nat) (i j : Iota) :
    wickTaylorSeries (covarianceTaylorPolynomial M H i j) =
      Finset.sum (Finset.range H) (fun k =>
        PowerSeries.monomial (k + 1) (covarianceSeriesCoefficient M k i j : Complex)) := by
  unfold covarianceTaylorPolynomial
  rw [wickTaylorSeries_finset_sum]
  case hf =>
    intro k hk
    exact (analyticAt_id.pow _).mul analyticAt_const
  simp_rw [wickTaylorSeries_power_mul]

omit [Nonempty Iota] in
theorem covarianceTaylorPolynomial_coeff_succ
    (M : Matrix Iota Iota Real) (k : Nat) (i j : Iota) :
    PowerSeries.coeff (k + 1)
        (wickTaylorSeries (covarianceTaylorPolynomial M (k + 1) i j)) =
      (covarianceSeriesCoefficient M k i j : Complex) := by
  rw [covarianceTaylorPolynomial_series, map_sum]
  have hOff : forall b, Membership.mem (Finset.range (k + 1)) b -> Not (b = k) ->
      PowerSeries.coeff (k + 1)
        (PowerSeries.monomial (b + 1) (covarianceSeriesCoefficient M b i j : Complex)) = 0 := by
    intro b hb hbk
    simp [PowerSeries.coeff_monomial, Ne.symm hbk]
  have hNot : Not (Membership.mem (Finset.range (k + 1)) k) ->
      PowerSeries.coeff (k + 1)
        (PowerSeries.monomial (k + 1) (covarianceSeriesCoefficient M k i j : Complex)) = 0 := by
    intro hk
    exact False.elim (hk (Finset.mem_range.mpr (Nat.lt_succ_self k)))
  rw [Finset.sum_eq_single k hOff hNot]
  simp only [PowerSeries.coeff_monomial, ite_true]

theorem realGaussianQuotientCovariance_taylor_match
    (M : Matrix Iota Iota Real) (hM : M.IsHermitian)
    (H k : Nat) (i j : Iota) (hk : k <= H) :
    PowerSeries.coeff k (wickTaylorSeries (fun s =>
        gaussianLinearCovariance
          (fun a => s * realGaussianEigenVariances M hM a /
            (1 + s * realGaussianEigenVariances M hM a))
          (realGaussianEigenRows M hM i) (realGaussianEigenRows M hM j))) =
      PowerSeries.coeff k
        (wickTaylorSeries (covarianceTaylorPolynomial M H i j)) := by
  let F := fun s : Complex =>
    gaussianLinearCovariance
      (fun a => s * realGaussianEigenVariances M hM a /
        (1 + s * realGaussianEigenVariances M hM a))
      (realGaussianEigenRows M hM i) (realGaussianEigenRows M hM j)
  let G := covarianceTaylorPolynomial M H i j
  have hF : AnalyticAt Complex F 0 := by
    apply gaussianLinearCovariance_analyticAt
    intro a
    exact (analyticAt_id.mul analyticAt_const).div
      (analyticAt_const.add (analyticAt_id.mul analyticAt_const)) (by simp)
  have hG : AnalyticAt Complex G 0 := covarianceTaylorPolynomial_analyticAt M H i j
  let C : Real := 2 * norm M ^ (H + 1)
  let r : Real := 1 / (2 * (norm M + 1))
  have hC : 0 <= C := by dsimp only [C]; positivity
  have hr : 0 < r := by dsimp only [r]; positivity
  have hBound : forall t : Real, 0 < t -> t < r ->
      norm ((F - G) (t : Complex)) <= C * t ^ (H + 1) := by
    intro t ht htr
    have hInv : r * (2 * (norm M + 1)) = 1 := by
      dsimp only [r]
      field_simp
    have hMul := mul_lt_mul_of_pos_right htr
      (show 0 < 2 * (norm M + 1) by positivity)
    rw [hInv] at hMul
    have hSmall : t * norm M <= 1 / 2 := by nlinarith [norm_nonneg M]
    exact realGaussianQuotientCovariance_polynomial_bound M hM t H i j ht.le hSmall
  have hDeriv := hamiltonian_derivatives_zero_of_positive_ray (F - G)
    (hF.sub hG) (H + 1) C r hC hr hBound k (Nat.lt_succ_of_le hk)
  rw [iteratedDeriv_sub hF.contDiffAt hG.contDiffAt] at hDeriv
  have hEqual : iteratedDeriv k F 0 = iteratedDeriv k G 0 := sub_eq_zero.mp hDeriv
  change PowerSeries.coeff k (wickTaylorSeries F) =
    PowerSeries.coeff k (wickTaylorSeries G)
  rw [wickTaylorSeries_coeff, wickTaylorSeries_coeff, hEqual]

theorem realGaussianCovarianceTaylorSeries_eq
    (M : Matrix Iota Iota Real) (hM : M.IsHermitian) :
    realGaussianCovarianceTaylorSeries M hM = covarianceFormalSeries M := by
  funext i j
  ext k
  cases k with
  | zero =>
    rw [realGaussianCovarianceTaylorSeries_coeff_zero, covarianceFormalSeries_coeff_zero]
  | succ k =>
    rw [covarianceFormalSeries_coeff_succ]
    change PowerSeries.coeff (k + 1) (wickTaylorSeries (fun s =>
      gaussianLinearCovariance
        (fun a => s * realGaussianEigenVariances M hM a /
          (1 + s * realGaussianEigenVariances M hM a))
        (realGaussianEigenRows M hM i) (realGaussianEigenRows M hM j))) = _
    rw [realGaussianQuotientCovariance_taylor_match M hM (k + 1) (k + 1) i j
      (le_refl _), covarianceTaylorPolynomial_coeff_succ]

theorem stochastic_compensated_taylor_covariance_series {n : Nat}
    (T : Matrix (Fin n) (Fin n) Real) (q rho : Real) (H k : Nat)
    (hn : 0 < n) (hq : (n : Real) * q = 1)
    (hRow : forall i, Finset.sum Finset.univ (fun j => T i j) = 1)
    (hCol : forall j, Finset.sum Finset.univ (fun i => T i j) = 1)
    (hNorm : norm (centeredKernel T q) <= rho) (hk : k <= H) :
    PowerSeries.coeff k (wickTaylorSeries
        (hamiltonianCompensatedRook (centeredKernel T q))) =
      PowerSeries.coeff k
        (Finset.sum (Finset.range (H + 1)) (fun e =>
          Finset.sum (Finset.range (e + 1)) (fun v =>
            wickSeriesDiagramCoefficient
              (covarianceFormalSeries (bipartiteLift (centeredKernel T q))) e v))) := by
  have : Nonempty (Fin n) := Nonempty.intro (Fin.mk 0 hn)
  have h := stochastic_compensated_taylor_wick_series T q rho H k hn hq hRow hCol hNorm hk
  rw [realGaussianCovarianceTaylorSeries_eq] at h
  exact h

end PrimeFactorOscillations

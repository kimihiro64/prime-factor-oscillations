/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianLowWickNormalForm
import PrimeFactorOscillations.Helpers.HamiltonianPermanentLocalExpansion

/-! # Analytic low correction with its inverse-dimension scale

The full signed correction remains the Gamma main term. These bounds
control only its local Taylor remainder after that main term is retained.
-/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations

variable {Iota J : Type*} [Fintype Iota] [DecidableEq Iota]
variable [Fintype J] [DecidableEq J]

theorem gaussianWickLowValue_nonconstant_norm_bound
    (z : Iota -> Complex) (row : J -> Iota -> Complex) (n : Nat) (kappa : Real)
    (hCard : Fintype.card J = 2 * n) (hn : 3 <= n) (hKappa : 0 <= kappa)
    (hCov : forall i j, norm (gaussianLinearCovariance z (row i) (row j)) <=
      kappa / (n : Real)) :
    norm (gaussianWickLowValue z row - 1) <=
      9 * (1 + 16 * Real.exp 1 * kappa) ^ 3 / (n : Real) := by
  have hnPos : 0 < n := by omega
  have hnReal : 0 < (n : Real) := Nat.cast_pos.mpr hnPos
  have hnZero : Not ((n : Real) = 0) := ne_of_gt hnReal
  let C := 16 * Real.exp 1 * kappa
  let M := (1 + C) ^ 3
  have hC : 0 <= C := by dsimp [C]; positivity
  have hM : 0 <= M := by dsimp [M]; positivity
  have hTerm : forall e v : Nat, 0 < e -> e <= 3 -> v < e ->
      norm (gaussianWickDiagramCoefficient z row e v) <= 3 * M / (n : Real) := by
    intro e v he0 he3 hv
    have hVE : v <= e := by omega
    have hEN : (e : Real) <= (n : Real) := by exact_mod_cast (show e <= n by omega)
    have hRatio0 : 0 <= (e : Real) / (n : Real) := div_nonneg (Nat.cast_nonneg e) hnReal.le
    have hRatio1 : (e : Real) / (n : Real) <= 1 := by
      simpa only [div_self hnZero] using div_le_div_of_nonneg_right hEN hnReal.le
    have hRatio3 : (e : Real) / (n : Real) <= 3 / (n : Real) :=
      div_le_div_of_nonneg_right (by exact_mod_cast he3) hnReal.le
    have hPower : ((e : Real) / (n : Real)) ^ (e - v) <= (e : Real) / (n : Real) := by
      have hIndex : e - v = (e - v - 1) + 1 := by omega
      rw [hIndex, pow_succ]
      have h := wick_unit_power_le_one _ hRatio0 hRatio1 (e - v - 1)
      have hMul := mul_le_mul_of_nonneg_right h hRatio0
      simpa only [one_mul] using hMul
    have hDegree : C ^ e <= M := by
      have h := hamiltonian_polynomial_power_bound 1 (1 + C) C e 3
        (by norm_num) (by linarith) hC (by linarith) he3
      simpa only [one_pow, one_mul, M] using h
    have hFactor : (16 * kappa) ^ e * Real.exp (e : Real) = C ^ e := by
      rw [wick_exp_nat_power, <- mul_pow]
      dsimp only [C]
      congr 1
      ring
    calc
      _ <= (16 * kappa) ^ e * Real.exp (e : Real) *
          ((e : Real) / (n : Real)) ^ (e - v) :=
        gaussianWickDiagramCoefficient_support_envelope z row n kappa e v
          hCard hnPos hKappa he0 hVE hCov
      _ = C ^ e * ((e : Real) / (n : Real)) ^ (e - v) := by rw [hFactor]
      _ <= M * (3 / (n : Real)) :=
        mul_le_mul hDegree (le_trans hPower hRatio3) (pow_nonneg hRatio0 _) hM
      _ = _ := by ring
  have h21 := hTerm 2 1 (by omega) (by omega) (by omega)
  have h31 := hTerm 3 1 (by omega) (by omega) (by omega)
  have h32 := hTerm 3 2 (by omega) (by omega) (by omega)
  rw [gaussianWickLowValue_three_profiles]
  have hIdentity : (1 + gaussianWickDiagramCoefficient z row 2 1 +
      gaussianWickDiagramCoefficient z row 3 1 +
      gaussianWickDiagramCoefficient z row 3 2) - 1 =
      (gaussianWickDiagramCoefficient z row 2 1 +
        gaussianWickDiagramCoefficient z row 3 1) +
      gaussianWickDiagramCoefficient z row 3 2 := by ring
  rw [hIdentity]
  calc
    _ <= norm (gaussianWickDiagramCoefficient z row 2 1 +
          gaussianWickDiagramCoefficient z row 3 1) +
        norm (gaussianWickDiagramCoefficient z row 3 2) := norm_add_le _ _
    _ <= norm (gaussianWickDiagramCoefficient z row 2 1) +
        norm (gaussianWickDiagramCoefficient z row 3 1) +
        norm (gaussianWickDiagramCoefficient z row 3 2) :=
      add_le_add (norm_add_le _ _) (le_refl _)
    _ <= (3 * M / (n : Real) + 3 * M / (n : Real)) + 3 * M / (n : Real) :=
      add_le_add (add_le_add h21 h31) h32
    _ = 9 * M / (n : Real) := by ring

theorem complex_diagonal_cube_norm_bound
    (G : Matrix J J Complex) (n : Nat) (kappa : Real)
    (hCard : Fintype.card J = 2 * n) (hn : 0 < n)
    (hEntry : forall i, norm (G i i) <= kappa / (n : Real)) :
    norm ((5 / 2 : Complex) *
      Finset.sum Finset.univ (fun i => G i i ^ 3)) <=
        5 * kappa ^ 3 / (n : Real) ^ 2 := by
  rw [norm_mul]
  have hScalar : norm (5 / 2 : Complex) = (5 / 2 : Real) := by norm_num
  rw [hScalar]
  have hSum : norm (Finset.sum Finset.univ (fun i => G i i ^ 3)) <=
      (2 * (n : Real)) * (kappa / (n : Real)) ^ 3 := by
    calc
      _ <= Finset.sum Finset.univ (fun i => norm (G i i ^ 3)) := norm_sum_le _ _
      _ <= Finset.sum (Finset.univ : Finset J) (fun _ => (kappa / (n : Real)) ^ 3) := by
        apply Finset.sum_le_sum
        intro i hi
        rw [norm_pow]
        exact wick_nonnegative_power_le _ _ (norm_nonneg _) (hEntry i) 3
      _ = _ := by
        simp only [Finset.sum_const, Finset.card_univ, hCard, nsmul_eq_mul, Nat.cast_mul,
          Nat.cast_ofNat]
  calc
    _ <= (5 / 2 : Real) * ((2 * (n : Real)) * (kappa / (n : Real)) ^ 3) :=
      mul_le_mul_of_nonneg_left hSum (by norm_num)
    _ = _ := by field_simp [ne_of_gt (Nat.cast_pos.mpr hn)]

def covarianceCorrectionComplexValue
    (z : Iota -> Complex) (row : J -> Iota -> Complex) : Complex :=
  gaussianWickLowValue z row - 1 +
    (5 / 2 : Complex) * Finset.sum Finset.univ (fun i =>
      gaussianLinearCovariance z (row i) (row i) ^ 3)

theorem covarianceCorrectionComplexValue_analyticAt
    (z : Complex -> Iota -> Complex) (row : J -> Iota -> Complex) (s : Complex)
    (hz : forall i, AnalyticAt Complex (fun w => z w i) s) :
    AnalyticAt Complex (fun w => covarianceCorrectionComplexValue (z w) row) s := by
  have hCov : forall i j : J, AnalyticAt Complex
      (fun w => gaussianLinearCovariance (z w) (row i) (row j)) s := by
    intro i j
    unfold gaussianLinearCovariance
    apply Finset.analyticAt_fun_sum
    intro k hk
    exact ((hz k).mul analyticAt_const).mul analyticAt_const
  have hDiag : AnalyticAt Complex (fun w => Finset.sum Finset.univ
      (fun i => gaussianLinearCovariance (z w) (row i) (row i) ^ 3)) s := by
    apply Finset.analyticAt_fun_sum
    intro i hi
    exact (hCov i i).pow 3
  exact ((gaussianWickLowValue_analyticAt z row s hz).sub analyticAt_const).add
    (analyticAt_const.mul hDiag)

theorem covarianceCorrectionComplexValue_norm_bound
    (z : Iota -> Complex) (row : J -> Iota -> Complex) (n : Nat) (kappa : Real)
    (hCard : Fintype.card J = 2 * n) (hn : 3 <= n) (hKappa : 0 <= kappa)
    (hCov : forall i j, norm (gaussianLinearCovariance z (row i) (row j)) <=
      kappa / (n : Real)) :
    norm (covarianceCorrectionComplexValue z row) <=
      20 * (1 + 16 * Real.exp 1 * kappa) ^ 3 / (n : Real) := by
  let C := 16 * Real.exp 1 * kappa
  let M := (1 + C) ^ 3
  have hC : 0 <= C := by dsimp [C]; positivity
  have hM : 0 <= M := by dsimp [M]; positivity
  have hnPos : 0 < n := by omega
  have hnReal : 0 < (n : Real) := Nat.cast_pos.mpr hnPos
  have hnOne : 1 <= (n : Real) := by exact_mod_cast (show 1 <= n by omega)
  have hExp := Real.add_one_le_exp (1 : Real)
  have hCoefficient : 1 <= 16 * Real.exp 1 := by linarith
  have hKC : kappa <= C := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hCoefficient hKappa
  have hKM : kappa ^ 3 <= M :=
    wick_nonnegative_power_le _ _ hKappa (by linarith) 3
  have hLow := gaussianWickLowValue_nonconstant_norm_bound z row n kappa hCard hn hKappa hCov
  have hDiag := complex_diagonal_cube_norm_bound
    (fun i j => gaussianLinearCovariance z (row i) (row j)) n kappa
      hCard hnPos (fun i => hCov i i)
  have hDiagPower : 5 * kappa ^ 3 / (n : Real) ^ 2 <= 5 * M / (n : Real) := by
    calc
      _ <= 5 * M / (n : Real) ^ 2 :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hKM (by norm_num)) (sq_nonneg _)
      _ = (5 * M) * (1 / (n : Real) ^ 2) := by ring
      _ <= (5 * M) * (1 / (n : Real)) :=
        mul_le_mul_of_nonneg_left
          (div_le_div_of_nonneg_left (by norm_num) hnReal (by nlinarith only [hnOne]))
          (by positivity)
      _ = _ := by ring
  unfold covarianceCorrectionComplexValue
  calc
    _ <= norm (gaussianWickLowValue z row - 1) +
        norm ((5 / 2 : Complex) * Finset.sum Finset.univ
          (fun i => gaussianLinearCovariance z (row i) (row i) ^ 3)) := norm_add_le _ _
    _ <= 9 * M / (n : Real) + 5 * M / (n : Real) :=
      add_le_add hLow (le_trans hDiag hDiagPower)
    _ = 14 * M / (n : Real) := by ring
    _ <= 20 * M / (n : Real) := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by norm_num : (14 : Real) <= 20) hM) hnReal.le

def realGaussianQuotientCorrectionFunction (M : Matrix Iota Iota Real)
    (hM : M.IsHermitian) (s : Complex) : Complex :=
  covarianceCorrectionComplexValue
    (fun j => s * realGaussianEigenVariances M hM j /
      (1 + s * realGaussianEigenVariances M hM j))
    (realGaussianEigenRows M hM)

theorem realGaussianQuotientCorrectionFunction_real (M : Matrix Iota Iota Real)
    (hM : M.IsHermitian) (s : Real)
    (hAdd : forall j, Not (1 + s * hM.eigenvalues j = 0)) :
    realGaussianQuotientCorrectionFunction M hM (s : Complex) =
      (covarianceCorrection (resolventCovariance (HSMul.hSMul s M)) : Complex) := by
  have hSum :
      Finset.sum Finset.univ (fun i =>
        gaussianLinearCovariance
          (fun j => (s : Complex) * realGaussianEigenVariances M hM j /
            (1 + (s : Complex) * realGaussianEigenVariances M hM j))
          (realGaussianEigenRows M hM i) (realGaussianEigenRows M hM i) ^ 3) =
        ((Finset.sum Finset.univ
          (fun i => resolventCovariance (HSMul.hSMul s M) i i ^ 3) : Real) : Complex) := by
    push_cast
    apply Finset.sum_congr rfl
    intro i hi
    rw [realGaussianQuotientCovariance_entry_resolvent M hM s hAdd i i]
  unfold realGaussianQuotientCorrectionFunction covarianceCorrectionComplexValue
  rw [realGaussianQuotientLowValue M hM s hAdd, hSum]
  push_cast
  ring

theorem realGaussianQuotientCorrectionFunction_analyticAt (M : Matrix Iota Iota Real)
    (hM : M.IsHermitian) (rho : Real) (hNorm : norm M <= rho)
    (s : Complex) (hs : norm s * rho < 1) :
    AnalyticAt Complex (realGaussianQuotientCorrectionFunction M hM) s := by
  unfold realGaussianQuotientCorrectionFunction
  apply covarianceCorrectionComplexValue_analyticAt
  intro j
  have hEigen : norm (realGaussianEigenVariances M hM j) <= rho := by
    simpa only [realGaussianEigenVariances, Complex.norm_real, Real.norm_eq_abs] using
      le_trans (realGaussianEigenvalue_abs_le_norm M hM j) hNorm
  have hSmall : norm (s * realGaussianEigenVariances M hM j) < 1 := by
    rw [norm_mul]
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left hEigen (norm_nonneg s)) hs
  have hUnit : IsUnit (1 - -(s * realGaussianEigenVariances M hM j)) :=
    isUnit_one_sub_of_norm_lt_one (by simpa only [norm_neg] using hSmall)
  have hNe : Not (1 + s * realGaussianEigenVariances M hM j = 0) := by
    simpa only [sub_neg_eq_add] using hUnit.ne_zero
  exact (analyticAt_id.mul analyticAt_const).div
    (analyticAt_const.add (analyticAt_id.mul analyticAt_const)) hNe

theorem stochastic_complex_correction_norm_bound {n : Nat}
    (T : Matrix (Fin n) (Fin n) Real) (q a delta : Real)
    (hn : 3 <= n) (hq : (n : Real) * q = 1) (ha : 1 <= a)
    (hRow : forall i, Finset.sum Finset.univ (fun j => T i j) = 1)
    (hCol : forall j, Finset.sum Finset.univ (fun i => T i j) = 1)
    (hNonneg : forall i j, 0 <= T i j) (hUpper : forall i j, T i j <= a * q)
    (hDelta0 : 0 < delta) (hDelta1 : delta <= 1)
    (hNorm : norm (centeredKernel T q) <= 1 - delta)
    (s : Complex) (hs : norm s <= hamiltonianWindowScale delta) :
    norm (realGaussianQuotientCorrectionFunction
      (bipartiteLift (centeredKernel T q)) (bipartiteLift_hermitian (centeredKernel T q)) s) <=
        20 * (1 + 16 * Real.exp 1 * hamiltonianPermanentWindowKappa delta a) ^ 3 /
          (n : Real) := by
  let b := hamiltonianWindowScale delta
  let kappa := hamiltonianPermanentWindowKappa delta a
  let R : NNReal := Subtype.mk (1 + delta / 8) (by positivity)
  have hnPos : 0 < n := by omega
  have hb := hamiltonian_window_scale_bounds delta hDelta0 hDelta1
  have hbR : b < (R : Real) := by
    change 1 + delta / 16 < 1 + delta / 8
    linarith
  have hGap : (R : Real) * (1 - delta) < 1 := by
    change (1 + delta / 8) * (1 - delta) < 1
    nlinarith [sq_nonneg delta]
  have hTheta : b * (1 - delta / 2) < 1 := by
    have h := hamiltonian_window_coefficient_gap delta hDelta0
    change 7 * delta / 16 <= 1 - b * (1 - delta / 2) at h
    linarith
  have hKappa0 : 0 <= kappa := by
    dsimp only [kappa, hamiltonianPermanentWindowKappa]
    exact div_nonneg (by positivity) (sub_pos.mpr hTheta).le
  have hCard : Fintype.card (Sum (Fin n) (Fin n)) = 2 * n := by
    simp only [Fintype.card_sum, Fintype.card_fin]
    omega
  have hN0 : Not ((n : Real) = 0) := ne_of_gt (Nat.cast_pos.mpr hnPos)
  have hQ : q = 1 / (n : Real) := by
    apply (eq_div_iff hN0).mpr
    simpa only [mul_comm] using hq
  unfold realGaussianQuotientCorrectionFunction
  apply covarianceCorrectionComplexValue_norm_bound _ _ n kappa hCard hn hKappa0
  intro i j
  have h := stochastic_complex_covariance_entry_bound T q a delta b R
    hnPos hq ha hRow hCol hNonneg hUpper hDelta0 hDelta1 hNorm
      hb.1.le hbR hGap hTheta s hs i j
  calc
    _ <= _ := h
    _ = _ := by rw [hQ]; dsimp only [kappa, hamiltonianPermanentWindowKappa, b]; ring

end PrimeFactorOscillations

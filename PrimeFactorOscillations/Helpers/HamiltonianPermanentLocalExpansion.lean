/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianLowWickNormalForm
import PrimeFactorOscillations.Helpers.HamiltonianPermanentCutoffClosure

/-! # Explicit local covariance correction on the whole physical window

The actual signed low value is identified before its cubic diagonal term
is bounded as an explicit N^-2 remainder, uniformly also for s greater than 1.
-/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations

theorem hamiltonian_window_eigen_add_ne_zero {n : Nat}
    (B : Matrix (Fin n) (Fin n) Real) (delta s : Real)
    (hDelta0 : 0 < delta) (hDelta1 : delta <= 1)
    (hNorm : norm B <= 1 - delta) (hs : abs s <= hamiltonianWindowScale delta) :
    forall j, Not (1 + s * (bipartiteLift_hermitian B).eigenvalues j = 0) := by
  let b := hamiltonianWindowScale delta
  have hb := hamiltonian_window_scale_bounds delta hDelta0 hDelta1
  have hb0 : 0 <= b := le_trans (by norm_num) hb.1.le
  have hTheta : b * (1 - delta / 2) < 1 := by
    have h := hamiltonian_window_coefficient_gap delta hDelta0
    change 7 * delta / 16 <= 1 - b * (1 - delta / 2) at h
    linarith
  have hProduct : abs s * (1 - delta) < 1 := by
    calc
      _ <= b * (1 - delta) :=
        mul_le_mul_of_nonneg_right hs (sub_nonneg.mpr hDelta1)
      _ <= b * (1 - delta / 2) :=
        mul_le_mul_of_nonneg_left (by linarith) hb0
      _ < 1 := hTheta
  have hGap : 0 < 1 - norm (s : Complex) * (1 - delta) := by
    simp only [Complex.norm_real, Real.norm_eq_abs]
    linarith
  intro j hZero
  have hDisk := bipartite_eigen_disk B (1 - delta) (s : Complex) hNorm hGap j
  change norm ((s : Complex) *
    (((bipartiteLift_hermitian B).eigenvalues j : Real) : Complex)) < 1 at hDisk
  rw [<- Complex.ofReal_mul, Complex.norm_real, Real.norm_eq_abs] at hDisk
  have hLower := (abs_lt.mp hDisk).1
  linarith only [hLower, hZero]

theorem stochasticLowWickValue_window_eq {n : Nat}
    (T : Matrix (Fin n) (Fin n) Real) (q delta s : Real)
    (hDelta0 : 0 < delta) (hDelta1 : delta <= 1)
    (hNorm : norm (centeredKernel T q) <= 1 - delta)
    (hs : abs s <= hamiltonianWindowScale delta) :
    stochasticLowWickValue T q s =
      1 + ((covarianceCorrection
          (resolventCovariance (HSMul.hSMul s (bipartiteLift (centeredKernel T q)))) -
        (5 / 2 : Real) * Finset.sum Finset.univ (fun i =>
          resolventCovariance (HSMul.hSMul s (bipartiteLift (centeredKernel T q))) i i ^ 3) :
        Real) : Complex) := by
  unfold stochasticLowWickValue
  exact realGaussianQuotientLowValue _ _ s
    (hamiltonian_window_eigen_add_ne_zero (centeredKernel T q)
      delta s hDelta0 hDelta1 hNorm hs)

theorem stochastic_resolvent_window_entry_bound {n : Nat}
    (T : Matrix (Fin n) (Fin n) Real) (q a delta s : Real)
    (hn : 0 < n) (hq : (n : Real) * q = 1) (ha : 1 <= a)
    (hRow : forall i, Finset.sum Finset.univ (fun j => T i j) = 1)
    (hCol : forall j, Finset.sum Finset.univ (fun i => T i j) = 1)
    (hNonneg : forall i j, 0 <= T i j) (hUpper : forall i j, T i j <= a * q)
    (hDelta0 : 0 < delta) (hDelta1 : delta <= 1)
    (hNorm : norm (centeredKernel T q) <= 1 - delta)
    (hs : abs s <= hamiltonianWindowScale delta)
    (i j : Sum (Fin n) (Fin n)) :
    norm ((resolventCovariance
        (HSMul.hSMul s (bipartiteLift (centeredKernel T q))) i j : Real) : Complex) <=
      hamiltonianPermanentWindowKappa delta a / (n : Real) := by
  let b := hamiltonianWindowScale delta
  let R : NNReal := Subtype.mk (1 + delta / 8) (by positivity)
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
  have hsComplex : norm (s : Complex) <= b := by
    simpa only [Complex.norm_real, Real.norm_eq_abs] using hs
  have hEntry := stochastic_complex_covariance_entry_bound T q a delta b R
    hn hq ha hRow hCol hNonneg hUpper hDelta0 hDelta1 hNorm
      hb.1.le hbR hGap hTheta (s : Complex) hsComplex i j
  have hAdd := hamiltonian_window_eigen_add_ne_zero
    (centeredKernel T q) delta s hDelta0 hDelta1 hNorm hs
  have hCov := realGaussianQuotientCovariance_entry_resolvent
    (bipartiteLift (centeredKernel T q)) (bipartiteLift_hermitian (centeredKernel T q))
      s hAdd i j
  have hN0 : Not ((n : Real) = 0) := ne_of_gt (Nat.cast_pos.mpr hn)
  have hQ : q = 1 / (n : Real) := by
    apply (eq_div_iff hN0).mpr
    simpa only [mul_comm] using hq
  calc
    _ = norm (realGaussianQuotientCovarianceFunction
        (bipartiteLift (centeredKernel T q)) (bipartiteLift_hermitian (centeredKernel T q))
          i j (s : Complex)) := congrArg norm hCov.symm
    _ <= _ := hEntry
    _ = _ := by rw [hQ]; unfold hamiltonianPermanentWindowKappa; dsimp only [b]; ring

theorem wickDegreeSixCorrection_entry_remainder {n : Nat}
    (G : Matrix (Sum (Fin n) (Fin n)) (Sum (Fin n) (Fin n)) Real)
    (kappa : Real) (hn : 0 < n) (hKappa : 0 <= kappa)
    (hEntry : forall i, norm ((G i i : Real) : Complex) <= kappa / (n : Real)) :
    norm (((covarianceCorrection G - (5 / 2 : Real) *
        Finset.sum Finset.univ (fun i => G i i ^ 3) : Real) : Complex) -
      (covarianceCorrection G : Complex)) <= 5 * kappa ^ 3 / (n : Real) ^ 2 := by
  have hIdentity :
      ((covarianceCorrection G - (5 / 2 : Real) *
        Finset.sum Finset.univ (fun i => G i i ^ 3) : Real) : Complex) -
        (covarianceCorrection G : Complex) =
      -(5 / 2 : Complex) * Finset.sum Finset.univ (fun i => (G i i : Complex) ^ 3) := by
    push_cast
    ring
  rw [hIdentity, norm_mul]
  have hScalar : norm (-(5 / 2 : Complex)) = (5 / 2 : Real) := by norm_num
  rw [hScalar]
  have hSum : norm (Finset.sum Finset.univ (fun i => (G i i : Complex) ^ 3)) <=
      (2 * (n : Real)) * (kappa / (n : Real)) ^ 3 := by
    calc
      _ <= Finset.sum Finset.univ (fun i => norm ((G i i : Complex) ^ 3)) :=
        norm_sum_le _ _
      _ <= Finset.sum (Finset.univ : Finset (Sum (Fin n) (Fin n)))
          (fun _ => (kappa / (n : Real)) ^ 3) := by
        apply Finset.sum_le_sum
        intro i hi
        rw [norm_pow]
        exact wick_nonnegative_power_le _ _ (norm_nonneg _) (hEntry i) 3
      _ = _ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_sum, Fintype.card_fin,
          nsmul_eq_mul, Nat.cast_add]
        ring
  calc
    _ <= (5 / 2 : Real) * ((2 * (n : Real)) * (kappa / (n : Real)) ^ 3) :=
      mul_le_mul_of_nonneg_left hSum (by norm_num)
    _ = _ := by field_simp [ne_of_gt (Nat.cast_pos.mpr hn)] <;> ring

def hamiltonianPermanentLocalCorrectionConstant (delta : Real) : Real :=
  hamiltonianPermanentWindowPolynomialConstant delta + 1080 / delta ^ 3

theorem stochastic_compensated_window_covariance_remainder {n : Nat}
    (T : Matrix (Fin n) (Fin n) Real) (q a delta s : Real)
    (hn : 11 <= n) (hq : (n : Real) * q = 1) (ha : 1 <= a)
    (hRow : forall i, Finset.sum Finset.univ (fun j => T i j) = 1)
    (hCol : forall j, Finset.sum Finset.univ (fun i => T i j) = 1)
    (hNonneg : forall i j, 0 <= T i j) (hUpper : forall i j, T i j <= a * q)
    (hDelta0 : 0 < delta) (hDelta1 : delta <= 1)
    (hNorm : norm (centeredKernel T q) <= 1 - delta)
    (hs : abs s <= hamiltonianWindowScale delta)
    (hSize : hamiltonianPermanentCutoffThreshold delta a <= Real.sqrt (n : Real)) :
    norm (hamiltonianCompensatedRook (centeredKernel T q) (s : Complex) -
      (1 + (covarianceCorrection
        (resolventCovariance (HSMul.hSMul s (bipartiteLift (centeredKernel T q)))) : Complex))) <=
      hamiltonianPermanentLocalCorrectionConstant delta * (1 + a) ^ 24 / (n : Real) ^ 2 := by
  let G := resolventCovariance (HSMul.hSMul s (bipartiteLift (centeredKernel T q)))
  let kappa := hamiltonianPermanentWindowKappa delta a
  let L := stochasticLowWickValue T q s
  let X := hamiltonianCompensatedRook (centeredKernel T q) (s : Complex)
  let Y : Complex := 1 + (covarianceCorrection G : Complex)
  have hnPos : 0 < n := by omega
  have hGap : 0 < 1 - hamiltonianWindowScale delta * (1 - delta / 2) := by
    have h := hamiltonian_window_coefficient_gap delta hDelta0
    linarith
  have hKappa0 : 0 <= kappa := by
    dsimp only [kappa, hamiltonianPermanentWindowKappa]
    positivity
  have hEntry : forall i, norm ((G i i : Real) : Complex) <= kappa / (n : Real) := by
    intro i
    exact stochastic_resolvent_window_entry_bound T q a delta s hnPos hq ha
      hRow hCol hNonneg hUpper hDelta0 hDelta1 hNorm hs i i
  have hDiag := wickDegreeSixCorrection_entry_remainder G kappa hnPos hKappa0 hEntry
  have hLow := stochasticLowWickValue_window_eq T q delta s hDelta0 hDelta1 hNorm hs
  have hIdentity : L - Y =
      ((covarianceCorrection G - (5 / 2 : Real) *
        Finset.sum Finset.univ (fun i => G i i ^ 3) : Real) : Complex) -
      (covarianceCorrection G : Complex) := by
    dsimp only [L, Y]
    rw [hLow]
    change (1 + ((covarianceCorrection G - (5 / 2 : Real) *
      Finset.sum Finset.univ (fun i => G i i ^ 3) : Real) : Complex)) -
        (1 + (covarianceCorrection G : Complex)) = _
    ring
  have hLowBound : norm (L - Y) <= 5 * kappa ^ 3 / (n : Real) ^ 2 := by
    rw [hIdentity]
    exact hDiag
  have hKappa : kappa <= (6 / delta) * (1 + a) := by
    calc
      _ <= 6 * a / delta :=
        hamiltonian_window_coefficient_kappa_bound delta a hDelta0 hDelta1 (by linarith)
      _ <= 6 * (1 + a) / delta :=
        div_le_div_of_nonneg_right (by linarith) hDelta0.le
      _ = _ := by ring
  have hPower := hamiltonian_polynomial_power_bound (6 / delta) (1 + a) kappa
    3 24 (by positivity) (by linarith) hKappa0 hKappa (by omega)
  have hDiagNumerator : 5 * kappa ^ 3 <= (1080 / delta ^ 3) * (1 + a) ^ 24 := by
    calc
      _ <= 5 * ((6 / delta) ^ 3 * (1 + a) ^ 24) :=
        mul_le_mul_of_nonneg_left hPower (by norm_num)
      _ = _ := by field_simp [ne_of_gt hDelta0] <;> ring
  have hLowFinal : norm (L - Y) <=
      ((1080 / delta ^ 3) * (1 + a) ^ 24) / (n : Real) ^ 2 :=
    le_trans hLowBound (div_le_div_of_nonneg_right hDiagNumerator (sq_nonneg _))
  have hMain := stochastic_compensated_fullLow_window_polynomial_remainder
    T q a delta s hn hq ha hRow hCol hNonneg hUpper hDelta0 hDelta1 hNorm hs hSize
  change norm (X - Y) <= _
  have hSplit : X - Y = (X - L) + (L - Y) := by ring
  rw [hSplit]
  calc
    _ <= norm (X - L) + norm (L - Y) := norm_add_le _ _
    _ <= hamiltonianPermanentWindowPolynomialConstant delta * (1 + a) ^ 24 / (n : Real) ^ 2 +
        ((1080 / delta ^ 3) * (1 + a) ^ 24) / (n : Real) ^ 2 :=
      add_le_add hMain hLowFinal
    _ = _ := by unfold hamiltonianPermanentLocalCorrectionConstant; ring

end PrimeFactorOscillations

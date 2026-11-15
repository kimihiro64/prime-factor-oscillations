/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianCauchyLinearRemainder
import PrimeFactorOscillations.Helpers.HamiltonianLowCorrectionAnalyticBounds

/-! # Uniform Taylor data for the actual stochastic covariance correction

The analytic function is the actual complete Wick correction. Its real
restriction is the matrix resolvent correction used by the Gamma average.
-/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations

def stochasticCovarianceCorrectionShift {n : Nat}
    (T : Matrix (Fin n) (Fin n) Real) (q : Real) (w : Complex) : Complex :=
  realGaussianQuotientCorrectionFunction (bipartiteLift (centeredKernel T q))
    (bipartiteLift_hermitian (centeredKernel T q)) (1 + w)

def stochasticCovarianceLinearCoefficient {n : Nat}
    (T : Matrix (Fin n) (Fin n) Real) (q : Real) : Real :=
  (PowerSeries.coeff 1 (wickTaylorSeries (stochasticCovarianceCorrectionShift T q))).re

theorem hamiltonianCorrection_shift_norm_bound (delta : Real) (hDelta0 : 0 < delta)
    (w : Complex) (hw : norm w <= delta / 32) :
    norm (1 + w) <= hamiltonianWindowScale delta := by
  have h := norm_add_le (1 : Complex) w
  rw [norm_one] at h
  unfold hamiltonianWindowScale
  linarith

theorem stochastic_correction_shift_disk_data {n : Nat}
    (T : Matrix (Fin n) (Fin n) Real) (q a delta : Real) (r : NNReal)
    (hn : 3 <= n) (hq : (n : Real) * q = 1) (ha : 1 <= a)
    (hRow : forall i, Finset.sum Finset.univ (fun j => T i j) = 1)
    (hCol : forall j, Finset.sum Finset.univ (fun i => T i j) = 1)
    (hNonneg : forall i j, 0 <= T i j) (hUpper : forall i j, T i j <= a * q)
    (hDelta0 : 0 < delta) (hDelta1 : delta <= 1)
    (hNorm : norm (centeredKernel T q) <= 1 - delta)
    (hr : (r : Real) <= delta / 32) :
    And (forall w, Membership.mem (Metric.closedBall (0 : Complex) (r : Real)) w ->
        AnalyticAt Complex (stochasticCovarianceCorrectionShift T q) w)
      (forall w, Membership.mem (Metric.sphere (0 : Complex) (r : Real)) w ->
        norm (stochasticCovarianceCorrectionShift T q w) <=
          20 * (1 + 16 * Real.exp 1 * hamiltonianPermanentWindowKappa delta a) ^ 3 /
            (n : Real)) := by
  have hnPos : 0 < n := by omega
  have : Nonempty (Fin n) := Nonempty.intro (Fin.mk 0 hnPos)
  let B := centeredKernel T q
  let b := hamiltonianWindowScale delta
  have hb := hamiltonian_window_scale_bounds delta hDelta0 hDelta1
  have hb0 : 0 <= b := le_trans (by norm_num) hb.1.le
  have hTheta : b * (1 - delta / 2) < 1 := by
    have h := hamiltonian_window_coefficient_gap delta hDelta0
    change 7 * delta / 16 <= 1 - b * (1 - delta / 2) at h
    linarith
  have hBlockNorm : norm (bipartiteLift B) <= 1 - delta :=
    le_trans (bipartiteLift_l2_norm_le B) hNorm
  constructor
  next =>
    intro w hw
    have hwNorm : norm w <= (r : Real) := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hw
    have hSize := hamiltonianCorrection_shift_norm_bound delta hDelta0 w
      (le_trans hwNorm hr)
    have hGap : norm (1 + w) * (1 - delta) < 1 := by
      calc
        _ <= b * (1 - delta) :=
          mul_le_mul_of_nonneg_right hSize (sub_nonneg.mpr hDelta1)
        _ <= b * (1 - delta / 2) :=
          mul_le_mul_of_nonneg_left (by linarith) hb0
        _ < 1 := hTheta
    unfold stochasticCovarianceCorrectionShift
    exact (realGaussianQuotientCorrectionFunction_analyticAt
      (bipartiteLift B) (bipartiteLift_hermitian B) (1 - delta)
        hBlockNorm (1 + w) hGap).comp (analyticAt_const.add analyticAt_id)
  next =>
    intro w hw
    have hwNorm : norm w = (r : Real) := by
      simpa only [Metric.mem_sphere, dist_zero_right] using hw
    have hSize := hamiltonianCorrection_shift_norm_bound delta hDelta0 w
      (le_trans hwNorm.le hr)
    exact stochastic_complex_correction_norm_bound T q a delta hn hq ha
      hRow hCol hNonneg hUpper hDelta0 hDelta1 hNorm (1 + w) hSize

theorem stochastic_covarianceCorrection_linear_coefficient_bound {n : Nat}
    (T : Matrix (Fin n) (Fin n) Real) (q a delta : Real)
    (hn : 3 <= n) (hq : (n : Real) * q = 1) (ha : 1 <= a)
    (hRow : forall i, Finset.sum Finset.univ (fun j => T i j) = 1)
    (hCol : forall j, Finset.sum Finset.univ (fun i => T i j) = 1)
    (hNonneg : forall i j, 0 <= T i j) (hUpper : forall i j, T i j <= a * q)
    (hDelta0 : 0 < delta) (hDelta1 : delta <= 1)
    (hNorm : norm (centeredKernel T q) <= 1 - delta) :
    abs (stochasticCovarianceLinearCoefficient T q) <=
      640 * (1 + 16 * Real.exp 1 * hamiltonianPermanentWindowKappa delta a) ^ 3 /
        (delta * (n : Real)) := by
  let r : NNReal := Subtype.mk (delta / 32) (by positivity)
  let C := (1 + 16 * Real.exp 1 * hamiltonianPermanentWindowKappa delta a) ^ 3
  let M := 20 * C / (n : Real)
  have hrReal : 0 < (r : Real) := by change 0 < delta / 32; positivity
  have hr : 0 < r := by exact_mod_cast hrReal
  have hData := stochastic_correction_shift_disk_data T q a delta r hn hq ha hRow hCol
    hNonneg hUpper hDelta0 hDelta1 hNorm (le_refl _)
  have hCoeff := hamiltonianTaylorCoefficient_norm_bound (stochasticCovarianceCorrectionShift T q)
    r M 1 hr hData.1 hData.2
  have hnPos : 0 < n := by omega
  calc
    _ <= norm (PowerSeries.coeff 1
        (wickTaylorSeries (stochasticCovarianceCorrectionShift T q))) :=
      Complex.abs_re_le_norm _
    _ <= M * Inv.inv (r : Real) := by simpa only [pow_one] using hCoeff
    _ = _ := by
      change (20 * C / (n : Real)) * Inv.inv (delta / 32) =
        640 * C / (delta * (n : Real))
      field_simp [ne_of_gt hDelta0, ne_of_gt (Nat.cast_pos.mpr hnPos)] <;> ring

theorem stochastic_covarianceCorrection_quadratic_remainder {n : Nat}
    (T : Matrix (Fin n) (Fin n) Real) (q a delta s : Real)
    (hn : 3 <= n) (hq : (n : Real) * q = 1) (ha : 1 <= a)
    (hRow : forall i, Finset.sum Finset.univ (fun j => T i j) = 1)
    (hCol : forall j, Finset.sum Finset.univ (fun i => T i j) = 1)
    (hNonneg : forall i j, 0 <= T i j) (hUpper : forall i j, T i j <= a * q)
    (hDelta0 : 0 < delta) (hDelta1 : delta <= 1)
    (hNorm : norm (centeredKernel T q) <= 1 - delta)
    (hs : abs (s - 1) <= delta / 64) :
    abs (covarianceCorrection
        (resolventCovariance (HSMul.hSMul s (bipartiteLift (centeredKernel T q)))) -
      covarianceCorrection
        (resolventCovariance (HSMul.hSMul (1 : Real) (bipartiteLift (centeredKernel T q)))) -
      (s - 1) * stochasticCovarianceLinearCoefficient T q) <=
      40960 * (1 + 16 * Real.exp 1 * hamiltonianPermanentWindowKappa delta a) ^ 3 *
        (s - 1) ^ 2 / (delta ^ 2 * (n : Real)) := by
  let B := centeredKernel T q
  let P : Real -> Real := fun v =>
    covarianceCorrection (resolventCovariance (HSMul.hSMul v (bipartiteLift B)))
  let g := stochasticCovarianceCorrectionShift T q
  let r : NNReal := Subtype.mk (delta / 32) (by positivity)
  let C := (1 + 16 * Real.exp 1 * hamiltonianPermanentWindowKappa delta a) ^ 3
  let M := 20 * C / (n : Real)
  let t : Complex := ((s - 1 : Real) : Complex)
  have hnPos : 0 < n := by omega
  have hrReal : 0 < (r : Real) := by change 0 < delta / 32; positivity
  have hr : 0 < r := by exact_mod_cast hrReal
  have hGap : 0 < 1 - hamiltonianWindowScale delta * (1 - delta / 2) := by
    have h := hamiltonian_window_coefficient_gap delta hDelta0
    linarith
  have hKappa0 : 0 <= hamiltonianPermanentWindowKappa delta a := by
    unfold hamiltonianPermanentWindowKappa
    positivity
  have hM0 : 0 <= M := by dsimp only [M, C]; positivity
  have hData := stochastic_correction_shift_disk_data T q a delta r hn hq ha hRow hCol
    hNonneg hUpper hDelta0 hDelta1 hNorm (le_refl _)
  have hNormT : norm t = abs (s - 1) := by
    dsimp only [t]
    rw [Complex.norm_real, Real.norm_eq_abs]
  have hStep : norm t <= (r : Real) / 2 := by
    calc
      _ = abs (s - 1) := hNormT
      _ <= delta / 64 := hs
      _ = _ := by change delta / 64 = (delta / 32) / 2; ring
  have hTail := hamiltonianCauchy_linear_remainder g r M hr hM0 hData.1 hData.2 t hStep
  have hReal : forall v : Real, abs v <= hamiltonianWindowScale delta ->
      g ((v - 1 : Real) : Complex) = (P v : Complex) := by
    intro v hv
    dsimp only [g, stochasticCovarianceCorrectionShift]
    have hPoint : (1 : Complex) + ((v - 1 : Real) : Complex) = (v : Complex) := by
      push_cast
      ring
    rw [hPoint]
    exact realGaussianQuotientCorrectionFunction_real
      (bipartiteLift B) (bipartiteLift_hermitian B) v
        (hamiltonian_window_eigen_add_ne_zero B delta v hDelta0 hDelta1 hNorm hv)
  have hSizeS : abs s <= hamiltonianWindowScale delta := by
    have hT32 : norm t <= delta / 32 := by rw [hNormT]; linarith only [hs, hDelta0]
    have hBound := hamiltonianCorrection_shift_norm_bound delta hDelta0 t hT32
    have hPoint : (1 : Complex) + t = (s : Complex) := by dsimp only [t]; push_cast; ring
    rw [hPoint] at hBound
    simpa only [Complex.norm_real, Real.norm_eq_abs] using hBound
  have hAtT : g t = (P s : Complex) := hReal s hSizeS
  have hAtZero : g 0 = (P 1 : Complex) := by
    have hb := hamiltonian_window_scale_bounds delta hDelta0 hDelta1
    have hBound : abs (1 : Real) <= hamiltonianWindowScale delta := by
      simpa only [abs_one] using hb.1.le
    simpa only [sub_self, Complex.ofReal_zero] using hReal 1 hBound
  rw [hAtT, hAtZero] at hTail
  have hRe := Complex.abs_re_le_norm
    ((P s : Complex) - (P 1 : Complex) -
      t * PowerSeries.coeff 1 (wickTaylorSeries g))
  have hReIdentity :
      (((P s : Complex) - (P 1 : Complex) -
        t * PowerSeries.coeff 1 (wickTaylorSeries g))).re =
      P s - P 1 - (s - 1) * stochasticCovarianceLinearCoefficient T q := by
    dsimp only [t, g, stochasticCovarianceLinearCoefficient]
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.mul_re,
      Complex.ofReal_im, zero_mul, sub_zero]
  change abs (P s - P 1 - (s - 1) * stochasticCovarianceLinearCoefficient T q) <= _
  calc
    _ = abs (((P s : Complex) - (P 1 : Complex) -
        t * PowerSeries.coeff 1 (wickTaylorSeries g))).re := congrArg abs hReIdentity.symm
    _ <= norm ((P s : Complex) - (P 1 : Complex) -
        t * PowerSeries.coeff 1 (wickTaylorSeries g)) := hRe
    _ <= 2 * M * norm t ^ 2 / (r : Real) ^ 2 := hTail
    _ = _ := by
      rw [hNormT, sq_abs]
      change 2 * (20 * C / (n : Real)) * (s - 1) ^ 2 / (delta / 32) ^ 2 =
        40960 * C * (s - 1) ^ 2 / (delta ^ 2 * (n : Real))
      field_simp [ne_of_gt hDelta0, ne_of_gt (Nat.cast_pos.mpr hnPos)] <;> ring

end PrimeFactorOscillations

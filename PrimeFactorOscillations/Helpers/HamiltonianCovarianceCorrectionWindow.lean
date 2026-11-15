/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianCovarianceCorrectionTaylor
import PrimeFactorOscillations.Helpers.HamiltonianMatrixSpectralAverage

/-! # Actual covariance correction on the physical Gamma window

Local analyticity is transferred to the real matrix correction. Measurability
is proved only on the needed window, without imposing global smoothness across
resolvent poles or assuming that an indicator is measurable.
-/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations

theorem stochastic_covarianceCorrection_window_real {n : Nat}
    (T : Matrix (Fin n) (Fin n) Real) (q delta s : Real)
    (hDelta0 : 0 < delta) (hDelta1 : delta <= 1)
    (hNorm : norm (centeredKernel T q) <= 1 - delta)
    (hs : abs (s - 1) <= delta / 32) :
    stochasticCovarianceCorrectionShift T q ((s - 1 : Real) : Complex) =
      (covarianceCorrection
        (resolventCovariance (HSMul.hSMul s (bipartiteLift (centeredKernel T q)))) : Complex) := by
  have hPoint : (1 : Complex) + ((s - 1 : Real) : Complex) = (s : Complex) := by
    push_cast
    ring
  have hW : norm ((s - 1 : Real) : Complex) <= delta / 32 := by
    simpa only [Complex.norm_real, Real.norm_eq_abs] using hs
  have hSize := hamiltonianCorrection_shift_norm_bound delta hDelta0
    ((s - 1 : Real) : Complex) hW
  rw [hPoint] at hSize
  have hRealSize : abs s <= hamiltonianWindowScale delta := by
    simpa only [Complex.norm_real, Real.norm_eq_abs] using hSize
  unfold stochasticCovarianceCorrectionShift
  rw [hPoint]
  exact realGaussianQuotientCorrectionFunction_real
    (bipartiteLift (centeredKernel T q))
    (bipartiteLift_hermitian (centeredKernel T q)) s
    (hamiltonian_window_eigen_add_ne_zero _ delta s hDelta0 hDelta1 hNorm hRealSize)

theorem stochastic_covarianceCorrection_window_bound {n : Nat}
    (T : Matrix (Fin n) (Fin n) Real) (q a delta s : Real)
    (hn : 3 <= n) (hq : (n : Real) * q = 1) (ha : 1 <= a)
    (hRow : forall i, Finset.sum Finset.univ (fun j => T i j) = 1)
    (hCol : forall j, Finset.sum Finset.univ (fun i => T i j) = 1)
    (hNonneg : forall i j, 0 <= T i j) (hUpper : forall i j, T i j <= a * q)
    (hDelta0 : 0 < delta) (hDelta1 : delta <= 1)
    (hNorm : norm (centeredKernel T q) <= 1 - delta)
    (hs : abs (s - 1) <= delta / 32) :
    abs (covarianceCorrection
        (resolventCovariance (HSMul.hSMul s (bipartiteLift (centeredKernel T q))))) <=
      20 * (1 + 16 * Real.exp 1 * hamiltonianPermanentWindowKappa delta a) ^ 3 /
        (n : Real) := by
  have hW : norm ((s - 1 : Real) : Complex) <= delta / 32 := by
    simpa only [Complex.norm_real, Real.norm_eq_abs] using hs
  have hSize := hamiltonianCorrection_shift_norm_bound delta hDelta0
    ((s - 1 : Real) : Complex) hW
  have hPoint : (1 : Complex) + ((s - 1 : Real) : Complex) = (s : Complex) := by
    push_cast
    ring
  rw [hPoint] at hSize
  have hBound := stochastic_complex_correction_norm_bound T q a delta hn hq ha
    hRow hCol hNonneg hUpper hDelta0 hDelta1 hNorm (s : Complex) hSize
  have hReal := stochastic_covarianceCorrection_window_real T q delta s
    hDelta0 hDelta1 hNorm hs
  unfold stochasticCovarianceCorrectionShift at hReal
  rw [hPoint] at hReal
  rw [hReal, Complex.norm_real, Real.norm_eq_abs] at hBound
  exact hBound

set_option maxHeartbeats 1000000 in
theorem stochastic_covarianceCorrection_continuousOn_window {n : Nat}
    (T : Matrix (Fin n) (Fin n) Real) (q a delta eps : Real)
    (hn : 3 <= n) (hq : (n : Real) * q = 1) (ha : 1 <= a)
    (hRow : forall i, Finset.sum Finset.univ (fun j => T i j) = 1)
    (hCol : forall j, Finset.sum Finset.univ (fun i => T i j) = 1)
    (hNonneg : forall i j, 0 <= T i j) (hUpper : forall i j, T i j <= a * q)
    (hDelta0 : 0 < delta) (hDelta1 : delta <= 1)
    (hNorm : norm (centeredKernel T q) <= 1 - delta)
    (hEps : eps <= delta / 32) :
    ContinuousOn (fun s : Real => covarianceCorrection
      (resolventCovariance (HSMul.hSMul s (bipartiteLift (centeredKernel T q)))))
      {s : Real | abs (s - 1) <= eps} := by
  let r : NNReal := Subtype.mk (delta / 32) (by positivity)
  let f : Real -> Complex := fun s =>
    stochasticCovarianceCorrectionShift T q ((s - 1 : Real) : Complex)
  have hData := stochastic_correction_shift_disk_data T q a delta r hn hq ha
    hRow hCol hNonneg hUpper hDelta0 hDelta1 hNorm (le_refl _)
  have hCont : ContinuousOn (fun s : Real => (f s).re)
      {s : Real | abs (s - 1) <= eps} := by
    intro s hs
    have hBall : Membership.mem (Metric.closedBall (0 : Complex) (r : Real))
        ((s - 1 : Real) : Complex) := by
      rw [Metric.mem_closedBall, dist_zero_right, Complex.norm_real, Real.norm_eq_abs]
      change abs (s - 1) <= delta / 32
      exact le_trans hs hEps
    have hAnalytic := hData.1 _ hBall
    have hMap : ContinuousAt (fun v : Real => ((v - 1 : Real) : Complex)) s :=
      Complex.continuous_ofReal.continuousAt.comp
        (continuousAt_id.sub continuousAt_const)
    have hComplexAt : ContinuousAt (stochasticCovarianceCorrectionShift T q)
        ((s - 1 : Real) : Complex) := hAnalytic.continuousAt
    have hComp : ContinuousAt f s :=
      ContinuousAt.comp (f := fun v : Real => ((v - 1 : Real) : Complex))
        (g := stochasticCovarianceCorrectionShift T q) hComplexAt hMap
    have hRe : ContinuousAt (fun v : Real => (f v).re) s :=
      Complex.continuous_re.continuousAt.comp hComp
    exact hRe.continuousWithinAt
  apply hCont.congr
  intro s hs
  have h := stochastic_covarianceCorrection_window_real T q delta s
    hDelta0 hDelta1 hNorm (le_trans hs hEps)
  exact (congrArg Complex.re h).symm

theorem stochastic_covarianceCorrection_product_window_measurable {n : Nat}
    (T : Matrix (Fin n) (Fin n) Real) (q a delta eps : Real)
    (hn : 3 <= n) (hq : (n : Real) * q = 1) (ha : 1 <= a)
    (hRow : forall i, Finset.sum Finset.univ (fun j => T i j) = 1)
    (hCol : forall j, Finset.sum Finset.univ (fun i => T i j) = 1)
    (hNonneg : forall i j, 0 <= T i j) (hUpper : forall i j, T i j <= a * q)
    (hDelta0 : 0 < delta) (hDelta1 : delta <= 1)
    (hNorm : norm (centeredKernel T q) <= 1 - delta)
    (hEps0 : 0 <= eps) (hEps : eps <= delta / 32) :
    Measurable (Set.indicator {s : Real | abs (s - 1) <= eps}
      (fun s => realGramDeterminantFactor (centeredKernel T q) s *
        covarianceCorrection
          (resolventCovariance (HSMul.hSMul s (bipartiteLift (centeredKernel T q)))))) := by
  classical
  let C : Set Real := {s | abs (s - 1) <= eps}
  let B := centeredKernel T q
  let lam := realGramEigenvalues B
  have hData := stochasticGram_spectral_data T q a delta
    (by simpa only [Fintype.card_fin] using hq) hRow hNonneg hUpper hDelta1 hNorm
  have hSpectral : ContinuousOn (spectralFactors Finset.univ lam) C := by
    intro s hs
    apply (spectralFactors_contDiffAt Finset.univ lam s _).continuousAt.continuousWithinAt
    intro i hi
    have hStrip := spectralFactor_strip delta eps (lam i) s hDelta0 hDelta1
      hEps0 (by linarith only [hEps, hDelta0]) (hData.1 i) (hData.2.1 i) hs
    exact ne_of_gt (lt_of_lt_of_le hDelta0 hStrip.2.2.2)
  have hDet : ContinuousOn (realGramDeterminantFactor B) C := by
    apply hSpectral.congr
    intro s hs
    exact realGramDeterminantFactor_eq_spectral_on_strip B delta eps s
      hDelta0 hDelta1 hEps0 (by linarith only [hEps, hDelta0]) hNorm hs
  have hCorr := stochastic_covarianceCorrection_continuousOn_window T q a delta eps
    hn hq ha hRow hCol hNonneg hUpper hDelta0 hDelta1 hNorm hEps
  have hProd := hDet.mul hCorr
  have hMap : Measurable (fun s : Real => abs (s - 1)) := by
    simpa only [Real.norm_eq_abs] using (measurable_sub_const (1 : Real)).norm
  have hC : MeasurableSet C := measurableSet_le hMap measurable_const
  change Measurable (C.piecewise
    (fun s : Real => realGramDeterminantFactor B s *
      covarianceCorrection (resolventCovariance (HSMul.hSMul s (bipartiteLift B))))
    (fun _ : Real => 0))
  exact hProd.measurable_piecewise continuous_zero.continuousOn hC

end PrimeFactorOscillations

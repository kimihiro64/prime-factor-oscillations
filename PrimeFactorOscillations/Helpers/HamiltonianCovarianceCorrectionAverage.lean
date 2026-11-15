/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianCovarianceCorrectionWindow
import PrimeFactorOscillations.Helpers.HamiltonianSpectralProductAverage

/-! # Actual signed covariance correction in the Gamma average

Every hypothesis of the affine Gamma consumer is discharged for an admissible
stochastic kernel. The constant covariance correction is kept, the complete
linear product term is canceled only through its exact full moment, and its
discarded tail remains explicit.
-/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations

def stochasticCorrectionGammaRemainderBound {n : Nat}
    (T : Matrix (Fin n) (Fin n) Real) (q a delta eps : Real) : Real :=
  let C := (1 + 16 * Real.exp 1 * hamiltonianPermanentWindowKappa delta a) ^ 3
  spectralCorrectionProductRemainderBound Finset.univ
    (realGramEigenvalues (centeredKernel T q)) delta eps
    (20 * C / (n : Real))
    (640 * C / (delta * (n : Real)))
    (40960 * C / (delta ^ 2 * (n : Real)))

def stochasticCorrectionGammaLinear {n : Nat}
    (T : Matrix (Fin n) (Fin n) Real) (q : Real) : Real :=
  realGramDeterminantFactor (centeredKernel T q) 1 *
      stochasticCovarianceLinearCoefficient T q +
    spectralFactorJet1 Finset.univ (realGramEigenvalues (centeredKernel T q)) 1 *
      covarianceCorrection
        (resolventCovariance (HSMul.hSMul (1 : Real) (bipartiteLift (centeredKernel T q))))

theorem stochastic_covarianceCorrection_gamma_window {n : Nat}
    (T : Matrix (Fin n) (Fin n) Real) (q a delta eps : Real)
    (hn : 16 <= n) (hq : (n : Real) * q = 1) (ha : 1 <= a)
    (hRow : forall i, Finset.sum Finset.univ (fun j => T i j) = 1)
    (hCol : forall j, Finset.sum Finset.univ (fun i => T i j) = 1)
    (hNonneg : forall i j, 0 <= T i j) (hUpper : forall i j, T i j <= a * q)
    (hDelta0 : 0 < delta) (hDelta1 : delta <= 1)
    (hNorm : norm (centeredKernel T q) <= 1 - delta)
    (hEps0 : 0 < eps) (hEps : eps <= delta / 64)
    (hLarge : 4 <= (n : Real) * eps)
    (hSmall : 2 * (a - 1) * eps <= delta) :
    abs (gammaInverseAverage n
        (Set.indicator {s : Real | abs (s - 1) <= eps}
          (fun s => realGramDeterminantFactor (centeredKernel T q) s *
            covarianceCorrection
              (resolventCovariance (HSMul.hSMul s (bipartiteLift (centeredKernel T q)))))) -
      realGramDeterminantFactor (centeredKernel T q) 1 *
        covarianceCorrection
          (resolventCovariance (HSMul.hSMul (1 : Real) (bipartiteLift (centeredKernel T q))))) <=
      stochasticCorrectionGammaRemainderBound T q a delta eps *
        (1 / ((n : Real) - 1)) +
      Real.exp (-((n : Real) + 1) * eps ^ 2 / 72) *
        (4 * abs (realGramDeterminantFactor (centeredKernel T q) 1 *
          covarianceCorrection
            (resolventCovariance (HSMul.hSMul (1 : Real) (bipartiteLift (centeredKernel T q))))) +
          7 * abs (stochasticCorrectionGammaLinear T q)) := by
  classical
  let B := centeredKernel T q
  let lam := realGramEigenvalues B
  let P : Real -> Real := fun s => covarianceCorrection
    (resolventCovariance (HSMul.hSMul s (bipartiteLift B)))
  let C := (1 + 16 * Real.exp 1 * hamiltonianPermanentWindowKappa delta a) ^ 3
  let G0 := 20 * C / (n : Real)
  let G1 := 640 * C / (delta * (n : Real))
  let G2 := 40960 * C / (delta ^ 2 * (n : Real))
  let M := stochasticCorrectionGammaRemainderBound T q a delta eps
  have hn3 : 3 <= n := by omega
  have hnPos : 0 < (n : Real) := Nat.cast_pos.mpr (by omega)
  have hEps32 : eps <= delta / 32 := by linarith only [hEps, hDelta0]
  have hEps4 : eps <= delta / 4 := by linarith only [hEps, hDelta0]
  have hEpsHalf : eps <= 1 / 2 := by linarith only [hEps, hDelta1]
  have hGap : 0 < 1 - hamiltonianWindowScale delta * (1 - delta / 2) := by
    have h := hamiltonian_window_coefficient_gap delta hDelta0
    linarith
  have hKappa : 0 <= hamiltonianPermanentWindowKappa delta a := by
    unfold hamiltonianPermanentWindowKappa
    positivity
  have hC0 : 0 <= C := by dsimp only [C]; positivity
  have hG0 : 0 <= G0 := by dsimp only [G0]; positivity
  have hG1 : 0 <= G1 := by dsimp only [G1]; positivity
  have hG2 : 0 <= G2 := by dsimp only [G2]; positivity
  have hData := stochasticGram_spectral_data T q a delta
    (by simpa only [Fintype.card_fin] using hq) hRow hNonneg hUpper hDelta1 hNorm
  have hSmall' : 2 * (Finset.sum Finset.univ lam) * eps <= delta := by
    have h := mul_le_mul_of_nonneg_right hData.2.2 hEps0.le
    change Finset.sum Finset.univ lam * eps <= (a - 1) * eps at h
    linarith only [h, hSmall]
  have hDet : forall s, abs (s - 1) <= eps ->
      realGramDeterminantFactor B s = spectralFactors Finset.univ lam s := by
    intro s hs
    exact realGramDeterminantFactor_eq_spectral_on_strip B delta eps s
      hDelta0 hDelta1 hEps0.le hEps4 hNorm hs
  have hOne : abs ((1 : Real) - 1) <= eps := by simpa only [sub_self, abs_zero] using hEps0.le
  have hDetOne := hDet 1 hOne
  have hP0 : abs (P 1) <= G0 :=
    stochastic_covarianceCorrection_window_bound T q a delta 1 hn3 hq ha hRow hCol
      hNonneg hUpper hDelta0 hDelta1 hNorm (by simp only [sub_self, abs_zero]; positivity)
  have hP1 : abs (stochasticCovarianceLinearCoefficient T q) <= G1 :=
    stochastic_covarianceCorrection_linear_coefficient_bound T q a delta hn3 hq ha
      hRow hCol hNonneg hUpper hDelta0 hDelta1 hNorm
  have hP2 : forall s, abs (s - 1) <= eps ->
      abs (P s - P 1 - (s - 1) * stochasticCovarianceLinearCoefficient T q) <=
        G2 * (s - 1) ^ 2 := by
    intro s hs
    have h := stochastic_covarianceCorrection_quadratic_remainder T q a delta s hn3
      hq ha hRow hCol hNonneg hUpper hDelta0 hDelta1 hNorm (le_trans hs hEps)
    change abs (P s - P 1 - (s - 1) * stochasticCovarianceLinearCoefficient T q) <= _
    calc
      _ <= 40960 * C * (s - 1) ^ 2 / (delta ^ 2 * (n : Real)) := h
      _ = G2 * (s - 1) ^ 2 := by dsimp only [G2]; ring
  have hM : 0 <= M := by
    have hPos : 0 < spectralFactors Finset.univ lam 1 := Real.exp_pos _
    have hMass : 0 <= Finset.sum Finset.univ lam :=
      Finset.sum_nonneg (fun i hi => hData.1 i)
    dsimp only [M, stochasticCorrectionGammaRemainderBound,
      spectralCorrectionProductRemainderBound, spectralAffineRemainderBound,
      spectralTaylorRemainderBound]
    positivity
  have hMeas := stochastic_covarianceCorrection_product_window_measurable T q a delta eps
    hn3 hq ha hRow hCol hNonneg hUpper hDelta0 hDelta1 hNorm hEps0.le hEps32
  apply gammaInverseAverage_local_affine_of_window_measurable n hn eps hEps0 hEpsHalf
    hLarge (fun s => realGramDeterminantFactor B s * P s) hMeas
    (realGramDeterminantFactor B 1 * P 1) (stochasticCorrectionGammaLinear T q) M hM
  intro s hs
  have h := spectralFactors_signed_product_remainder Finset.univ lam delta eps
    hDelta0 hDelta1 hEps0.le hEps4 (fun i hi => hData.1 i)
    (fun i hi => hData.2.1 i) hSmall' P (stochasticCovarianceLinearCoefficient T q)
    G0 G1 G2 hG0 hG1 hG2 hP0 hP1 hP2 s hs
  change abs (realGramDeterminantFactor B s * P s -
    gammaCubic (realGramDeterminantFactor B 1 * P 1)
      (stochasticCorrectionGammaLinear T q) 0 0 s) <= _
  rw [hDet s hs, hDetOne]
  unfold stochasticCorrectionGammaLinear
  change abs (spectralFactors Finset.univ lam s * P s -
    gammaCubic (spectralFactors Finset.univ lam 1 * P 1)
      (realGramDeterminantFactor B 1 * stochasticCovarianceLinearCoefficient T q +
        spectralFactorJet1 Finset.univ lam 1 * P 1) 0 0 s) <= _
  rw [hDetOne]
  exact h

end PrimeFactorOscillations

/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianSpectralGammaRate
import PrimeFactorOscillations.Helpers.HamiltonianStochasticCorrectionBudget

/-! # Polynomial budget for the discarded covariance affine tail

The complete affine coefficient Delta(1)*a1+Jet1*Psi1 is retained. This
estimate is used only after its full signed Gamma moment has canceled;
it bounds the explicitly discarded tail in the permanent expansion.
-/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations

def hamiltonianCovarianceAffineTailBudget (delta : Real) : Real :=
  (1 + 96 * Real.exp 1 / delta) ^ 3 *
    (80 + 4480 / delta + 140 * hamiltonianSpectralGammaBudget delta)

theorem stochastic_covariance_affine_tail_coefficient_bound {n : Nat}
    (T : Matrix (Fin n) (Fin n) Real) (q a delta : Real)
    (hn : 3 <= n) (hq : (n : Real) * q = 1) (ha : 1 <= a)
    (hRow : forall i, Finset.sum Finset.univ (fun j => T i j) = 1)
    (hCol : forall j, Finset.sum Finset.univ (fun i => T i j) = 1)
    (hNonneg : forall i j, 0 <= T i j) (hUpper : forall i j, T i j <= a * q)
    (hDelta0 : 0 < delta) (hDelta1 : delta <= 1)
    (hNorm : norm (centeredKernel T q) <= 1 - delta) :
    4 * abs (realGramDeterminantFactor (centeredKernel T q) 1 *
        covarianceCorrection
          (resolventCovariance (HSMul.hSMul (1 : Real) (bipartiteLift (centeredKernel T q))))) +
      7 * abs (stochasticCorrectionGammaLinear T q) <=
        realGramDeterminantFactor (centeredKernel T q) 1 * (1 + a) ^ 7 / (n : Real) *
          hamiltonianCovarianceAffineTailBudget delta := by
  classical
  let B := centeredKernel T q
  let lam := realGramEigenvalues B
  let D := realGramDeterminantFactor B 1
  let P := covarianceCorrection
    (resolventCovariance (HSMul.hSMul (1 : Real) (bipartiteLift B)))
  let J := spectralFactorJet1 Finset.univ lam 1
  let K := hamiltonianSpectralGammaBudget delta
  let H := (1 + a) ^ 4
  let C := (1 + 16 * Real.exp 1 * hamiltonianPermanentWindowKappa delta a) ^ 3
  let F := D * C / (n : Real)
  let Q := 80 + 4480 / delta + 140 * K
  have hN : 0 < (n : Real) := Nat.cast_pos.mpr (by omega)
  have ha0 : 0 <= a := by linarith only [ha]
  have hH : 1 <= H := by
    have h := wick_nonnegative_power_le 1 (1 + a) (by norm_num)
      (show (1 : Real) <= 1 + a by linarith only [ha0]) 4
    simpa only [one_pow] using h
  have hH0 : 0 <= H := le_trans (by norm_num) hH
  have hGap : 0 < 1 - hamiltonianWindowScale delta * (1 - delta / 2) := by
    have h := hamiltonian_window_coefficient_gap delta hDelta0
    linarith
  have hKappa0 : 0 <= hamiltonianPermanentWindowKappa delta a := by
    unfold hamiltonianPermanentWindowKappa
    positivity
  have hC0 : 0 <= C := by dsimp only [C]; positivity
  have hK0 : 0 <= K := by
    dsimp only [K, hamiltonianSpectralGammaBudget, hamiltonianSpectralAffineBudget]
    positivity
  have hQ0 : 0 <= Q := by dsimp only [Q]; positivity
  have hData := stochasticGram_spectral_data T q a delta
    (by simpa only [Fintype.card_fin] using hq) hRow hNonneg hUpper hDelta1 hNorm
  have hMass : Finset.sum Finset.univ lam <= a := by
    have h := hData.2.2
    change Finset.sum Finset.univ lam <= a - 1 at h
    linarith only [h]
  have hAtOne : D = spectralFactors Finset.univ lam 1 :=
    realGramDeterminantFactor_eq_spectral_on_strip B delta 0 1 hDelta0 hDelta1
      (by norm_num) (by linarith only [hDelta0]) hNorm (by norm_num)
  have hD : 0 < D := by rw [hAtOne]; exact Real.exp_pos _
  have hF0 : 0 <= F := by dsimp only [F]; positivity
  have hCommon := spectralGamma_common_budget Finset.univ lam delta a hDelta0 hDelta1 ha
    (fun i hi => hData.1 i) (fun i hi => hData.2.1 i) hMass
  rw [<- hAtOne] at hCommon
  have hJ : abs J <= D * H * K := hCommon.2.1
  have hP : abs P <= 20 * C / (n : Real) :=
    stochastic_covarianceCorrection_window_bound T q a delta 1 hn hq ha hRow hCol
      hNonneg hUpper hDelta0 hDelta1 hNorm
      (by simp only [sub_self, abs_zero]; positivity)
  have hA := stochastic_covarianceCorrection_linear_coefficient_bound T q a delta hn
    hq ha hRow hCol hNonneg hUpper hDelta0 hDelta1 hNorm
  have hDP : abs (D * P) <= 20 * F := by
    rw [abs_mul, abs_of_pos hD]
    calc
      _ <= D * (20 * C / (n : Real)) := mul_le_mul_of_nonneg_left hP hD.le
      _ = _ := by dsimp only [F]; ring
  have hL : abs (stochasticCorrectionGammaLinear T q) <=
      D * (640 * C / (delta * (n : Real))) + (D * H * K) * (20 * C / (n : Real)) := by
    have hFirst := mul_le_mul_of_nonneg_left hA hD.le
    have hSecond := mul_le_mul hJ hP (abs_nonneg _) (by positivity : 0 <= D * H * K)
    have hTriangle := abs_add_le
      (D * stochasticCovarianceLinearCoefficient T q) (J * P)
    rw [abs_mul, abs_of_pos hD, abs_mul] at hTriangle
    change abs (D * stochasticCovarianceLinearCoefficient T q + J * P) <= _
    linarith only [hFirst, hSecond, hTriangle]
  have hPad : F * (80 + 4480 / delta) <= F * H * (80 + 4480 / delta) := by
    have h := mul_le_mul_of_nonneg_left hH
      (mul_nonneg hF0 (by positivity : (0 : Real) <= 80 + 4480 / delta))
    nlinarith only [h]
  have hLNormalized : abs (stochasticCorrectionGammaLinear T q) <=
      F * (640 / delta + 20 * H * K) := by
    calc
      _ <= D * (640 * C / (delta * (n : Real))) +
          (D * H * K) * (20 * C / (n : Real)) := hL
      _ = _ := by dsimp only [F]; ring
  have hRaw : 4 * abs (D * P) + 7 * abs (stochasticCorrectionGammaLinear T q) <=
      F * H * Q := by
    calc
      _ <= 4 * (20 * F) + 7 * (F * (640 / delta + 20 * H * K)) :=
        add_le_add
          (mul_le_mul_of_nonneg_left hDP (by norm_num))
          (mul_le_mul_of_nonneg_left hLNormalized (by norm_num))
      _ = F * (80 + 4480 / delta) + 140 * F * H * K := by ring
      _ <= F * H * (80 + 4480 / delta) + 140 * F * H * K :=
        add_le_add hPad (le_refl _)
      _ = _ := by dsimp only [Q]; ring
  have hCPoly := hamiltonianPermanentWindowKappa_polynomial delta a hDelta0 hDelta1 ha
  have hMultiplier : 0 <= D / (n : Real) * H * Q := by positivity
  have hScaled := mul_le_mul_of_nonneg_left hCPoly hMultiplier
  change 4 * abs (D * P) + 7 * abs (stochasticCorrectionGammaLinear T q) <= _
  calc
    _ <= F * H * Q := hRaw
    _ = (D / (n : Real) * H * Q) * C := by dsimp only [F]; ring
    _ <= (D / (n : Real) * H * Q) *
        ((1 + 96 * Real.exp 1 / delta) ^ 3 * (1 + a) ^ 3) := hScaled
    _ = _ := by dsimp only [D, H, Q, K, hamiltonianCovarianceAffineTailBudget]; ring

end PrimeFactorOscillations

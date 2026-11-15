/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianCovarianceGammaTailBudget
import PrimeFactorOscillations.Helpers.HamiltonianPermanentGammaExpansion

/-! # Polynomial rate for the full signed permanent Gamma expansion

The higher-moment and covariance errors have two inverse dimension powers.
The affine coefficient is estimated only in its discarded concentration
tail, after its full signed moment has canceled.
-/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations

def hamiltonianPermanentGammaCoreBudget (delta : Real) : Real :=
  Real.exp 1 * hamiltonianPermanentLocalCorrectionConstant delta +
    hamiltonianCorrectionGammaBudget delta + 64 * hamiltonianSpectralGammaBudget delta

def hamiltonianPermanentGammaCoreTailBudget (delta : Real) : Real :=
  97 * hamiltonianSpectralGammaBudget delta + hamiltonianCovarianceAffineTailBudget delta

theorem stochastic_permanent_core_gamma_remainder_rate {n : Nat}
    (T : Matrix (Fin n) (Fin n) Real) (q a delta eps : Real)
    (hn : 16 <= n) (hq : (n : Real) * q = 1) (ha : 1 <= a)
    (hRow : forall i, Finset.sum Finset.univ (fun j => T i j) = 1)
    (hCol : forall j, Finset.sum Finset.univ (fun i => T i j) = 1)
    (hNonneg : forall i j, 0 <= T i j) (hUpper : forall i j, T i j <= a * q)
    (hDelta0 : 0 < delta) (hDelta1 : delta <= 1)
    (hNorm : norm (centeredKernel T q) <= 1 - delta) :
    stochasticPermanentCoreRemainderBound T q a delta eps <=
      realGramDeterminantFactor (centeredKernel T q) 1 * (1 + a) ^ 24 *
        (hamiltonianPermanentGammaCoreBudget delta / (n : Real) ^ 2 +
          Real.exp (-((n : Real) + 1) * eps ^ 2 / 72) *
            hamiltonianPermanentGammaCoreTailBudget delta) := by
  classical
  let B := centeredKernel T q
  let lam := realGramEigenvalues B
  let D := realGramDeterminantFactor B 1
  let K := hamiltonianSpectralGammaBudget delta
  let G := hamiltonianCorrectionGammaBudget delta
  let V := hamiltonianCovarianceAffineTailBudget delta
  let H := (1 + a) ^ 24
  let tail := Real.exp (-((n : Real) + 1) * eps ^ 2 / 72)
  let C := 4 * abs (D *
      covarianceCorrection (resolventCovariance (HSMul.hSMul (1 : Real) (bipartiteLift B)))) +
    7 * abs (stochasticCorrectionGammaLinear T q)
  have hN : (16 : Real) <= (n : Real) := by exact_mod_cast hn
  have hN0 : 0 < (n : Real) := by linarith only [hN]
  have hA0 : 0 <= a := by linarith only [ha]
  have hBase : 1 <= 1 + a := by linarith only [hA0]
  have hPower : forall k : Nat, k <= 24 -> (1 + a) ^ k <= H := by
    intro k hk
    simpa only [one_pow, one_mul, H] using
      hamiltonian_polynomial_power_bound 1 (1 + a) (1 + a) k 24
        (by norm_num) hBase (by linarith only [hBase]) (by linarith) hk
  have hK0 : 0 <= K := by
    dsimp only [K, hamiltonianSpectralGammaBudget, hamiltonianSpectralAffineBudget]
    positivity
  have hG0 : 0 <= G := by
    dsimp only [G, hamiltonianCorrectionGammaBudget, hamiltonianCorrectionProductBudget,
      hamiltonianSpectralIncrementBudget, hamiltonianSpectralAffineBudget]
    positivity
  have hV0 : 0 <= V := by
    dsimp only [V, hamiltonianCovarianceAffineTailBudget, hamiltonianSpectralGammaBudget,
      hamiltonianSpectralAffineBudget]
    positivity
  have hTail0 : 0 <= tail := (Real.exp_pos _).le
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
  have hHigher := spectralGamma_higher_moment_remainder Finset.univ lam n hn delta a
    hDelta0 hDelta1 ha (fun i hi => hData.1 i) (fun i hi => hData.2.1 i) hMass
  rw [gammaInverseAverage_fourth_uniform n (by omega),
    gammaInverseAverage_third_uniform n (by omega), <- hAtOne] at hHigher
  have hCubic : (spectralFactorJet3 Finset.univ lam 1 / 6) *
      (4 / (((n : Real) - 1) * ((n : Real) - 2))) =
        4 * (spectralFactorJet3 Finset.univ lam 1 / 6) /
          (((n : Real) - 1) * ((n : Real) - 2)) := by ring
  rw [hCubic] at hHigher
  have hHigherPad :
      64 * D * (1 + a) ^ 4 * K / (n : Real) ^ 2 <=
        64 * D * H * K / (n : Real) ^ 2 := by
    apply div_le_div_of_nonneg_right _ (sq_nonneg _)
    have h := mul_le_mul_of_nonneg_left (hPower 4 (by omega))
      (by positivity : 0 <= 64 * D * K)
    nlinarith only [h]
  have hMoment := le_trans hHigher hHigherPad
  have hCovBase : G * D * (1 + a) ^ 7 / (n : Real) ^ 2 <=
      G * D * H / (n : Real) ^ 2 :=
    div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hPower 7 (by omega))
        (mul_nonneg hG0 hD.le)) (sq_nonneg _)
  have hSpec := spectralGamma_tail_coefficient_bound Finset.univ lam delta a
    hDelta0 hDelta1 ha (fun i hi => hData.1 i) (fun i hi => hData.2.1 i) hMass
  rw [<- hAtOne] at hSpec
  have hSpecPad : 97 * D * (1 + a) ^ 4 * K <= 97 * D * H * K := by
    have h := mul_le_mul_of_nonneg_left (hPower 4 (by omega))
      (by positivity : 0 <= 97 * D * K)
    nlinarith only [h]
  have hCov := stochastic_covariance_affine_tail_coefficient_bound T q a delta
    (by omega) hq ha hRow hCol hNonneg hUpper hDelta0 hDelta1 hNorm
  change C <= D * (1 + a) ^ 7 / (n : Real) * V at hCov
  have hCovPad : D * (1 + a) ^ 7 / (n : Real) * V <= D * H * V := by
    apply mul_le_mul_of_nonneg_right _ hV0
    apply le_of_mul_le_mul_right (a := (n : Real)) _ hN0
    calc
      _ = D * (1 + a) ^ 7 := by field_simp [ne_of_gt hN0]
      _ <= D * H := mul_le_mul_of_nonneg_left (hPower 7 (by omega)) hD.le
      _ <= _ := by
        have h := mul_le_mul_of_nonneg_left
          (show (1 : Real) <= (n : Real) by linarith only [hN])
          (mul_nonneg hD.le (by dsimp only [H]; positivity : 0 <= H))
        simpa only [mul_one] using h
  have hTail : tail * (spectralTaylorTailCoefficient Finset.univ lam + C) <=
      tail * (D * H * (97 * K + V)) := by
    apply mul_le_mul_of_nonneg_left _ hTail0
    have h1 := le_trans hSpec hSpecPad
    have h2 := le_trans hCov hCovPad
    nlinarith only [h1, h2]
  change _ <= D * H *
    (hamiltonianPermanentGammaCoreBudget delta / (n : Real) ^ 2 +
      tail * hamiltonianPermanentGammaCoreTailBudget delta)
  calc
    _ = Real.exp 1 * D *
          (hamiltonianPermanentLocalCorrectionConstant delta * H / (n : Real) ^ 2) +
        (spectralTaylorRemainderBound Finset.univ lam delta *
            (3 * ((n : Real) + 6) /
              (((n : Real) - 1) * ((n : Real) - 2) * ((n : Real) - 3))) +
          abs (4 * (spectralFactorJet3 Finset.univ lam 1 / 6) /
            (((n : Real) - 1) * ((n : Real) - 2)))) +
        G * D * (1 + a) ^ 7 / (n : Real) ^ 2 +
        tail * (spectralTaylorTailCoefficient Finset.univ lam + C) := by
          dsimp only [stochasticPermanentCoreRemainderBound, B, lam, D, G, H, tail, C]
          ring
    _ <= Real.exp 1 * D *
          (hamiltonianPermanentLocalCorrectionConstant delta * H / (n : Real) ^ 2) +
        64 * D * H * K / (n : Real) ^ 2 +
        G * D * H / (n : Real) ^ 2 +
        tail * (D * H * (97 * K + V)) := by
          exact add_le_add (add_le_add (add_le_add (le_refl _) hMoment) hCovBase) hTail
    _ = _ := by
      dsimp only [hamiltonianPermanentGammaCoreBudget,
        hamiltonianPermanentGammaCoreTailBudget, K, G, V]
      ring

end PrimeFactorOscillations

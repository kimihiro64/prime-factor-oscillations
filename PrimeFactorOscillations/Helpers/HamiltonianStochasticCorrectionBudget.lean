/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianGammaCorrectionBudget

/-! # Two-power covariance Gamma remainder for actual stochastic kernels

The complete determinant-covariance product budget has one inverse dimension.
Its exact second Gamma moment supplies the second inverse dimension. Every
constant depends only on the spectral gap, and the entry-cap degree is seven.
-/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations

def hamiltonianCorrectionProductBudget (delta : Real) : Real :=
  20 * hamiltonianSpectralAffineBudget delta +
    640 * hamiltonianSpectralIncrementBudget delta / delta +
      40960 * Real.exp 1 / delta ^ 2

def hamiltonianCorrectionGammaBudget (delta : Real) : Real :=
  2 * hamiltonianCorrectionProductBudget delta * (1 + 96 * Real.exp 1 / delta) ^ 3

theorem hamiltonianPermanentWindowKappa_polynomial (delta a : Real)
    (hDelta0 : 0 < delta) (hDelta1 : delta <= 1) (ha : 1 <= a) :
    (1 + 16 * Real.exp 1 * hamiltonianPermanentWindowKappa delta a) ^ 3 <=
      (1 + 96 * Real.exp 1 / delta) ^ 3 * (1 + a) ^ 3 := by
  have hGap : 0 < 1 - hamiltonianWindowScale delta * (1 - delta / 2) := by
    have h := hamiltonian_window_coefficient_gap delta hDelta0
    linarith
  have ha0 : 0 <= a := by linarith only [ha]
  have hKappa0 : 0 <= hamiltonianPermanentWindowKappa delta a := by
    unfold hamiltonianPermanentWindowKappa
    positivity
  have hKappa := hamiltonian_window_coefficient_kappa_bound delta a hDelta0 hDelta1 ha0
  change hamiltonianPermanentWindowKappa delta a <= 6 * a / delta at hKappa
  have hLinear : 16 * Real.exp 1 * hamiltonianPermanentWindowKappa delta a <=
      (96 * Real.exp 1 / delta) * a := by
    have h := mul_le_mul_of_nonneg_left hKappa
      (mul_nonneg (by norm_num : (0 : Real) <= 16) (Real.exp_pos 1).le)
    convert h using 1 <;> ring
  have hC0 : 0 <= 96 * Real.exp 1 / delta := by positivity
  have hBase : 1 + 16 * Real.exp 1 * hamiltonianPermanentWindowKappa delta a <=
      (1 + 96 * Real.exp 1 / delta) * (1 + a) := by
    nlinarith only [hLinear, hC0, ha0]
  calc
    _ <= ((1 + 96 * Real.exp 1 / delta) * (1 + a)) ^ 3 :=
      wick_nonnegative_power_le _ _ (by positivity) hBase 3
    _ = _ := by rw [mul_pow]

theorem stochasticCorrectionGammaRemainderBound_polynomial {n : Nat}
    (T : Matrix (Fin n) (Fin n) Real) (q a delta eps : Real)
    (hn : 0 < n) (hq : (n : Real) * q = 1) (ha : 1 <= a)
    (hRow : forall i, Finset.sum Finset.univ (fun j => T i j) = 1)
    (hNonneg : forall i j, 0 <= T i j) (hUpper : forall i j, T i j <= a * q)
    (hDelta0 : 0 < delta) (hDelta1 : delta <= 1)
    (hNorm : norm (centeredKernel T q) <= 1 - delta)
    (hEps0 : 0 <= eps) (hEps1 : eps <= 1) :
    stochasticCorrectionGammaRemainderBound T q a delta eps <=
      realGramDeterminantFactor (centeredKernel T q) 1 * (1 + a) ^ 7 /
        (n : Real) *
          (hamiltonianCorrectionProductBudget delta *
            (1 + 96 * Real.exp 1 / delta) ^ 3) := by
  classical
  let B := centeredKernel T q
  let lam := realGramEigenvalues B
  let D := spectralFactors Finset.univ lam 1
  let C := (1 + 16 * Real.exp 1 * hamiltonianPermanentWindowKappa delta a) ^ 3
  have hN : 0 < (n : Real) := Nat.cast_pos.mpr hn
  have hGap : 0 < 1 - hamiltonianWindowScale delta * (1 - delta / 2) := by
    have h := hamiltonian_window_coefficient_gap delta hDelta0
    linarith
  have hKappa0 : 0 <= hamiltonianPermanentWindowKappa delta a := by
    unfold hamiltonianPermanentWindowKappa
    positivity
  have hC : 0 <= C := by dsimp only [C]; positivity
  have hD : 0 < D := Real.exp_pos _
  have hA0 : 0 <= a := by linarith only [ha]
  have hBudget0 : 0 <= hamiltonianCorrectionProductBudget delta := by
    unfold hamiltonianCorrectionProductBudget hamiltonianSpectralIncrementBudget
      hamiltonianSpectralAffineBudget
    positivity
  have hData := stochasticGram_spectral_data T q a delta
    (by simpa only [Fintype.card_fin] using hq) hRow hNonneg hUpper hDelta1 hNorm
  have hMass : Finset.sum Finset.univ lam <= a := by
    have h := hData.2.2
    change Finset.sum Finset.univ lam <= a - 1 at h
    linarith only [h]
  have hR := spectralCorrectionProductRemainderBound_polynomial Finset.univ lam delta eps a
    (20 * C / (n : Real)) (640 * C / (delta * (n : Real)))
      (40960 * C / (delta ^ 2 * (n : Real)))
    hDelta0 hDelta1 ha hEps0 hEps1 (fun i hi => hData.1 i)
      (fun i hi => hData.2.1 i) hMass (by positivity) (by positivity) (by positivity)
  have hSimplified : stochasticCorrectionGammaRemainderBound T q a delta eps <=
      D * (1 + a) ^ 4 * C / (n : Real) * hamiltonianCorrectionProductBudget delta := by
    calc
      _ <= D * (1 + a) ^ 4 *
          (hamiltonianSpectralAffineBudget delta * (20 * C / (n : Real)) +
            hamiltonianSpectralIncrementBudget delta * (640 * C / (delta * (n : Real))) +
              Real.exp 1 * (40960 * C / (delta ^ 2 * (n : Real)))) := hR
      _ = _ := by unfold hamiltonianCorrectionProductBudget; ring
  have hCPoly := hamiltonianPermanentWindowKappa_polynomial delta a hDelta0 hDelta1 ha
  have hMultiplier : 0 <= D * (1 + a) ^ 4 / (n : Real) *
      hamiltonianCorrectionProductBudget delta := by positivity
  have hScaled := mul_le_mul_of_nonneg_left hCPoly hMultiplier
  have hDet : realGramDeterminantFactor B 1 = D :=
    realGramDeterminantFactor_eq_spectral_on_strip B delta 0 1 hDelta0 hDelta1
      (by norm_num) (by linarith only [hDelta0]) hNorm (by norm_num)
  rw [hDet]
  calc
    _ <= D * (1 + a) ^ 4 * C / (n : Real) *
        hamiltonianCorrectionProductBudget delta := hSimplified
    _ = (D * (1 + a) ^ 4 / (n : Real) *
        hamiltonianCorrectionProductBudget delta) * C := by ring
    _ <= (D * (1 + a) ^ 4 / (n : Real) *
        hamiltonianCorrectionProductBudget delta) *
          ((1 + 96 * Real.exp 1 / delta) ^ 3 * (1 + a) ^ 3) := hScaled
    _ = _ := by ring

theorem stochasticCorrectionGamma_second_moment_bound {n : Nat}
    (T : Matrix (Fin n) (Fin n) Real) (q a delta eps : Real)
    (hn : 2 <= n) (hq : (n : Real) * q = 1) (ha : 1 <= a)
    (hRow : forall i, Finset.sum Finset.univ (fun j => T i j) = 1)
    (hNonneg : forall i j, 0 <= T i j) (hUpper : forall i j, T i j <= a * q)
    (hDelta0 : 0 < delta) (hDelta1 : delta <= 1)
    (hNorm : norm (centeredKernel T q) <= 1 - delta)
    (hEps0 : 0 <= eps) (hEps1 : eps <= 1) :
    stochasticCorrectionGammaRemainderBound T q a delta eps *
        (1 / ((n : Real) - 1)) <=
      hamiltonianCorrectionGammaBudget delta *
        realGramDeterminantFactor (centeredKernel T q) 1 * (1 + a) ^ 7 /
          (n : Real) ^ 2 := by
  let D := realGramDeterminantFactor (centeredKernel T q) 1
  let Q := hamiltonianCorrectionProductBudget delta *
    (1 + 96 * Real.exp 1 / delta) ^ 3
  have hN : (2 : Real) <= (n : Real) := by exact_mod_cast hn
  have hN0 : 0 < (n : Real) := by linarith only [hN]
  have hNm1 : 0 < (n : Real) - 1 := by linarith only [hN]
  have hInv : 1 / ((n : Real) - 1) <= 2 / (n : Real) := by
    calc
      _ = (n : Real) / ((n : Real) * ((n : Real) - 1)) := by
        field_simp [ne_of_gt hN0, ne_of_gt hNm1]
      _ <= (2 * ((n : Real) - 1)) / ((n : Real) * ((n : Real) - 1)) :=
        div_le_div_of_nonneg_right (by linarith only [hN]) (mul_nonneg hN0.le hNm1.le)
      _ = _ := by field_simp [ne_of_gt hN0, ne_of_gt hNm1]
  have hR := stochasticCorrectionGammaRemainderBound_polynomial T q a delta eps
    (by omega) hq ha hRow hNonneg hUpper hDelta0 hDelta1 hNorm hEps0 hEps1
  have hD : 0 < D := by
    have h := realGramDeterminantFactor_eq_spectral_on_strip
      (centeredKernel T q) delta 0 1 hDelta0 hDelta1
      (by norm_num) (by linarith only [hDelta0]) hNorm (by norm_num)
    dsimp only [D]
    rw [h]
    exact Real.exp_pos _
  have hQ : 0 <= Q := by
    dsimp only [Q, hamiltonianCorrectionProductBudget, hamiltonianSpectralAffineBudget,
      hamiltonianSpectralIncrementBudget]
    positivity
  have hA0 : 0 <= a := by linarith only [ha]
  have hUpper0 : 0 <= D * (1 + a) ^ 7 / (n : Real) * Q := by positivity
  calc
    _ <= (D * (1 + a) ^ 7 / (n : Real) * Q) * (1 / ((n : Real) - 1)) :=
      mul_le_mul_of_nonneg_right hR (div_nonneg (by norm_num) hNm1.le)
    _ <= (D * (1 + a) ^ 7 / (n : Real) * Q) * (2 / (n : Real)) :=
      mul_le_mul_of_nonneg_left hInv hUpper0
    _ = _ := by dsimp only [D, Q, hamiltonianCorrectionGammaBudget]; ring

end PrimeFactorOscillations

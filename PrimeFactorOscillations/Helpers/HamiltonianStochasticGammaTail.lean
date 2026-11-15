/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianGaussianShiftedGammaTail

/-! # Explicit stochastic constants in the full Gaussian-Gamma tail

The two actual Gaussian moments are bounded at 1 and 1+delta/4.
Their costs are carried through the same outside-window integral.
-/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations

private theorem positive_div_le_of_mul_le (a b c : Real) (hb : 0 < b)
    (h : a <= c * b) : a / b <= c := by
  by_contra hNot
  have hStrict := mul_lt_mul_of_pos_right (lt_of_not_ge hNot) hb
  have hCancel : (a / b) * b = a := by field_simp
  rw [hCancel] at hStrict
  linarith

theorem gaussianTail_tilt_gap (delta : Real) (hDelta : 0 < delta) :
    0 < 1 - (1 + delta / 4) * (1 - delta) := by
  nlinarith [sq_nonneg delta]

theorem gaussianTail_tilt_budget (delta : Real) (hDelta : 0 < delta) :
    2 * (1 + delta / 4) / (1 - (1 + delta / 4) * (1 - delta)) <=
      10 / (3 * delta) := by
  apply positive_div_le_of_mul_le _ _ _ (gaussianTail_tilt_gap delta hDelta)
  have hIdentity :
      10 / (3 * delta) * (1 - (1 + delta / 4) * (1 - delta)) =
        5 / 2 + 5 * delta / 6 := by
    field_simp [ne_of_gt hDelta]
    ring
  rw [hIdentity]
  linarith

theorem gaussianTail_unit_budget (delta : Real) (hDelta : 0 < delta) :
    2 * (1 : Real) / (1 - 1 * (1 - delta)) <= 10 / (3 * delta) := by
  have hDen : 1 - (1 : Real) * (1 - delta) = delta := by ring
  rw [hDen, mul_one]
  apply positive_div_le_of_mul_le _ _ _ hDelta
  have hIdentity : 10 / (3 * delta) * delta = (10 : Real) / 3 := by
    field_simp [ne_of_gt hDelta]
  rw [hIdentity]
  norm_num

theorem stochasticGaussianGammaOutsideAverage_bound {n : Nat}
    (T : Matrix (Fin n) (Fin n) Real) (q a delta : Real)
    (hq : (n : Real) * q = 1) (ha : 1 <= a)
    (hRow : forall i, Finset.sum Finset.univ (fun j => T i j) = 1)
    (hNonneg : forall i j, 0 <= T i j) (hUpper : forall i j, T i j <= a * q)
    (hNorm : norm (centeredKernel T q) <= 1 - delta)
    (hDelta0 : 0 < delta) (hDelta1 : delta <= 1)
    (hN : 8 <= (n : Real) * delta) :
    realGaussianGammaOutsideAverage (bipartiteLift (centeredKernel T q))
        (bipartiteLift_hermitian (centeredKernel T q)) n delta <=
      3 * Real.exp (-(n : Real) * delta ^ 2 / 2304 +
        10 / (3 * delta) * Real.sqrt ((n : Real) * (a - 1))) := by
  let M := bipartiteLift (centeredKernel T q)
  let hM := bipartiteLift_hermitian (centeredKernel T q)
  let tau := 1 + delta / 4
  let X := Real.sqrt ((n : Real) * (a - 1))
  let K := Real.exp (10 / (3 * delta) * X)
  have hNormM : norm M <= 1 - delta :=
    le_trans (bipartiteLift_l2_norm_le _) hNorm
  have hGap : 0 < 1 - (1 - delta) := by linarith
  have hTau : 1 <= tau := by dsimp only [tau]; linarith
  have hTauGap : 0 < 1 - tau * (1 - delta) :=
    gaussianTail_tilt_gap delta hDelta0
  have hOne := stochasticGaussianQuadraticMGF_bound T q a 1 (1 - delta)
    (by simpa only [Fintype.card_fin] using hq) ha hRow hNonneg hUpper
    zero_le_one hNorm (by simpa only [one_mul] using hGap)
  have hTilt := stochasticGaussianQuadraticMGF_bound T q a tau (1 - delta)
    (by simpa only [Fintype.card_fin] using hq) ha hRow hNonneg hUpper
    (le_trans zero_le_one hTau) hNorm hTauGap
  have hMGF1 : realSpectralGaussianQuadraticMGF M hM 1 <= K := by
    apply le_trans hOne
    apply Real.exp_le_exp.mpr
    simpa only [Fintype.card_fin] using
      mul_le_mul_of_nonneg_right (gaussianTail_unit_budget delta hDelta0)
        (Real.sqrt_nonneg ((n : Real) * (a - 1)))
  have hMGFTau : realSpectralGaussianQuadraticMGF M hM tau <= K := by
    apply le_trans hTilt
    apply Real.exp_le_exp.mpr
    simpa only [Fintype.card_fin] using
      mul_le_mul_of_nonneg_right (gaussianTail_tilt_budget delta hDelta0)
        (Real.sqrt_nonneg ((n : Real) * (a - 1)))
  have hLow : Real.exp (-((n : Real) + 1) * delta ^ 2 / 2304) <=
      Real.exp (-(n : Real) * delta ^ 2 / 2304) := by
    apply Real.exp_le_exp.mpr
    nlinarith [sq_nonneg delta]
  have hHigh : Real.exp (-(tau - 1) * (delta * (n : Real) / 16)) <=
      Real.exp (-(n : Real) * delta ^ 2 / 2304) := by
    apply Real.exp_le_exp.mpr
    have h0 := mul_nonneg (Nat.cast_nonneg n : 0 <= (n : Real)) (sq_nonneg delta)
    dsimp only [tau]
    nlinarith
  have hKernel := realGaussianGammaOutsideAverage_two_tilts M hM n delta tau (1 - delta)
    hDelta0 hDelta1 hN hTau hNormM hGap hTauGap
  have hK : 0 <= K := (Real.exp_pos _).le
  calc
    _ <= (2 * Real.exp (-((n : Real) + 1) * delta ^ 2 / 2304)) *
          realSpectralGaussianQuadraticMGF M hM 1 +
        Real.exp (-(tau - 1) * (delta * (n : Real) / 16)) *
          realSpectralGaussianQuadraticMGF M hM tau := hKernel
    _ <= (2 * Real.exp (-((n : Real) + 1) * delta ^ 2 / 2304)) * K +
        Real.exp (-(tau - 1) * (delta * (n : Real) / 16)) * K :=
      add_le_add
        (mul_le_mul_of_nonneg_left hMGF1 (mul_nonneg (by norm_num) (Real.exp_pos _).le))
        (mul_le_mul_of_nonneg_left hMGFTau (Real.exp_pos _).le)
    _ <= (2 * Real.exp (-(n : Real) * delta ^ 2 / 2304)) * K +
        Real.exp (-(n : Real) * delta ^ 2 / 2304) * K :=
      add_le_add
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hLow (by norm_num)) hK)
        (mul_le_mul_of_nonneg_right hHigh hK)
    _ = _ := by
      dsimp only [K, X]
      rw [Real.exp_add]
      ring

end PrimeFactorOscillations

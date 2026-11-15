/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianGammaRootWindow
import PrimeFactorOscillations.Helpers.HamiltonianPermanentGammaRate

/-! # Uniform signed permanent asymptotics for polylogarithmic entry caps

One common root-scale window controls the full rook integral. Polynomial
exponential bounds absorb the core, annular and outer tails into the
second-order remainder. Constants depend only on the spectral gap.
-/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations

def hamiltonianGammaRootTailConstant : Real := 24 * 72 ^ 4

def hamiltonianGammaOuterTailConstant (delta : Real) : Real :=
  6 * 73728 ^ 3 / delta ^ 6

def hamiltonianPermanentUniformBudget (delta : Real) : Real :=
  hamiltonianPermanentGammaCoreBudget delta +
    hamiltonianGammaRootTailConstant * hamiltonianPermanentGammaCoreTailBudget delta +
      2 * hamiltonianGammaRootTailConstant + 3 * hamiltonianGammaOuterTailConstant delta

theorem hamiltonian_gamma_root_tail_decay (n : Nat) (r : Real)
    (hn : 1 <= n) (hr : 0 < r) (hr8 : r ^ 8 = (n : Real)) :
    Real.exp (-(r ^ 6) / 72) <= hamiltonianGammaRootTailConstant / (n : Real) ^ 2 := by
  let u := r ^ 6 / 72
  let c := hamiltonianGammaRootTailConstant
  have hN : (1 : Real) <= (n : Real) := by exact_mod_cast hn
  have hN0 : 0 < (n : Real) := by linarith only [hN]
  have hu : 0 <= u := by dsimp only [u]; positivity
  have hSeries : u ^ 4 / (24 : Real) <= Real.exp u := by
    simpa only [show (Nat.factorial 4 : Real) = 24 by norm_num] using
      Real.pow_div_factorial_le_exp u hu 4
  have hProduct := mul_le_mul_of_nonneg_right hSeries (Real.exp_pos (-u)).le
  rw [<- Real.exp_add, add_neg_cancel, Real.exp_zero] at hProduct
  have hc : 0 <= c := by dsimp only [c, hamiltonianGammaRootTailConstant]; positivity
  have hScalar : Real.exp (-u) * (n : Real) ^ 3 <= c := by
    calc
      _ = c * ((u ^ 4 / 24) * Real.exp (-u)) := by
        rw [<- hr8]
        dsimp only [c, u, hamiltonianGammaRootTailConstant]
        ring
      _ <= c * 1 := mul_le_mul_of_nonneg_left hProduct hc
      _ = _ := mul_one _
  have hNPower : (n : Real) ^ 2 <= (n : Real) ^ 3 := by
    have h := mul_le_mul_of_nonneg_right hN (sq_nonneg (n : Real))
    nlinarith only [h]
  have hFinal : Real.exp (-u) * (n : Real) ^ 2 <=
      (c / (n : Real) ^ 2) * (n : Real) ^ 2 := by
    calc
      _ <= Real.exp (-u) * (n : Real) ^ 3 :=
        mul_le_mul_of_nonneg_left hNPower (Real.exp_pos (-u)).le
      _ <= c := hScalar
      _ = _ := by field_simp [ne_of_gt hN0]
  have h := le_of_mul_le_mul_right hFinal (pow_pos hN0 2)
  change Real.exp (-(r ^ 6) / 72) <= c / (n : Real) ^ 2
  convert h using 1 <;> dsimp only [u] <;> congr 1 <;> ring

theorem hamiltonian_gamma_outer_tail_decay (n : Nat) (delta : Real)
    (hn : 1 <= n) (hDelta : 0 < delta) :
    Real.exp (-(n : Real) * delta ^ 2 / 73728) <=
      hamiltonianGammaOuterTailConstant delta / (n : Real) ^ 2 := by
  let u := (n : Real) * delta ^ 2 / 73728
  let c := hamiltonianGammaOuterTailConstant delta
  have hN : (1 : Real) <= (n : Real) := by exact_mod_cast hn
  have hN0 : 0 < (n : Real) := by linarith only [hN]
  have hu : 0 <= u := by dsimp only [u]; positivity
  have hSeries : u ^ 3 / (6 : Real) <= Real.exp u := by
    simpa only [show (Nat.factorial 3 : Real) = 6 by norm_num] using
      Real.pow_div_factorial_le_exp u hu 3
  have hProduct := mul_le_mul_of_nonneg_right hSeries (Real.exp_pos (-u)).le
  rw [<- Real.exp_add, add_neg_cancel, Real.exp_zero] at hProduct
  have hc : 0 <= c := by dsimp only [c, hamiltonianGammaOuterTailConstant]; positivity
  have hScalar : Real.exp (-u) * (n : Real) ^ 3 <= c := by
    calc
      _ = c * ((u ^ 3 / 6) * Real.exp (-u)) := by
        dsimp only [c, u, hamiltonianGammaOuterTailConstant]
        field_simp [ne_of_gt hDelta] <;> ring
      _ <= c * 1 := mul_le_mul_of_nonneg_left hProduct hc
      _ = _ := mul_one _
  have hNPower : (n : Real) ^ 2 <= (n : Real) ^ 3 := by
    have h := mul_le_mul_of_nonneg_right hN (sq_nonneg (n : Real))
    nlinarith only [h]
  have hFinal : Real.exp (-u) * (n : Real) ^ 2 <=
      (c / (n : Real) ^ 2) * (n : Real) ^ 2 := by
    calc
      _ <= Real.exp (-u) * (n : Real) ^ 3 :=
        mul_le_mul_of_nonneg_left hNPower (Real.exp_pos (-u)).le
      _ <= c := hScalar
      _ = _ := by field_simp [ne_of_gt hN0]
  have h := le_of_mul_le_mul_right hFinal (pow_pos hN0 2)
  change Real.exp (-(n : Real) * delta ^ 2 / 73728) <= c / (n : Real) ^ 2
  convert h using 1 <;> dsimp only [u] <;> congr 1 <;> ring

theorem stochasticGramDeterminantFactor_one_le {n : Nat}
    (T : Matrix (Fin n) (Fin n) Real) (q a delta : Real)
    (hq : (n : Real) * q = 1)
    (hRow : forall i, Finset.sum Finset.univ (fun j => T i j) = 1)
    (hNonneg : forall i j, 0 <= T i j) (hUpper : forall i j, T i j <= a * q)
    (hDelta0 : 0 < delta) (hDelta1 : delta <= 1)
    (hNorm : norm (centeredKernel T q) <= 1 - delta) :
    1 <= realGramDeterminantFactor (centeredKernel T q) 1 := by
  classical
  let B := centeredKernel T q
  let lam := realGramEigenvalues B
  have hData := stochasticGram_spectral_data T q a delta
    (by simpa only [Fintype.card_fin] using hq) hRow hNonneg hUpper hDelta1 hNorm
  have hAtOne := realGramDeterminantFactor_eq_spectral_on_strip B delta 0 1
    hDelta0 hDelta1 (by norm_num) (by linarith only [hDelta0]) hNorm (by norm_num)
  rw [hAtOne]
  have hLog : 0 <= spectralLogFactors Finset.univ lam 1 := by
    apply Finset.sum_nonneg
    intro i hi
    have hStrip := spectralFactor_strip delta 0 (lam i) 1 hDelta0 hDelta1
      (by norm_num) (by linarith only [hDelta0]) (hData.1 i) (hData.2.1 i) (by norm_num)
    have hDen : 0 <= 1 - lam i := by
      have h := hStrip.2.2.2
      norm_num only [one_pow, one_mul] at h
      linarith only [h, hDelta0]
    have hUpperLog : 1 - lam i <= 1 := by linarith only [hData.1 i]
    have h := Real.log_nonpos hDen hUpperLog
    dsimp only [spectralCoordinate0]
    norm_num only [one_pow, one_mul]
    linarith only [h]
  change 1 <= Real.exp (spectralLogFactors Finset.univ lam 1)
  calc
    _ = Real.exp 0 := Real.exp_zero.symm
    _ <= _ := Real.exp_le_exp.mpr hLog


theorem stochastic_permanent_gamma_error_uniform {n : Nat}
    (T : Matrix (Fin n) (Fin n) Real) (q a delta : Real)
    (hn : 16 <= n) (hq : (n : Real) * q = 1) (ha : 1 <= a)
    (hRow : forall i, Finset.sum Finset.univ (fun j => T i j) = 1)
    (hCol : forall j, Finset.sum Finset.univ (fun i => T i j) = 1)
    (hNonneg : forall i j, 0 <= T i j) (hUpper : forall i j, T i j <= a * q)
    (hDelta0 : 0 < delta) (hDelta1 : delta <= 1)
    (hNorm : norm (centeredKernel T q) <= 1 - delta)
    (hWindow : HamiltonianGammaRootWindowData n a delta) :
    stochasticPermanentGammaErrorBound T q a delta (hamiltonianGammaCoreWidth (n : Real)) <=
      realGramDeterminantFactor (centeredKernel T q) 1 * (1 + a) ^ 24 *
        hamiltonianPermanentUniformBudget delta / (n : Real) ^ 2 := by
  let D := realGramDeterminantFactor (centeredKernel T q) 1
  let H := (1 + a) ^ 24
  let eps := hamiltonianGammaCoreWidth (n : Real)
  let c := hamiltonianGammaRootTailConstant
  let d := hamiltonianGammaOuterTailConstant delta
  have hN : (16 : Real) <= (n : Real) := by exact_mod_cast hn
  have hN0 : 0 < (n : Real) := by linarith only [hN]
  have hA0 : 0 <= a := by linarith only [ha]
  have hc : 0 <= c := by dsimp only [c, hamiltonianGammaRootTailConstant]; positivity
  have hd : 0 <= d := by dsimp only [d, hamiltonianGammaOuterTailConstant]; positivity
  have hD : 1 <= D :=
    stochasticGramDeterminantFactor_one_le T q a delta hq hRow hNonneg hUpper
      hDelta0 hDelta1 hNorm
  have hD0 : 0 <= D := le_trans (by norm_num) hD
  have hH : 1 <= H := by
    have h := wick_nonnegative_power_le 1 (1 + a) (by norm_num)
      (show (1 : Real) <= 1 + a by linarith only [hA0]) 24
    simpa only [one_pow] using h
  have hH0 : 0 <= H := le_trans (by norm_num) hH
  have hDH : 1 <= D * H := by
    calc
      _ <= D := hD
      _ <= D * H := by simpa only [mul_one] using mul_le_mul_of_nonneg_left hH hD0
  have hCT0 : 0 <= hamiltonianPermanentGammaCoreTailBudget delta := by
    unfold hamiltonianPermanentGammaCoreTailBudget hamiltonianCovarianceAffineTailBudget
      hamiltonianSpectralGammaBudget hamiltonianSpectralAffineBudget
    positivity
  have hRootDecay := hamiltonian_gamma_root_tail_decay n
    (hamiltonianGammaCoreRoot (n : Real)) (by omega) hWindow.root_pos hWindow.root_eighth
  have hOuterDecay := hamiltonian_gamma_outer_tail_decay n delta (by omega) hDelta0
  have hCoreDecay : Real.exp (-((n : Real) + 1) * eps ^ 2 / 72) <= c / (n : Real) ^ 2 :=
    le_trans (Real.exp_le_exp.mpr hWindow.core_exponent) hRootDecay
  have hAnnularDecay :
      Real.exp (6 * a * Real.sqrt (n : Real) / delta -
        ((n : Real) + 1) * eps ^ 2 / 36) <= c / (n : Real) ^ 2 :=
    le_trans (Real.exp_le_exp.mpr hWindow.annular_exponent) hRootDecay
  have hFarDecay :
      Real.exp (-(n : Real) * delta ^ 2 / 36864 +
        40 / (3 * delta) * Real.sqrt ((n : Real) * (a - 1))) <= d / (n : Real) ^ 2 :=
    le_trans (Real.exp_le_exp.mpr hWindow.outer_exponent) hOuterDecay
  have hCore := stochastic_permanent_core_gamma_remainder_rate T q a delta eps
    hn hq ha hRow hCol hNonneg hUpper hDelta0 hDelta1 hNorm
  have hCorePoly : stochasticPermanentCoreRemainderBound T q a delta eps <=
      D * H * ((hamiltonianPermanentGammaCoreBudget delta +
        c * hamiltonianPermanentGammaCoreTailBudget delta) / (n : Real) ^ 2) := by
    calc
      _ <= D * H * (hamiltonianPermanentGammaCoreBudget delta / (n : Real) ^ 2 +
          Real.exp (-((n : Real) + 1) * eps ^ 2 / 72) *
            hamiltonianPermanentGammaCoreTailBudget delta) := hCore
      _ <= D * H * (hamiltonianPermanentGammaCoreBudget delta / (n : Real) ^ 2 +
          (c / (n : Real) ^ 2) * hamiltonianPermanentGammaCoreTailBudget delta) :=
        mul_le_mul_of_nonneg_left
          (add_le_add (le_refl _) (mul_le_mul_of_nonneg_right hCoreDecay hCT0))
          (mul_nonneg hD0 hH0)
      _ = _ := by ring
  have hRookTail : hamiltonianRookGammaTailBudget n a delta eps <=
      (2 * c + 3 * d) / (n : Real) ^ 2 := by
    unfold hamiltonianRookGammaTailBudget
    calc
      _ <= 2 * (c / (n : Real) ^ 2) + 3 * (d / (n : Real) ^ 2) :=
        add_le_add
          (mul_le_mul_of_nonneg_left hAnnularDecay (by norm_num))
          (mul_le_mul_of_nonneg_left hFarDecay (by norm_num))
      _ = _ := by ring
  have hTailScale : (2 * c + 3 * d) / (n : Real) ^ 2 <=
      D * H * ((2 * c + 3 * d) / (n : Real) ^ 2) := by
    have h := mul_le_mul_of_nonneg_right hDH
      (by positivity : 0 <= (2 * c + 3 * d) / (n : Real) ^ 2)
    simpa only [one_mul] using h
  change _ <= D * H * hamiltonianPermanentUniformBudget delta / (n : Real) ^ 2
  calc
    _ = stochasticPermanentCoreRemainderBound T q a delta eps +
        hamiltonianRookGammaTailBudget n a delta eps := rfl
    _ <= D * H * ((hamiltonianPermanentGammaCoreBudget delta +
          c * hamiltonianPermanentGammaCoreTailBudget delta) / (n : Real) ^ 2) +
        D * H * ((2 * c + 3 * d) / (n : Real) ^ 2) :=
      add_le_add hCorePoly (le_trans hRookTail hTailScale)
    _ = _ := by dsimp only [hamiltonianPermanentUniformBudget, c, d]; ring

theorem stochastic_permanent_first_correction_root_uniform {n : Nat}
    (T : Matrix (Fin n) (Fin n) Real) (q a delta : Real)
    (hn : 16 <= n) (hq : (n : Real) * q = 1) (ha : 1 <= a)
    (hRow : forall i, Finset.sum Finset.univ (fun j => T i j) = 1)
    (hCol : forall j, Finset.sum Finset.univ (fun i => T i j) = 1)
    (hNonneg : forall i j, 0 <= T i j) (hUpper : forall i j, T i j <= a * q)
    (hDelta0 : 0 < delta) (hDelta1 : delta <= 1)
    (hNorm : norm (centeredKernel T q) <= 1 - delta)
    (hRoot : 64 / delta <= hamiltonianGammaCoreRoot (n : Real))
    (hCap : a <= delta ^ 3 * hamiltonianGammaCoreRoot (n : Real) / 1000000)
    (hSize : hamiltonianPermanentCutoffThreshold delta a <= Real.sqrt (n : Real)) :
    abs (((n : Real) ^ n / (n.factorial : Real)) * weightedPermutationSum T -
      realGramDeterminantFactor (centeredKernel T q) 1 *
        (1 + stochasticPermanentFirstCorrection T q)) <=
      realGramDeterminantFactor (centeredKernel T q) 1 * (1 + a) ^ 24 *
        hamiltonianPermanentUniformBudget delta / (n : Real) ^ 2 := by
  have hW := hamiltonian_gamma_root_window_data n a delta hn ha hDelta0 hDelta1 hRoot hCap
  have hExact := stochastic_permanent_first_correction_explicit T q a delta
    (hamiltonianGammaCoreWidth (n : Real)) hn hq ha hRow hCol hNonneg hUpper
    hDelta0 hDelta1 hNorm hW.width_pos hW.width_small hW.core_large
    hW.physical_large hW.covariance_small hSize
  exact le_trans hExact
    (stochastic_permanent_gamma_error_uniform T q a delta hn hq ha hRow hCol
      hNonneg hUpper hDelta0 hDelta1 hNorm hW)

theorem stochastic_permanent_first_correction_polylog_uniform (delta K : Real)
    (hDelta0 : 0 < delta) (hDelta1 : delta <= 1) :
    Exists (fun N0 : Nat => And (16 <= N0)
      (forall n : Nat, N0 <= n ->
        forall (T : Matrix (Fin n) (Fin n) Real) (q a : Real),
          (n : Real) * q = 1 -> 1 <= a -> a <= (Real.log (n : Real)) ^ K ->
          (forall i, Finset.sum Finset.univ (fun j => T i j) = 1) ->
          (forall j, Finset.sum Finset.univ (fun i => T i j) = 1) ->
          (forall i j, 0 <= T i j) -> (forall i j, T i j <= a * q) ->
          norm (centeredKernel T q) <= 1 - delta ->
          abs (((n : Real) ^ n / (n.factorial : Real)) * weightedPermutationSum T -
            realGramDeterminantFactor (centeredKernel T q) 1 *
              (1 + stochasticPermanentFirstCorrection T q)) <=
            realGramDeterminantFactor (centeredKernel T q) 1 * (1 + a) ^ 24 *
              hamiltonianPermanentUniformBudget delta / (n : Real) ^ 2)) := by
  let range := hamiltonian_permanent_gamma_polylog_range delta K hDelta0
  refine Exists.intro range.choose (And.intro range.choose_spec.1 ?_)
  intro n hn T q a hq ha hA hRow hCol hNonneg hUpper hNorm
  have hData := range.choose_spec.2 n hn a ha hA
  exact stochastic_permanent_first_correction_root_uniform T q a delta
    (le_trans range.choose_spec.1 hn) hq ha hRow hCol hNonneg hUpper
    hDelta0 hDelta1 hNorm hData.2.1 hData.2.2 hData.1

end PrimeFactorOscillations

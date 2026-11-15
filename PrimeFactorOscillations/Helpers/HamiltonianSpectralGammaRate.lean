/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianGammaCorrectionBudget
import PrimeFactorOscillations.Helpers.HamiltonianGammaMomentDecay

/-! # Spectral terms in the complete permanent Gamma error

A common energy budget controls the actual Taylor coefficients and their
truncation tails. The algebraic affine budget is evaluated at width one
only to bound its nonnegative coefficients; no analytic window is enlarged.
The exact odd third moment retains its two-power decay.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

variable {Iota : Type*}

def hamiltonianSpectralGammaBudget (delta : Real) : Real :=
  1 + 2 / delta + hamiltonianSpectralAffineBudget delta

theorem spectralGamma_common_budget (S : Finset Iota) (lam : Iota -> Real)
    (delta a : Real) (hDelta0 : 0 < delta) (hDelta1 : delta <= 1) (ha : 1 <= a)
    (hLam0 : forall i, Membership.mem S i -> 0 <= lam i)
    (hLam1 : forall i, Membership.mem S i -> lam i <= (1 - delta) ^ 2)
    (hMass : Finset.sum S lam <= a) :
    let M := spectralFactors S lam 1 * (1 + a) ^ 4 * hamiltonianSpectralGammaBudget delta
    And (abs (spectralFactors S lam 1) <= M)
      (And (abs (spectralFactorJet1 S lam 1) <= M)
        (And (abs (spectralFactorJet2 S lam 1 / 2) <= M)
          (And (abs (spectralFactorJet3 S lam 1 / 6) <= M)
            (spectralTaylorRemainderBound S lam delta <= M)))) := by
  let D := spectralFactors S lam 1
  let H := (1 + a) ^ 4
  let U := hamiltonianSpectralAffineBudget delta
  let K := hamiltonianSpectralGammaBudget delta
  have hD : 0 < D := Real.exp_pos _
  have ha0 : 0 <= a := by linarith only [ha]
  have hH : 1 <= H := by
    have h := wick_nonnegative_power_le 1 (1 + a) (by norm_num)
      (show (1 : Real) <= 1 + a by linarith only [ha0]) 4
    simpa only [one_pow] using h
  have hH0 : 0 <= H := le_trans (by norm_num) hH
  have hDH : 0 <= D * H := mul_nonneg hD.le hH0
  have hU : 0 <= U := by dsimp only [U, hamiltonianSpectralAffineBudget]; positivity
  have hKOne : 1 <= K := by
    change 1 <= 1 + 2 / delta + U
    have hDiv : (0 : Real) <= 2 / delta := by positivity
    linarith only [hDiv, hU]
  have hKU : U <= K := by
    change U <= 1 + 2 / delta + U
    have hDiv : (0 : Real) <= 2 / delta := by positivity
    linarith only [hDiv]
  have hKFirst : 2 / delta <= K := by
    change 2 / delta <= 1 + 2 / delta + U
    linarith only [hU]
  have hUM := mul_le_mul_of_nonneg_left hKU hDH
  have hBudget := spectralAffineRemainderBound_polynomial S lam delta 1 a
    hDelta0 hDelta1 ha (by norm_num) (by norm_num) hLam0 hLam1 hMass
  simp only [spectralAffineRemainderBound, one_pow, mul_one] at hBudget
  have hMass0 : 0 <= Finset.sum S lam := Finset.sum_nonneg (fun i hi => hLam0 i hi)
  have hR0 : 0 <= spectralTaylorRemainderBound S lam delta := by
    unfold spectralTaylorRemainderBound
    positivity
  have hSecond : abs (spectralFactorJet2 S lam 1 / 2) <= D * H * U := by
    change _ <= D * H * U at hBudget
    linarith only [hBudget, abs_nonneg (spectralFactorJet3 S lam 1 / 6), hR0]
  have hThird : abs (spectralFactorJet3 S lam 1 / 6) <= D * H * U := by
    change _ <= D * H * U at hBudget
    linarith only [hBudget, abs_nonneg (spectralFactorJet2 S lam 1 / 2), hR0]
  have hFourth : spectralTaylorRemainderBound S lam delta <= D * H * U := by
    change _ <= D * H * U at hBudget
    linarith only [hBudget, abs_nonneg (spectralFactorJet2 S lam 1 / 2),
      abs_nonneg (spectralFactorJet3 S lam 1 / 6)]
  have haH : a <= H := by
    simpa only [one_pow, one_mul, pow_one] using
      hamiltonian_polynomial_power_bound 1 (1 + a) a 1 4
        (by norm_num) (by linarith only [ha]) ha0 (by linarith) (by omega)
  have hJ1 := (spectralFactors_central_jet_bounds S lam delta a
    hDelta0 hDelta1 ha hLam0 hLam1 hMass).1
  have hFirst : abs (spectralFactorJet1 S lam 1) <= D * H * (2 / delta) := by
    apply le_of_mul_le_mul_left (a := delta) _ hDelta0
    have h := mul_le_mul_of_nonneg_left haH (by positivity : 0 <= 2 * D)
    calc
      _ <= 2 * D * H := by nlinarith only [hJ1, h]
      _ = _ := by field_simp [ne_of_gt hDelta0]
  refine And.intro ?_ (And.intro ?_ (And.intro ?_ (And.intro ?_ ?_)))
  next =>
    change abs D <= D * H * K
    rw [abs_of_pos hD]
    calc
      _ <= D * H := by
        have h := mul_le_mul_of_nonneg_left hH hD.le
        simpa only [mul_one] using h
      _ <= _ := by simpa only [mul_one] using mul_le_mul_of_nonneg_left hKOne hDH
  next =>
    exact le_trans hFirst (mul_le_mul_of_nonneg_left hKFirst hDH)
  next => exact le_trans hSecond hUM
  next => exact le_trans hThird hUM
  next => exact le_trans hFourth hUM

theorem spectralGamma_tail_coefficient_bound (S : Finset Iota) (lam : Iota -> Real)
    (delta a : Real) (hDelta0 : 0 < delta) (hDelta1 : delta <= 1) (ha : 1 <= a)
    (hLam0 : forall i, Membership.mem S i -> 0 <= lam i)
    (hLam1 : forall i, Membership.mem S i -> lam i <= (1 - delta) ^ 2)
    (hMass : Finset.sum S lam <= a) :
    spectralTaylorTailCoefficient S lam <=
      97 * spectralFactors S lam 1 * (1 + a) ^ 4 * hamiltonianSpectralGammaBudget delta := by
  have h := spectralGamma_common_budget S lam delta a hDelta0 hDelta1 ha hLam0 hLam1 hMass
  unfold spectralTaylorTailCoefficient
  nlinarith only [h.1, h.2.1, h.2.2.1, h.2.2.2.1]

theorem spectralGamma_higher_moment_remainder (S : Finset Iota) (lam : Iota -> Real)
    (n : Nat) (hn : 16 <= n) (delta a : Real)
    (hDelta0 : 0 < delta) (hDelta1 : delta <= 1) (ha : 1 <= a)
    (hLam0 : forall i, Membership.mem S i -> 0 <= lam i)
    (hLam1 : forall i, Membership.mem S i -> lam i <= (1 - delta) ^ 2)
    (hMass : Finset.sum S lam <= a) :
    spectralTaylorRemainderBound S lam delta *
        gammaInverseAverage n (fun s : Real => (s - 1) ^ 4) +
      abs ((spectralFactorJet3 S lam 1 / 6) *
        gammaInverseAverage n (fun s : Real => (s - 1) ^ 3)) <=
      64 * spectralFactors S lam 1 * (1 + a) ^ 4 *
        hamiltonianSpectralGammaBudget delta / (n : Real) ^ 2 := by
  let M := spectralFactors S lam 1 * (1 + a) ^ 4 * hamiltonianSpectralGammaBudget delta
  have hCommon := spectralGamma_common_budget S lam delta a
    hDelta0 hDelta1 ha hLam0 hLam1 hMass
  have hM0 : 0 <= M := le_trans (abs_nonneg _) hCommon.1
  have hN : (16 : Real) <= (n : Real) := by exact_mod_cast hn
  have h1 : 0 < (n : Real) - 1 := by linarith only [hN]
  have h2 : 0 < (n : Real) - 2 := by linarith only [hN]
  have h3 : 0 < (n : Real) - 3 := by linarith only [hN]
  have hMu4 : 0 <= gammaInverseAverage n (fun s : Real => (s - 1) ^ 4) := by
    rw [gammaInverseAverage_fourth_uniform n (by omega)]
    positivity
  have hFourth := mul_le_mul hCommon.2.2.2.2
    (gammaInverseAverage_fourth_decay n (by omega)) hMu4 hM0
  have hThird := mul_le_mul hCommon.2.2.2.1
    (gammaInverseAverage_third_decay n (by omega)) (abs_nonneg _) hM0
  rw [abs_mul]
  calc
    _ <= M * (48 / (n : Real) ^ 2) + M * (16 / (n : Real) ^ 2) :=
      add_le_add hFourth hThird
    _ = _ := by dsimp only [M]; ring

end PrimeFactorOscillations

/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianCovarianceCorrectionAverage
import PrimeFactorOscillations.Helpers.HamiltonianSpectralCentralJets

/-! # Polynomial budgets for the complete Gamma correction remainder

The actual spectral jets supply a fourth-power entry-cap budget. Combining
this with the inverse-dimension covariance Taylor estimate gives the required
two-power scale after Gamma averaging. The signed constant and linear terms
remain in the exact averaging theorem.
-/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations

variable {Iota : Type*}

def hamiltonianSpectralAffineBudget (delta : Real) : Real :=
  13 / (2 * delta ^ 2) + 23 / delta ^ 3 + 86 * Real.exp 1 / delta ^ 4

def hamiltonianSpectralIncrementBudget (delta : Real) : Real :=
  2 / delta + hamiltonianSpectralAffineBudget delta

theorem spectralAffineRemainderBound_polynomial (S : Finset Iota) (lam : Iota -> Real)
    (delta eps a : Real) (hDelta0 : 0 < delta) (hDelta1 : delta <= 1)
    (ha : 1 <= a) (hEps0 : 0 <= eps) (hEps1 : eps <= 1)
    (hLam0 : forall i, Membership.mem S i -> 0 <= lam i)
    (hLam1 : forall i, Membership.mem S i -> lam i <= (1 - delta) ^ 2)
    (hMass : Finset.sum S lam <= a) :
    spectralAffineRemainderBound S lam delta eps <=
      spectralFactors S lam 1 * (1 + a) ^ 4 *
        hamiltonianSpectralAffineBudget delta := by
  let D := spectralFactors S lam 1
  let H := (1 + a) ^ 4
  have hD : 0 < D := Real.exp_pos _
  have ha0 : 0 <= a := by linarith only [ha]
  have hH : 0 <= H := by dsimp only [H]; positivity
  have hPower : forall k : Nat, k <= 4 -> a ^ k <= H := by
    intro k hk
    simpa only [one_pow, one_mul, H] using
      hamiltonian_polynomial_power_bound 1 (1 + a) a k 4
        (by norm_num) (by linarith only [ha]) ha0 (by linarith) hk
  have hJets := spectralFactors_central_jet_bounds S lam delta a hDelta0 hDelta1
    ha hLam0 hLam1 hMass
  have hJ2 : abs (spectralFactorJet2 S lam 1) <= 13 * D * H / delta ^ 2 := by
    apply le_of_mul_le_mul_left (a := delta ^ 2) _ (pow_pos hDelta0 2)
    have h := mul_le_mul_of_nonneg_left (hPower 2 (by omega))
      (mul_nonneg (by norm_num : (0 : Real) <= 13) hD.le)
    calc
      _ <= 13 * D * H := by nlinarith only [hJets.2.1, h]
      _ = _ := by field_simp [ne_of_gt hDelta0]
  have hJ3 : abs (spectralFactorJet3 S lam 1) <= 138 * D * H / delta ^ 3 := by
    apply le_of_mul_le_mul_left (a := delta ^ 3) _ (pow_pos hDelta0 3)
    have h := mul_le_mul_of_nonneg_left (hPower 3 (by omega))
      (mul_nonneg (by norm_num : (0 : Real) <= 138) hD.le)
    calc
      _ <= 138 * D * H := by nlinarith only [hJets.2.2, h]
      _ = _ := by field_simp [ne_of_gt hDelta0]
  have hSecond : abs (spectralFactorJet2 S lam 1 / 2) <=
      D * H * (13 / (2 * delta ^ 2)) := by
    calc
      _ = abs (spectralFactorJet2 S lam 1) / 2 := by rw [abs_div]; norm_num
      _ <= (13 * D * H / delta ^ 2) / 2 :=
        div_le_div_of_nonneg_right hJ2 (by norm_num)
      _ = _ := by ring
  have hThird : abs (spectralFactorJet3 S lam 1 / 6) * eps <=
      D * H * (23 / delta ^ 3) := by
    have hDiv : abs (spectralFactorJet3 S lam 1 / 6) <=
        D * H * (23 / delta ^ 3) := by
      calc
        _ = abs (spectralFactorJet3 S lam 1) / 6 := by rw [abs_div]; norm_num
        _ <= (138 * D * H / delta ^ 3) / 6 :=
          div_le_div_of_nonneg_right hJ3 (by norm_num)
        _ = _ := by ring
    calc
      _ <= abs (spectralFactorJet3 S lam 1 / 6) * 1 :=
        mul_le_mul_of_nonneg_left hEps1 (abs_nonneg _)
      _ <= _ := by simpa only [mul_one] using hDiv
  have hMass0 : 0 <= Finset.sum S lam := Finset.sum_nonneg (fun i hi => hLam0 i hi)
  have hMassPower : (1 + Finset.sum S lam) ^ 4 <= H :=
    wick_nonnegative_power_le _ _ (by linarith only [hMass0])
      (by linarith only [hMass]) 4
  have hEps2 : eps ^ 2 <= 1 := wick_unit_power_le_one eps hEps0 hEps1 2
  have hFourth : spectralTaylorRemainderBound S lam delta * eps ^ 2 <=
      D * H * (86 * Real.exp 1 / delta ^ 4) := by
    have hR0 : 0 <= spectralTaylorRemainderBound S lam delta := by
      unfold spectralTaylorRemainderBound
      positivity
    calc
      _ <= spectralTaylorRemainderBound S lam delta * 1 :=
        mul_le_mul_of_nonneg_left hEps2 hR0
      _ = (2049 / 24 : Real) * Real.exp 1 * D *
          (1 + Finset.sum S lam) ^ 4 / delta ^ 4 := by
        dsimp only [spectralTaylorRemainderBound, D]
        ring
      _ <= (2049 / 24 : Real) * Real.exp 1 * D * H / delta ^ 4 :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hMassPower (by positivity))
          (pow_nonneg hDelta0.le 4)
      _ = (2049 / 24 : Real) * (Real.exp 1 * D * H) / delta ^ 4 := by ring
      _ <= 86 * (Real.exp 1 * D * H) / delta ^ 4 :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right (by norm_num : (2049 / 24 : Real) <= 86)
            (by positivity : 0 <= Real.exp 1 * D * H))
          (pow_nonneg hDelta0.le 4)
      _ = _ := by ring
  change _ <= D * H * hamiltonianSpectralAffineBudget delta
  unfold spectralAffineRemainderBound hamiltonianSpectralAffineBudget
  linarith only [hSecond, hThird, hFourth]

theorem spectralCorrectionProductRemainderBound_polynomial
    (S : Finset Iota) (lam : Iota -> Real)
    (delta eps a G0 G1 G2 : Real) (hDelta0 : 0 < delta) (hDelta1 : delta <= 1)
    (ha : 1 <= a) (hEps0 : 0 <= eps) (hEps1 : eps <= 1)
    (hLam0 : forall i, Membership.mem S i -> 0 <= lam i)
    (hLam1 : forall i, Membership.mem S i -> lam i <= (1 - delta) ^ 2)
    (hMass : Finset.sum S lam <= a)
    (hG0 : 0 <= G0) (hG1 : 0 <= G1) (hG2 : 0 <= G2) :
    spectralCorrectionProductRemainderBound S lam delta eps G0 G1 G2 <=
      spectralFactors S lam 1 * (1 + a) ^ 4 *
        (hamiltonianSpectralAffineBudget delta * G0 +
          hamiltonianSpectralIncrementBudget delta * G1 + Real.exp 1 * G2) := by
  let D := spectralFactors S lam 1
  let H := (1 + a) ^ 4
  let U := hamiltonianSpectralAffineBudget delta
  have hD : 0 < D := Real.exp_pos _
  have ha0 : 0 <= a := by linarith only [ha]
  have hH : 1 <= H := by
    dsimp only [H]
    have hBase : 1 <= 1 + a := by linarith only [ha0]
    have h := wick_nonnegative_power_le 1 (1 + a) (by norm_num) hBase 4
    simpa only [one_pow] using h
  have hH0 : 0 <= H := le_trans (by norm_num) hH
  have hU : 0 <= U := by dsimp only [U, hamiltonianSpectralAffineBudget]; positivity
  have hR := spectralAffineRemainderBound_polynomial S lam delta eps a
    hDelta0 hDelta1 ha hEps0 hEps1 hLam0 hLam1 hMass
  have hJets := spectralFactors_central_jet_bounds S lam delta a
    hDelta0 hDelta1 ha hLam0 hLam1 hMass
  have haH : a <= H := by
    simpa only [one_pow, one_mul, pow_one, H] using
      hamiltonian_polynomial_power_bound 1 (1 + a) a 1 4
        (by norm_num) (by linarith only [ha]) ha0 (by linarith) (by omega)
  have hJ1 : abs (spectralFactorJet1 S lam 1) <= D * H * (2 / delta) := by
    apply le_of_mul_le_mul_left (a := delta) _ hDelta0
    have h := mul_le_mul_of_nonneg_left haH (by positivity : 0 <= 2 * D)
    calc
      _ <= 2 * D * H := by nlinarith only [hJets.1, h]
      _ = _ := by field_simp [ne_of_gt hDelta0]
  have hREps : spectralAffineRemainderBound S lam delta eps * eps <= D * H * U := by
    have h := mul_le_mul_of_nonneg_right hR hEps0
    have h' := mul_le_mul_of_nonneg_left hEps1
      (mul_nonneg (mul_nonneg hD.le hH0) hU)
    change _ <= D * H * U
    change _ <= D * H * U * eps at h
    nlinarith only [h, h']
  have hFirst := mul_le_mul_of_nonneg_right hR hG0
  have hInc : abs (spectralFactorJet1 S lam 1) +
      spectralAffineRemainderBound S lam delta eps * eps <=
        D * H * hamiltonianSpectralIncrementBudget delta := by
    unfold hamiltonianSpectralIncrementBudget
    change _ <= D * H * (2 / delta + U)
    nlinarith only [hJ1, hREps]
  have hSecond := mul_le_mul_of_nonneg_right hInc hG1
  have hThird : Real.exp 1 * D * G2 <= D * H * (Real.exp 1 * G2) := by
    have h := mul_le_mul_of_nonneg_left hH
      (mul_nonneg (mul_nonneg (Real.exp_pos 1).le hD.le) hG2)
    nlinarith only [h]
  unfold spectralCorrectionProductRemainderBound
  change _ <= D * H * (U * G0 + hamiltonianSpectralIncrementBudget delta * G1 +
    Real.exp 1 * G2)
  nlinarith only [hFirst, hSecond, hThird]

end PrimeFactorOscillations

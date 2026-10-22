/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Proof.PrimeClassDeletion.GaussianRealCutoffTransfer

/-!
# A forbidden zeta zero forces deletions at every large real cutoff

This is the full unconditional paper theorem for the fixed greedy
deleted-prime class. No largest zero real part, RH hypothesis, or
assumed oscillation asymptotic occurs among its inputs.
-/

set_option autoImplicit false
set_option Elab.async false

open PrimeFactorOscillations.PrimeClassSampling

namespace PrimeFactorOscillations.PrimeClassDeletion

theorem greedyDeletedPrimeClass_uniform_zero_response
    (rho0 : Complex) (hZero : riemannZeta rho0 = 0)
    (hStrip : And (0 < rho0.re) (rho0.re < 1))
    (hBeta : (1 / 2 : Real) < rho0.re)
    (epsilon : Real) (he : 0 < epsilon) :
    Exists fun d : Real => And (0 < d)
      (Exists fun X0 : Real => forall X : Real, X0 <= X ->
        d * X ^ (rho0.re - epsilon) <=
          ((primeClassPrefix greedyDeletedPrimeClass (Nat.floor X)).card : Real)) := by
  classical
  have heHalf : 0 < epsilon / 2 := div_pos he (by norm_num)
  cases exists_gaussian_localizer (epsilon / 2) heHalf with
  | intro a ha =>
    let z0 : ZetaDistinctZero := Subtype.mk rho0 (And.intro hZero hStrip)
    have hc : 0 < a ^ 2 := sq_pos_of_pos ha.1
    cases gaussianZetaEnvelope_unique_exposure (a ^ 2) hc z0 hBeta with
    | intro tau ht =>
      cases ht.2 with
      | intro w hw =>
        let B : Real := gaussianZeroExponent (a ^ 2) w.val.re w.val.im tau
        let kappa : Real := a ^ 2 + 2 * a
        let s : Real := 1 + a ^ 2 + 2 * a
        let d : Real := gaussianZetaAmplitude w / 8
        have hd : 0 < d := div_pos (gaussianZetaAmplitude_pos w) (by norm_num)
        have hWin := hw.2.2.2
        rw [hw.1] at hWin
        have hEnvelope := (max_lt_iff.mp hWin).1
        have hPrimePower := (max_lt_iff.mp (max_lt_iff.mp hWin).2).1
        have hBad := (max_lt_iff.mp (max_lt_iff.mp hWin).2).2
        change rho0.re < B at hBad
        choose T hT using greedyPrimeRegulatorReal_gaussian_power_lower
          a tau ha.1 ha.2.1 w hw.2.2.1 hEnvelope hPrimePower
        have hk : 0 <= kappa := by
          dsimp only [kappa]
          nlinarith only [ha.1, sq_nonneg a]
        have hCross := gaussian_localized_exponent_cross rho0.re (epsilon / 2) kappa
          hStrip.2.le heHalf hk ha.2.2
        have hs : 0 < s := by
          change 0 < 1 + a ^ 2 + 2 * a
          nlinarith only [ha.1, sq_nonneg a]
        have hCross' : (rho0.re - epsilon / 2) * s < B := by
          have hsEq : 1 + kappa = s := by dsimp only [kappa, s]; ring
          rw [hsEq] at hCross
          exact hCross.2.trans hBad
        have hRate : rho0.re - epsilon / 2 < B / s := by
          have hCancel : (B / s) * s = B := by field_simp [hs.ne']
          by_contra hFail
          have hMul := mul_le_mul_of_nonneg_right (le_of_not_gt hFail) hs.le
          rw [hCancel] at hMul
          exact (not_lt_of_ge hMul) hCross'
        choose Y0 hY0 using greedyPrimeRegulatorReal_rescale_power_lower s B d T hs hT
        choose Y1 hY1 using greedyDeletedPrimeClass_count_of_regulator_power_lower
          (B / s) d (epsilon / 2) Y0 hd heHalf hY0
        refine Exists.intro d (And.intro hd (Exists.intro (max 2 Y1) ?_))
        intro X hX0
        have hX2 : 2 <= X := (le_max_left 2 Y1).trans hX0
        have hXPos : 0 < X := by linarith only [hX2]
        have hCount := hY1 X ((le_max_right 2 Y1).trans hX0)
        have hExponent : rho0.re - epsilon <= B / s - epsilon / 2 := by
          linarith only [hRate]
        have hPower : X ^ (rho0.re - epsilon) <= X ^ (B / s - epsilon / 2) := by
          simp only [Real.rpow_def_of_pos hXPos]
          apply Real.exp_le_exp.mpr
          exact mul_le_mul_of_nonneg_left hExponent
            (Real.log_nonneg (by linarith only [hX2]))
        exact (mul_le_mul_of_nonneg_left hPower hd.le).trans hCount

end PrimeFactorOscillations.PrimeClassDeletion

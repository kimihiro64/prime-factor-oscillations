/-
Copyright (c) 2026 Matteo Cipollina and Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina, Prime Factor Oscillations contributors
-/
import PrimeNumberTheoremAnd.Mathlib.NumberTheory.LSeries.RiemannXiDivisorZeros
/-!
# Logarithmic growth of the completed xi function

Retains the logarithm in the Gamma and zeta growth argument, giving a fixed
constant times (1 + norm z) log (2 + norm z). This is the analytic input for
a multiplicity-counting Jensen bound and the sharp degree-localization error.

The argument adapts the right-half-plane bounds from
PrimeNumberTheoremAnd/Mathlib/NumberTheory/LSeries/ZetaFiniteOrder.lean at
f6147e7572ab3abe5428101bc0b13627bcb005df, licensed Apache-2.0. It uses the
canonical cached xi function and its functional equation. No moving epsilon
is substituted into an existential finite-order bound. This is a
formalization of classical growth estimates, not a new prime-gap result.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

/-- Polynomial prefactor and logarithmic exponential growth on the right half-plane. -/
theorem nicolasXi_right_growth :
    Exists fun C : Real => And (0 < C) (forall w : Complex, (1 / 2 : Real) <= w.re -> 4 <= norm w ->
        norm (Complex.riemannXi w) <=
          (1 + norm w) ^ (3 : Nat) *
            Real.exp (C * norm w * Real.log (1 + norm w))) := by
  choose C hC hGamma using Complex.Gamma.stirling_bound_re_ge_zero
  refine Exists.intro C (And.intro hC ?_)
  intro w hwRe hwNorm
  have hw0 : Not (w = 0) := by
    intro h
    norm_num [h] at hwNorm
  have hw1 : Not (w = 1) := by
    intro h
    norm_num [h] at hwNorm
  have hwRePos : 0 < w.re := by linarith
  have hhalfRe : 0 < (w / 2).re := by
    simp only [Complex.div_ofNat_re]
    linarith
  have hhalfNorm : norm (w / 2) = norm w / 2 := by
    rw [norm_div]
    norm_num
  have hGamma0 := Complex.Gamma_ne_zero_of_re_pos hhalfRe
  have hGam := hGamma (w / 2) hhalfRe.le (by rw [hhalfNorm]; linarith)
  rw [hhalfNorm] at hGam
  have hlog0 : 0 <= Real.log (1 + norm w / 2) :=
    Real.log_nonneg (by linarith [norm_nonneg w])
  have hlogLe : Real.log (1 + norm w / 2) <= Real.log (1 + norm w) :=
    Real.log_le_log (by positivity) (by linarith [norm_nonneg w])
  have hGamExp : C * (norm w / 2) * Real.log (1 + norm w / 2) <=
      C * norm w * Real.log (1 + norm w) := by
    exact mul_le_mul
      (mul_le_mul_of_nonneg_left (by linarith [norm_nonneg w]) hC.le)
      hlogLe hlog0 (by positivity)
  have hGamBound : norm (Complex.Gamma (w / 2)) <=
      Real.exp (C * norm w * Real.log (1 + norm w)) :=
    hGam.trans (Real.exp_le_exp.mpr hGamExp)
  have hPi : norm ((Real.pi : Complex) ^ (-w / 2)) <= 1 := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
    apply Real.rpow_le_one_of_one_le_of_nonpos (by linarith [Real.pi_gt_three])
    simp only [Complex.div_ofNat_re, Complex.neg_re]
    linarith
  have hDist : norm (1 / (w - 1)) <= 1 := by
    have hBack := norm_add_le (w - 1) (1 : Complex)
    simp only [sub_add_cancel, norm_one] at hBack
    rw [norm_div, norm_one]
    exact (div_le_one (by linarith)).mpr (by linarith)
  have hDiv : norm w / w.re <= 2 * norm w := by
    have hInv : 1 / w.re <= 2 := by
      have h := one_div_le_one_div_of_le (by norm_num : (0 : Real) < 1 / 2) hwRe
      norm_num at h
      simpa using h
    calc
      _ = norm w * (1 / w.re) := by ring
      _ <= norm w * 2 := mul_le_mul_of_nonneg_left hInv (norm_nonneg w)
      _ = _ := by ring
  have hZeta := norm_riemannZeta_le w
    (mem_zetaAbelContinuationDomain_of_re hw1
      (zetaAbelContinuationReLower_lt_half.trans_le (by simpa using hwRe)))
  have hZetaBound : norm (riemannZeta w) <= 2 + 2 * norm w := by
    linarith
  have hLambda : norm (completedRiemannZeta w) <=
      Real.exp (C * norm w * Real.log (1 + norm w)) * (2 + 2 * norm w) := by
    rw [completedRiemannZeta_eq_cpow_mul_Gamma_mul_riemannZeta hw0 hGamma0,
      norm_mul, norm_mul]
    exact mul_le_mul
      ((mul_le_mul hPi hGamBound (norm_nonneg _) (by norm_num)).trans_eq (one_mul _))
      hZetaBound (norm_nonneg _) (by positivity)
  have hWSub : norm (w - 1) <= norm w + 1 := by
    simpa only [norm_one] using norm_sub_le w 1
  rw [Complex.riemannXi_eq_mul_completedRiemannZeta hw0 hw1,
    norm_div, norm_mul, norm_mul]
  rw [show norm (2 : Complex) = (2 : Real) by norm_num]
  have hTop := mul_le_mul
    (mul_le_mul_of_nonneg_left hWSub (norm_nonneg w))
    hLambda (norm_nonneg _) (by positivity)
  have hPoly : norm w * (norm w + 1) *
      (Real.exp (C * norm w * Real.log (1 + norm w)) * (2 + 2 * norm w)) <=
      2 * ((1 + norm w) ^ (3 : Nat) *
        Real.exp (C * norm w * Real.log (1 + norm w))) := by
    nlinarith [mul_nonneg
      (sq_nonneg (1 + norm w))
      (Real.exp_pos (C * norm w * Real.log (1 + norm w))).le]
  nlinarith [hTop, hPoly]


/-- Fixed logarithmic growth; no epsilon-dependent constant is specialized. -/
theorem nicolasXi_log_growth :
    Exists fun C : Real => And (0 < C) (forall z : Complex,
      Real.log (1 + norm (Complex.riemannXi z)) <=
        C * (1 + norm z) * Real.log (2 + norm z)) := by
  choose G hG hRight using nicolasXi_right_growth
  choose M hM hCompact using Complex.exists_norm_bound_on_closedBall
    (Complex.differentiable_riemannXi.continuous.continuousOn :
      ContinuousOn Complex.riemannXi (Metric.closedBall 0 4))
  let C : Real := 2 * (G + 4) + (M + 1) / Real.log 2
  have hLog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hReserve : 0 < (M + 1) / Real.log 2 := div_pos (by linarith) hLog2
  have hC : 0 < C := by dsimp [C]; linarith
  refine Exists.intro C (And.intro hC ?_)
  intro z
  have hReflect : Exists fun w : Complex =>
      And ((1 / 2 : Real) <= w.re)
        (And (norm w <= 1 + norm z) (Complex.riemannXi w = Complex.riemannXi z)) := by
    by_cases h : (1 / 2 : Real) <= z.re
    . exact Exists.intro z (And.intro h (And.intro (by linarith) rfl))
    . refine Exists.intro (1 - z) (And.intro ?_ (And.intro ?_
        (Complex.riemannXi_one_sub z)))
      . simp only [Complex.sub_re, Complex.one_re]
        linarith
      . simpa only [norm_one] using norm_sub_le (1 : Complex) z
  choose w hwRe hwNorm hwEq using hReflect
  have hL : 0 <= Real.log (2 + norm z) :=
    Real.log_nonneg (by linarith [norm_nonneg z])
  have hWeight : Real.log 2 <= (1 + norm z) * Real.log (2 + norm z) := by
    have hLog := Real.log_le_log (by norm_num : (0 : Real) < 2)
      (show (2 : Real) <= 2 + norm z by linarith [norm_nonneg z])
    nlinarith [mul_nonneg (norm_nonneg z) hL]
  rw [<- hwEq]
  by_cases hSmall : norm w <= 4
  . have hNorm := hCompact w hSmall
    have hLog := Real.log_le_sub_one_of_pos
      (show 0 < 1 + norm (Complex.riemannXi w) by positivity)
    have hPayment := mul_le_mul_of_nonneg_left hWeight hReserve.le
    have hPaid : (M + 1) / Real.log 2 * Real.log 2 = M + 1 := by
      field_simp [hLog2.ne']
    rw [hPaid] at hPayment
    have hExtra : 0 <= 2 * (G + 4) * (1 + norm z) * Real.log (2 + norm z) :=
      mul_nonneg (by positivity) hL
    dsimp [C]
    nlinarith [hLog, hNorm, hPayment, hExtra]
  . have hw4 : 4 <= norm w := (lt_of_not_ge hSmall).le
    have hRPos : 0 < 1 + norm w := by positivity
    have hLR : 0 <= Real.log (1 + norm w) :=
      Real.log_nonneg (by linarith [norm_nonneg w])
    have hExp1 : 1 <= Real.exp (G * norm w * Real.log (1 + norm w)) :=
      Real.one_le_exp_iff.mpr (by positivity)
    have hPoly1 : (1 : Real) <= (1 + norm w) ^ (3 : Nat) := by
      have hCube : 0 <= norm w * norm w * norm w := by positivity
      nlinarith [sq_nonneg (norm w)]
    have hV1 : (1 : Real) <= (1 + norm w) ^ (3 : Nat) *
        Real.exp (G * norm w * Real.log (1 + norm w)) := by
      simpa only [one_mul] using
        mul_le_mul hPoly1 hExp1 (by norm_num : (0 : Real) <= 1) (by positivity)
    have hNorm := hRight w hwRe hw4
    have hBound : Real.log (1 + norm (Complex.riemannXi w)) <=
        Real.log 2 + 3 * Real.log (1 + norm w) +
          G * norm w * Real.log (1 + norm w) := by
      calc
        _ <= Real.log (2 * ((1 + norm w) ^ (3 : Nat) *
            Real.exp (G * norm w * Real.log (1 + norm w)))) :=
          Real.log_le_log (by positivity) (by linarith)
        _ = _ := by
          rw [Real.log_mul (by norm_num : Not ((2 : Real) = 0)) (by positivity),
            Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_exp]
          ring
    have hLog2R : Real.log 2 <= Real.log (1 + norm w) :=
      Real.log_le_log (by norm_num) (by linarith)
    have hCoarse : Real.log (1 + norm (Complex.riemannXi w)) <=
        (G + 4) * (1 + norm w) * Real.log (1 + norm w) := by
      have hA := mul_nonneg hG.le hLR
      have hB := mul_nonneg (norm_nonneg w) hLR
      nlinarith [hBound, hLog2R]
    have hRatio : (1 + norm w) * Real.log (1 + norm w) <=
        (2 * (1 + norm z)) * Real.log (2 + norm z) :=
      mul_le_mul (by linarith [norm_nonneg z])
        (Real.log_le_log hRPos (by linarith)) hLR (by positivity)
    have hScale := mul_le_mul_of_nonneg_left hRatio (show 0 <= G + 4 by linarith)
    have hRest : 0 <= (M + 1) / Real.log 2 *
        (1 + norm z) * Real.log (2 + norm z) := mul_nonneg (by positivity) hL
    dsimp [C]
    nlinarith [hCoarse, hScale, hRest]

end PrimeFactorOscillations

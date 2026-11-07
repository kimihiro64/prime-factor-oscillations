/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.CarmichaelSharpMultiplicity
import PrimeFactorOscillations.Helpers.CompensatedXiConstants
import PrimeFactorOscillations.Helpers.XiEffectiveBounds

/-!
# Explicit epsilon constants and the scope of a simplicity certificate

The coarse epsilon witness uses fixed real zeta logarithmic derivatives.
A separate signed estimate supplies constants 4/5 and 11/100 at coefficient
3/5 and proves a numerical simplicity window, including every multiplicity
copy on the full critical strip. No Riemann hypothesis is assumed.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

open Complex Robin1984

def effectiveMultiplicityInner (eps : Real) : Real :=
  1 / 2 + min ((Real.sharpResolventOuter - 1 / 2) / 2) eps

def effectiveMultiplicityConstant (eps : Real) : Real :=
  let r := effectiveMultiplicityInner eps
  let a := 1 / 2 + r
  multiplicityBoundConstant r Real.sharpResolventOuter
    (xiExplicitHeight a a) (xiExplicitLipschitz a)

theorem effectiveMultiplicity_parameters (eps : Real) (heps : 0 < eps) :
    And (1 / 2 < effectiveMultiplicityInner eps)
      (And (effectiveMultiplicityInner eps < Real.sharpResolventOuter)
        (And (2 * (3 / 8 : Real) <=
          Real.sqrt ((effectiveMultiplicityInner eps) ^ 2 - (3 / 8 : Real) ^ 2) +
          Real.sqrt (Real.sharpResolventOuter ^ 2 - (3 / 8 : Real) ^ 2))
          (Real.pairedResolventCoefficient (effectiveMultiplicityInner eps)
            Real.sharpResolventOuter < Real.sharpResolventCoefficient + eps))) := by
  let d := min ((Real.sharpResolventOuter - 1 / 2) / 2) eps
  let r := effectiveMultiplicityInner eps
  have hd : 0 < d := lt_min (by linarith only [Real.sharpResolventOuter_gt_half]) heps
  have hdOuter : d <= (Real.sharpResolventOuter - 1 / 2) / 2 := min_le_left _ _
  have hdEps : d <= eps := min_le_right _ _
  have hr : 1 / 2 < r := by dsimp only [r, effectiveMultiplicityInner]; linarith only [hd]
  have hR : r < Real.sharpResolventOuter := by
    dsimp only [r, effectiveMultiplicityInner]
    linarith only [hdOuter, Real.sharpResolventOuter_gt_half]
  have hb := Real.pairedResolventCoefficient_increment r Real.sharpResolventOuter hr.le
    (by linarith only [Real.sharpResolventOuter_gt_half])
  have hBase : Real.pairedResolventCoefficient (1 / 2) Real.sharpResolventOuter =
      Real.sharpResolventCoefficient := by
    rw [Real.sharpResolventCoefficient_eq]
    unfold Real.pairedResolventCoefficient
    field_simp
  rw [hBase] at hb
  refine And.intro hr (And.intro hR
    (And.intro (Real.sharpResolvent_positive_of_inner r hr.le) ?_))
  change Real.pairedResolventCoefficient r Real.sharpResolventOuter <
    Real.sharpResolventCoefficient + eps
  have hrd : r - 1 / 2 = d := by
    dsimp only [r, effectiveMultiplicityInner, d]
    ring
  rw [hrd] at hb
  linarith only [hb, hdEps, heps]

theorem zeta_multiplicity_seven_eighths_effective_bound (eps : Real) (heps : 0 < eps)
    (w : Complex) (hw : And (0 < w.re) (w.re < 1)) (ht : 2 <= abs w.im) :
    (analyticOrderNatAt riemannZeta w : Real) <=
      (Real.sharpResolventCoefficient + eps) * Real.log (abs w.im) +
        effectiveMultiplicityConstant eps := by
  let r := effectiveMultiplicityInner eps
  let a := 1 / 2 + r
  have hp := effectiveMultiplicity_parameters eps heps
  have ha : 1 < a := by dsimp only [a]; linarith only [hp.1]
  have hb := zeta_multiplicity_bound_with_constants (3 / 8) r Real.sharpResolventOuter
    (xiExplicitHeight a a) (xiExplicitLipschitz a) (by norm_num)
    (by linarith only [hp.1]) hp.1 hp.2.1 hp.2.2.1 xi_seven_eighths_centered_strip
    (xi_logDeriv_explicit_height a a ha) (xi_logDeriv_explicit_lipschitz a ha) w hw ht
  have hLog : 0 <= Real.log (abs w.im) := Real.log_nonneg (by linarith only [ht])
  have hCoef := mul_le_mul_of_nonneg_right hp.2.2.2.le hLog
  change (analyticOrderNatAt riemannZeta w : Real) <=
    Real.pairedResolventCoefficient r Real.sharpResolventOuter * Real.log (abs w.im) +
      effectiveMultiplicityConstant eps at hb
  linarith only [hb, hCoef]

theorem effectiveMultiplicityConstant_gt_two (eps : Real) (heps : 0 < eps) :
    2 < effectiveMultiplicityConstant eps := by
  let r := effectiveMultiplicityInner eps
  let S := Real.sharpResolventOuter
  let a := 1 / 2 + r
  let delta := r - 1 / 2
  let f := r * S / (r + S)
  have hp := effectiveMultiplicity_parameters eps heps
  have hr : 1 / 2 < r := hp.1
  have hS : 1 / 2 < S := Real.sharpResolventOuter_gt_half
  have hr0 : 0 < r := by linarith only [hr]
  have hS0 : 0 < S := by linarith only [hS]
  have ha : 1 < a := by dsimp only [a]; linarith only [hr]
  have hd : 0 < delta := sub_pos.mpr hr
  have hSupper : S < 3 / 4 := by
    have hA0 := Real.sharpResolventSemiaxis_pos
    have hA2 := Real.sharpResolventSemiaxis_sq
    have hSS := Real.sharpResolventOuter_sq
    have hA : 1 / 6 < Real.sharpResolventSemiaxis := by nlinarith only [hA0, hA2]
    change Real.sharpResolventOuter < 3 / 4
    nlinarith only [hA, hA2, hSS, Real.sharpResolventOuter_gt_half]
  have hdelta : delta < 1 / 8 := by
    have hmin := min_le_left ((S - 1 / 2) / 2) eps
    have hdeltaDef : delta = min ((S - 1 / 2) / 2) eps := by
      dsimp only [delta, r, effectiveMultiplicityInner, S]
      ring
    rw [hdeltaDef]
    linarith only [hmin, hSupper]
  have hden : 0 < r + S := add_pos hr0 hS0
  have hf0 : 0 < f := div_pos (mul_pos hr0 hS0) hden
  have hf : 1 / 4 < f := by
    have hProd := mul_pos (sub_pos.mpr hr) (sub_pos.mpr hS)
    have hCross : (r + S) / 4 < r * S := by nlinarith only [hr, hS, hProd]
    have hId : f * (r + S) = r * S := by dsimp only [f]; field_simp
    by_contra hn
    have hm := mul_nonneg (sub_nonneg.mpr (le_of_not_gt hn)) hden.le
    nlinarith only [hId, hm, hCross]
  have hH := xiExplicitHeight_ge_pole a a
  have hdeltaEq : a - 1 = delta := by dsimp only [a, delta]; ring
  rw [hdeltaEq] at hH
  have hL := xiExplicitLipschitz_nonneg a ha
  have hLow : 1 / delta <= xiExplicitHeight a a + r * xiExplicitLipschitz a := by
    have hh := mul_nonneg hr0.le hL
    linarith only [hH, hh]
  have hLowMul := mul_le_mul_of_nonneg_left hLow hf0.le
  change f * (1 / delta) <= effectiveMultiplicityConstant eps at hLowMul
  have hStep : 2 * delta < f := by linarith only [hdelta, hf]
  have hMul := mul_lt_mul_of_pos_right hStep (div_pos (by norm_num : (0 : Real) < 1) hd)
  have hTwo : 2 < f * (1 / delta) := by
    convert hMul using 1 <;> field_simp [hd.ne'] <;> ring
  exact hTwo.trans_le hLowMul

theorem effectiveMultiplicity_bound_gt_two (eps T : Real)
    (heps : 0 < eps) (hT : 2 <= T) :
    2 < (Real.sharpResolventCoefficient + eps) * Real.log T +
      effectiveMultiplicityConstant eps := by
  have hC := effectiveMultiplicityConstant_gt_two eps heps
  have hCoef : 0 <= Real.sharpResolventCoefficient + eps := by
    dsimp only [Real.sharpResolventCoefficient]
    positivity
  have hLog : 0 <= Real.log T := Real.log_nonneg (by linarith only [hT])
  have hProd := mul_nonneg hCoef hLog
  linarith only [hC, hProd]

theorem xiPairedLogTrace_effective_low (t : Real) (ht : 2 <= abs t) :
    (18 / 5) * (xiPairedLogTrace 2 t - (2 / 3) * xiPairedLogTrace 3 t) <=
      (3 / 5) * Real.log (abs t) + 4 / 5 := by
  have h0 := (xi_compensated_scalar_bound t ht).trans (compensatedXiScalar_low t ht)
  have ht1 : 2 <= abs (-t) := by simpa only [abs_neg] using ht
  have h1 := (xi_compensated_scalar_bound (-t) ht1).trans (compensatedXiScalar_low (-t) ht1)
  simp only [abs_neg] at h1
  dsimp only [xiPairedLogTrace]
  linarith only [h0, h1]

theorem xiPairedLogTrace_effective_high (t : Real) (ht : 6 <= abs t) :
    (18 / 5) * (xiPairedLogTrace 2 t - (2 / 3) * xiPairedLogTrace 3 t) <=
      (3 / 5) * Real.log (abs t) + 11 / 100 := by
  have ht2 : 2 <= abs t := by linarith only [ht]
  have h0 := (xi_compensated_scalar_bound t ht2).trans (compensatedXiScalar_high t ht)
  have ht1 : 6 <= abs (-t) := by simpa only [abs_neg] using ht
  have ht12 : 2 <= abs (-t) := by linarith only [ht1]
  have h1 := (xi_compensated_scalar_bound (-t) ht12).trans (compensatedXiScalar_high (-t) ht1)
  simp only [abs_neg] at h1
  dsimp only [xiPairedLogTrace]
  linarith only [h0, h1]

theorem zeta_multiplicity_le_effective_trace {w : Complex}
    (hw : And (0 < w.re) (w.re < 1)) :
    (analyticOrderNatAt riemannZeta w : Real) <=
      (18 / 5) * (xiPairedLogTrace 2 w.im - (2 / 3) * xiPairedLogTrace 3 w.im) := by
  have hStrip (p : RiemannXiDivisorZeroIndex) :
      abs ((riemannXiDivisorZeroValue p).re - 1 / 2) <= 1 / 2 := by
    have hp := BombieriVinogradov.SiegelWalfisz.riemannXiDivisorZeroValue_re_mem_Ioo p
    exact abs_le.mpr (And.intro (by linarith only [hp.1]) (by linarith only [hp.2]))
  have hPos : 2 * (1 / 2 : Real) <= Real.sqrt (2 ^ 2 - (1 / 2) ^ 2) +
      Real.sqrt (3 ^ 2 - (1 / 2) ^ 2) := by
    have hA := eulerSqrt_lower ((2 : Real) ^ 2 - (1 / 2) ^ 2) 1
      (by norm_num) (by norm_num) (by norm_num)
    have hB := Real.sqrt_nonneg ((3 : Real) ^ 2 - (1 / 2) ^ 2)
    linarith only [hA, hB]
  have hh := zeta_multiplicity_le_positive_strip_trace hw 2 3 (by norm_num) (by norm_num)
    (1 / 2) (by norm_num) (by norm_num) hPos hStrip
  norm_num only at hh
  linarith only [hh]

theorem zeta_multiplicity_effective_low {w : Complex}
    (hw : And (0 < w.re) (w.re < 1)) (ht : 2 <= abs w.im) :
    (analyticOrderNatAt riemannZeta w : Real) <= (3 / 5) * Real.log (abs w.im) + 4 / 5 :=
  (zeta_multiplicity_le_effective_trace hw).trans (xiPairedLogTrace_effective_low w.im ht)

theorem zeta_multiplicity_effective_high {w : Complex}
    (hw : And (0 < w.re) (w.re < 1)) (ht : 6 <= abs w.im) :
    (analyticOrderNatAt riemannZeta w : Real) <= (3 / 5) * Real.log (abs w.im) + 11 / 100 :=
  (zeta_multiplicity_le_effective_trace hw).trans (xiPairedLogTrace_effective_high w.im ht)

theorem zeta_simplicity_window {w : Complex} (hw : And (0 < w.re) (w.re < 1))
    (ht : 2 <= abs w.im) (hmax : abs w.im < Real.exp (63 / 20)) :
    analyticOrderNatAt riemannZeta w <= 1 := by
  have hm : (analyticOrderNatAt riemannZeta w : Real) < 2 := by
    by_cases hs : abs w.im <= 6
    next =>
      have hh := zeta_multiplicity_effective_low hw ht
      have hl := Real.log_le_log (by linarith only [ht] : 0 < abs w.im) hs
      have h6 := simplicity_log_six_lt_two
      linarith only [hh, hl, h6]
    next =>
      have hh := zeta_multiplicity_effective_high hw (le_of_lt (lt_of_not_ge hs))
      have hl := Real.log_lt_log (by linarith only [ht] : 0 < abs w.im) hmax
      rw [Real.log_exp] at hl
      linarith only [hh, hl]
  exact Nat.le_of_lt_succ (by exact_mod_cast hm)

end PrimeFactorOscillations

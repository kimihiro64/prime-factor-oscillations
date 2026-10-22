/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Exponents for positive log-Gaussian record probes

The exact spectral shift keeps the signed exponent difference. The
localization parameters tend to zero without losing the target exponent.
The full contour identity and every-real-cutoff prime-counting consumer
are proved by the maintained GaussianUniformZeroResponse chain; this
module supplies the scalar exponent comparisons consumed there.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.PrimeClassDeletion

noncomputable def gaussianZeroExponent (c beta gamma tau : Real) : Real :=
  beta + c / 2 * (beta ^ 2 - (gamma - tau) ^ 2)

theorem gaussianZeroExponent_at_height (c beta gamma : Real) :
    gaussianZeroExponent c beta gamma gamma = beta + c / 2 * beta ^ 2 := by
  unfold gaussianZeroExponent
  ring

theorem gaussianZeroExponent_shift (c beta gamma tau : Real) :
    gaussianZeroExponent c beta gamma tau - gaussianZeroExponent c beta gamma 0 =
      c * tau * (2 * gamma - tau) / 2 := by
  unfold gaussianZeroExponent
  ring

theorem gaussianZeroExponent_increases_from_zero (c beta gamma tau : Real)
    (hc : 0 < c) (ht : 0 < tau) (htg : tau < 2 * gamma) :
    gaussianZeroExponent c beta gamma 0 < gaussianZeroExponent c beta gamma tau := by
  have hpos : 0 < c * tau * (2 * gamma - tau) / 2 :=
    div_pos (mul_pos (mul_pos hc ht) (sub_pos.mpr htg)) (by norm_num)
  have h := gaussianZeroExponent_shift c beta gamma tau
  linarith only [h, hpos]

theorem gaussianZeroExponent_beta_difference (c b1 b2 gamma tau : Real) :
    gaussianZeroExponent c b2 gamma tau - gaussianZeroExponent c b1 gamma tau =
      (b2 - b1) * (1 + c / 2 * (b1 + b2)) := by
  unfold gaussianZeroExponent
  ring

theorem gaussianZeroExponent_strictMono_beta (c b1 b2 gamma tau : Real)
    (hc : 0 <= c) (hb1 : 0 <= b1) (hb : b1 < b2) :
    gaussianZeroExponent c b1 gamma tau < gaussianZeroExponent c b2 gamma tau := by
  have hsum : 0 <= b1 + b2 := by linarith only [hb1, hb]
  have hprod := mul_nonneg (div_nonneg hc (by norm_num : (0 : Real) <= 2)) hsum
  have hfactor : 0 < 1 + c / 2 * (b1 + b2) := by linarith only [hprod]
  have hpos := mul_pos (sub_pos.mpr hb) hfactor
  have h := gaussianZeroExponent_beta_difference c b1 b2 gamma tau
  linarith only [h, hpos]

theorem gaussianZeroExponent_bad_signal (c beta gamma : Real)
    (hc : 0 < c) (hb : (1 / 2 : Real) < beta) :
    (1 / 2 : Real) + c / 8 < gaussianZeroExponent c beta gamma gamma := by
  rw [gaussianZeroExponent_at_height]
  have hsum : 0 < beta + (1 / 2 : Real) := by linarith only [hb]
  have hs := mul_pos (sub_pos.mpr hb) hsum
  have hp := mul_pos hc hs
  nlinarith only [hb, hp]

/-- Cross multiplication of the upper-tail exponent; division requires
a positive a, supplied by the next existence theorem. -/
theorem gaussianTail_localization_cross (a : Real) :
    (2 * a ^ 2) * (1 + a ^ 2 / 2) - (a ^ 2 + 2 * a - a ^ 2) ^ 2 =
      (2 * a ^ 2) * (-1 + a ^ 2 / 2) := by
  ring

theorem exists_gaussian_localizer (epsilon : Real) (he : 0 < epsilon) :
    Exists fun a : Real =>
      0 < a /\ a < 1 / 4 /\ a ^ 2 + 2 * a < epsilon := by
  let a : Real := min (epsilon / 8) (1 / 8)
  have ha : 0 < a := lt_min (div_pos he (by norm_num)) (by norm_num)
  have hsmall : a <= (1 / 8 : Real) := min_le_right _ _
  have heighth : a <= epsilon / 8 := min_le_left _ _
  have hsquare := mul_nonneg ha.le (sub_nonneg.mpr hsmall)
  refine Exists.intro a (And.intro ha (And.intro ?_ ?_))
  . linarith only [hsmall]
  . nlinarith only [he, heighth, hsquare]

/-- The positive-denominator exponent comparison used after localization. -/
theorem gaussian_localized_exponent_cross (beta epsilon kappa : Real)
    (hb : beta <= 1) (he : 0 < epsilon)
    (hk : 0 <= kappa) (hke : kappa < epsilon) :
    0 < 1 + kappa /\ (beta - epsilon) * (1 + kappa) < beta := by
  have hfirst := mul_nonneg hk (sub_nonneg.mpr hb)
  have hsecond := mul_nonneg he.le hk
  exact And.intro (by linarith only [hk])
    (by nlinarith only [hfirst, hsecond, hke])

end PrimeFactorOscillations.PrimeClassDeletion

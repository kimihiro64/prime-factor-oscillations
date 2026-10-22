/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Proof.PrimeClassDeletion.GaussianFiniteEnvelope

/-!
# A positive Gaussian shift with the complete strict gain

Starting from any zero to the right of one half, a concrete positive
shift beats the unshifted envelope, the prime-power exponent, and the
original zero real part simultaneously. All zero-set maxima are actual.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.PrimeClassDeletion

theorem gaussianZeroExponent_strict_shift_gain
    (c : Real) (hc : 0 < c) (z0 : ZetaDistinctZero)
    (hBeta : (1 / 2 : Real) < z0.val.re) :
    Exists fun tau : Real => Exists fun w : ZetaDistinctZero =>
      And (0 < tau)
        (And (gaussianZetaEnvelope c 0 < gaussianZeroExponent c w.val.re w.val.im tau)
          (And ((1 / 2 : Real) + c / 8 < gaussianZeroExponent c w.val.re w.val.im tau)
            (z0.val.re < gaussianZeroExponent c w.val.re w.val.im tau))) := by
  let b : Real := z0.val.re + c / 2 * z0.val.re ^ 2
  have hExtra : 0 < c / 2 * z0.val.re ^ 2 :=
    mul_pos (div_pos hc (by norm_num)) (pow_pos z0.property.2.1 2)
  have hBetaB : z0.val.re < b := by
    dsimp only [b]
    linarith only [hExtra]
  have hPowerB : (1 / 2 : Real) + c / 8 < b := by
    simpa only [gaussianZeroExponent_at_height, b] using
      gaussianZeroExponent_bad_signal c z0.val.re z0.val.im hc hBeta
  by_cases hBase : gaussianZetaEnvelope c 0 < b
  . cases zetaDistinctZero_exists_positive_height z0 with
    | intro w hw =>
      have hAt : gaussianZeroExponent c w.val.re w.val.im w.val.im = b := by
        rw [gaussianZeroExponent_at_height, hw.1]
      refine Exists.intro w.val.im (Exists.intro w (And.intro hw.2.2 ?_))
      rw [hAt]
      exact And.intro hBase (And.intro hPowerB hBetaB)
  . have hBaseLe : b <= gaussianZetaEnvelope c 0 := le_of_not_gt hBase
    cases gaussianZetaEnvelope_attained c 0 hc z0 with
    | intro v hv =>
      cases zetaDistinctZero_exists_positive_height v with
      | intro w hw =>
        have hZero : gaussianZeroExponent c w.val.re w.val.im 0 =
            gaussianZetaEnvelope c 0 := by
          rw [hv.1]
          unfold gaussianZeroExponent
          simp only [sub_zero]
          rw [hw.1, hw.2.1]
        have hIncrease := gaussianZeroExponent_increases_from_zero c w.val.re w.val.im
          w.val.im hc hw.2.2 (by linarith only [hw.2.2])
        have hGain : gaussianZetaEnvelope c 0 <
            gaussianZeroExponent c w.val.re w.val.im w.val.im := by
          rw [<- hZero]
          exact hIncrease
        exact Exists.intro w.val.im (Exists.intro w
          (And.intro hw.2.2 (And.intro hGain
            (And.intro ((lt_of_lt_of_le hPowerB hBaseLe).trans hGain)
              ((lt_of_lt_of_le hBetaB hBaseLe).trans hGain)))))

end PrimeFactorOscillations.PrimeClassDeletion

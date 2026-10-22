/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Proof.PrimeClassDeletion.GaussianThetaBounds

/-!
# The complete signed lower bound for the coupled theta probe

The exposed principal residue survives. Every other allowance is
explicit, including the unshifted zero envelope and both physical
and prime-power errors. The two probes are actual integrals.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.PrimeClassDeletion

theorem logGaussianThetaProbe_coupled_signed_lower_bound
    (c tau : Real) (hc : 0 < c) (w : ZetaDistinctZero)
    (hUnique : forall z : ZetaDistinctZero, Not (z = w) ->
      gaussianZeroExponent c z.val.re z.val.im tau <
        gaussianZeroExponent c w.val.re w.val.im tau) :
    Exists fun delta : Real => And (0 < delta) (And (delta <= 1)
      (Exists fun C1 : Real => And (0 <= C1)
        (Exists fun C0 : Real => And (0 <= C0)
          (forall X : Real, Real.exp (1 / c) <= X -> Real.exp 1 <= X ->
            gaussianZetaAmplitude w *
                X ^ (gaussianZeroExponent c w.val.re w.val.im tau) -
              C1 * X ^ (gaussianZeroExponent c w.val.re w.val.im tau - delta) -
              C0 * X ^ (gaussianZetaEnvelope c 0) -
              2 * abs (Real.log (2 * Real.pi)) -
              (logGaussianExplicitErrorConstant tau + logGaussianExplicitErrorConstant 0) *
                X ^ (-1 + c / 2) -
              (4 * (2 + c / 2 + 2 * c / Real.pi)) *
                X ^ (1 / 2 + c / 8) * Real.log X <=
              (logGaussianThetaProbe X (c * Real.log X) 0).re +
                norm (logGaussianThetaProbe X (c * Real.log X) tau))))) := by
  cases logGaussianZetaResidue_uniform_dominance c tau hc w hUnique with
  | intro delta hd =>
    cases hd.2.2 with
    | intro C1 hC1 =>
      cases logGaussianZetaResidue_envelope_norm_bound c 0 hc w with
      | intro C0 hC0 =>
        refine Exists.intro delta (And.intro hd.1 (And.intro hd.2.1
          (Exists.intro C1 (And.intro hC1.1
            (Exists.intro C0 (And.intro hC0.1 ?_))))))
        intro X hBase hExp
        have hX1 : 1 <= X := by
          have he : (1 : Real) <= Real.exp 1 := by
            simpa only [Real.exp_zero] using
              (Real.exp_le_exp.mpr (by norm_num : (0 : Real) <= 1))
          exact he.trans hExp
        have hXPos : 0 < X := lt_of_lt_of_le Real.zero_lt_one hX1
        have hLog : 1 <= Real.log X := by
          have h := Real.log_le_log (Real.exp_pos 1) hExp
          simpa only [Real.log_exp] using h
        have hV : 1 <= c * Real.log X := by
          have h := mul_le_mul_of_nonneg_left
            (Real.log_le_log (Real.exp_pos (1 / c)) hBase) hc.le
          rw [Real.log_exp] at h
          have hUnit : c * (1 / c) = 1 := by field_simp [hc.ne']
          rw [hUnit] at h
          exact h
        let V : Real := c * Real.log X
        let S0 : Complex := tsum (logGaussianZetaResidue X V 0)
        let St : Complex := tsum (logGaussianZetaResidue X V tau)
        let H0 : Complex := logGaussianThetaProbe X V 0
        let Ht : Complex := logGaussianThetaProbe X V tau
        have hMain := (hC1.2 X hBase).2
        have hZero := hC0.2 X hBase
        have hError0 := logGaussianThetaProbe_log_scale_error X c 0 hX1 hLog hc hV
        have hErrort := logGaussianThetaProbe_log_scale_error X c tau hX1 hLog hc hV
        have hShift : norm St <= norm Ht + norm (Ht + St) := by
          calc
            _ = norm ((Ht + St) - Ht) := by congr 1; ring
            _ <= norm (Ht + St) + norm Ht := norm_sub_le _ _
            _ = _ := by ring
        have hUnshift : norm H0 <= norm S0 + norm (H0 + S0) := by
          calc
            _ = norm ((H0 + S0) - S0) := by congr 1; ring
            _ <= norm (H0 + S0) + norm S0 := norm_sub_le _ _
            _ = _ := by ring
        have hReal : -norm H0 <= H0.re :=
          (abs_le.mp (Complex.abs_re_le_norm H0)).1
        change _ <= H0.re + norm Ht
        change _ <= norm St at hMain
        change norm S0 <= _ at hZero
        change norm (H0 + S0) <= _ at hError0
        change norm (Ht + St) <= _ at hErrort
        linarith only [hMain, hZero, hError0, hErrort, hShift, hUnshift, hReal]

end PrimeFactorOscillations.PrimeClassDeletion

/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.LogGaussianDistinctZeroFormula
import PrimeFactorOscillations.Helpers.LogGaussianPrimePowerScale
import PrimeFactorOscillations.Helpers.XiZetaFactor

/-!
# The complete Gaussian formula over distinct nontrivial zeta zeros

The actual physical integral, analytic zeta multiplicities, absolute
convergence, signed residue series and uniform prime-power error all
occur in the same unconditional statement.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.PrimeClassDeletion

abbrev ZetaDistinctZero := {s : Complex //
  And (riemannZeta s = 0) (And (0 < s.re) (s.re < 1))}

def xiDistinctZeroEquivZeta : Equiv XiDistinctZero ZetaDistinctZero where
  toFun z := Subtype.mk z.val ((riemannXi_zero_iff_nontrivial_zeta_zero z.val).mp z.property)
  invFun z := Subtype.mk z.val ((riemannXi_zero_iff_nontrivial_zeta_zero z.val).mpr z.property)
  left_inv z := Subtype.ext (Eq.refl z.val)
  right_inv z := Subtype.ext (Eq.refl z.val)

noncomputable def logGaussianZetaResidue
    (X V tau : Real) (z : ZetaDistinctZero) : Complex :=
  ((analyticOrderAt riemannZeta z.val).toNat : Complex) / z.val * (X : Complex) ^ z.val *
    Complex.exp ((V : Complex) / 2 * (z.val - (tau : Complex) * Complex.I) ^ 2)

theorem logGaussian_zeta_zero_residue_hasSum
    (X V tau : Real) (hX : 0 < X) (hV : 1 <= V) :
    HasSum (logGaussianZetaResidue X V tau)
      (tsum (fun p : RiemannXiDivisorZeroIndex =>
        logGaussianZeroResidue X V tau (riemannXiDivisorZeroValue p))) := by
  apply xiDistinctZeroEquivZeta.hasSum_iff.mp
  convert logGaussian_distinct_zero_residue_hasSum X V tau hX hV using 1
  funext z
  have hs := (riemannXi_zero_iff_nontrivial_zeta_zero z.val).mp z.property
  have hOne : Not (z.val = 1) := by
    intro h
    have hRe := hs.2.2
    rw [h, Complex.one_re] at hRe
    exact (lt_irrefl 1) hRe
  change ((analyticOrderAt riemannZeta z.val).toNat : Complex) / z.val *
      (X : Complex) ^ z.val *
      Complex.exp ((V : Complex) / 2 * (z.val - (tau : Complex) * Complex.I) ^ 2) =
    (xiZeroMultiplicity z.val : Complex) / z.val * (X : Complex) ^ z.val *
      Complex.exp ((V : Complex) / 2 * (z.val - (tau : Complex) * Complex.I) ^ 2)
  rw [xiZeroMultiplicity_eq_zetaOrder hs.2.1 hOne]
  rfl

theorem logGaussian_zeta_zero_residue_abs_summable
    (X V tau : Real) (hX : 0 < X) (hV : 1 <= V) :
    Summable (fun z : ZetaDistinctZero => norm (logGaussianZetaResidue X V tau z)) :=
  (logGaussian_zeta_zero_residue_hasSum X V tau hX hV).summable.norm

theorem logGaussianPsiProbe_eq_zeta_zero_formula
    (X V tau : Real) (hX : 0 < X) (hV : 1 <= V) :
    logGaussianPsiProbe X V tau =
      -tsum (logGaussianZetaResidue X V tau) -
      (Real.log (2 * Real.pi) : Complex) * (Real.exp (-V * tau ^ 2 / 2) : Complex) +
      logGaussianExplicitRemainder X V tau := by
  rw [logGaussianPsiProbe_eq_explicit_formula X V tau hX hV,
    <- (logGaussian_zeta_zero_residue_hasSum X V tau hX hV).tsum_eq]

theorem logGaussian_signed_zeta_explicit_with_prime_powers
    (X c tau : Real) (hX : 1 < X) (hc : 0 < c) (hV : 1 <= c * Real.log X) :
    And
      (Summable (fun z : ZetaDistinctZero =>
        norm (logGaussianZetaResidue X (c * Real.log X) tau z)))
      (And
        (logGaussianPsiProbe X (c * Real.log X) tau =
          -tsum (logGaussianZetaResidue X (c * Real.log X) tau) -
          (Real.log (2 * Real.pi) : Complex) *
            (Real.exp (-(c * Real.log X) * tau ^ 2 / 2) : Complex) +
          logGaussianExplicitRemainder X (c * Real.log X) tau)
        (And
          (norm (logGaussianExplicitRemainder X (c * Real.log X) tau) <=
            logGaussianExplicitErrorConstant tau * X ^ (-1 + c / 2))
          (norm (logGaussianPsiProbe X (c * Real.log X) tau -
            logGaussianThetaProbe X (c * Real.log X) tau) <=
            2 * Real.sqrt X * Real.exp ((c * Real.log X) / 8) *
              (Real.log X + (c * Real.log X) / 2 +
                Real.sqrt (2 * (c * Real.log X) / Real.pi))))) := by
  have hXPos : 0 < X := lt_trans Real.zero_lt_one hX
  have hVPos : 0 < c * Real.log X := mul_pos hc (Real.log_pos hX)
  exact And.intro
    (logGaussian_zeta_zero_residue_abs_summable X (c * Real.log X) tau hXPos hV)
    (And.intro
      (logGaussianPsiProbe_eq_zeta_zero_formula X (c * Real.log X) tau hXPos hV)
      (And.intro
        (logGaussianExplicitRemainder_log_scale_bound X c tau hXPos hV)
        (logGaussian_prime_power_correction_bound X (c * Real.log X) tau hX.le hVPos)))

end PrimeFactorOscillations.PrimeClassDeletion

/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.LogGaussianExplicitFormula
import PrimeFactorOscillations.Helpers.XiDistinctZeroSums

/-!
# The actual Gaussian explicit formula grouped by distinct zero

The coefficient at each distinct zero is its analytic multiplicity
divided by that zero. The full signed sum and explicit error are retained.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.PrimeClassDeletion

theorem logGaussian_distinct_zero_residue_hasSum
    (X V tau : Real) (hX : 0 < X) (hV : 1 <= V) :
    HasSum (fun z : XiDistinctZero =>
      (xiZeroMultiplicity z.val : Complex) / z.val * (X : Complex) ^ z.val *
        Complex.exp ((V : Complex) / 2 * (z.val - (tau : Complex) * Complex.I) ^ 2))
      (tsum (fun p : RiemannXiDivisorZeroIndex =>
        logGaussianZeroResidue X V tau (riemannXiDivisorZeroValue p))) := by
  have h := xiDistinctZero_weighted_hasSum (logGaussianZeroResidue X V tau)
    (logGaussian_zero_residue_xi_summable X V tau hX hV)
  convert h using 1
  funext z
  dsimp only [logGaussianZeroResidue]
  ring

theorem logGaussian_distinct_zero_residue_abs_summable
    (X V tau : Real) (hX : 0 < X) (hV : 1 <= V) :
    Summable (fun z : XiDistinctZero =>
      norm ((xiZeroMultiplicity z.val : Complex) / z.val * (X : Complex) ^ z.val *
        Complex.exp ((V : Complex) / 2 * (z.val - (tau : Complex) * Complex.I) ^ 2))) :=
  (logGaussian_distinct_zero_residue_hasSum X V tau hX hV).summable.norm

theorem logGaussianPsiProbe_eq_distinct_zero_formula
    (X V tau : Real) (hX : 0 < X) (hV : 1 <= V) :
    logGaussianPsiProbe X V tau =
      -tsum (fun z : XiDistinctZero =>
        (xiZeroMultiplicity z.val : Complex) / z.val * (X : Complex) ^ z.val *
          Complex.exp ((V : Complex) / 2 * (z.val - (tau : Complex) * Complex.I) ^ 2)) -
      (Real.log (2 * Real.pi) : Complex) * (Real.exp (-V * tau ^ 2 / 2) : Complex) +
      logGaussianExplicitRemainder X V tau := by
  rw [logGaussianPsiProbe_eq_explicit_formula X V tau hX hV,
    <- (logGaussian_distinct_zero_residue_hasSum X V tau hX hV).tsum_eq]

end PrimeFactorOscillations.PrimeClassDeletion

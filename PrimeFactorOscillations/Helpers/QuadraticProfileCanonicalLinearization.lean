/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.QuadraticProfileGenerating
import PrimeFactorOscillations.Helpers.QuadraticProfileLinearization

/-!
# Uniform Nicolas linearization of the actual family ratio

Both coefficient denominators are proved positive. The dimension nu remains
in the reference clock and in the signed signal; no finite asymptotic
truncation replaces the entire profile.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.QuadraticPrimeLaw

open Filter Robin1984

theorem exists_eventually_densityRatio_linearization (law : QuadraticPrimeLaw)
    (b : Real) (hb : 0 < b) :
    exists r0 : Nat, exists K : Real, 0 < r0 /\ 0 <= K /\
      Filter.Eventually (fun N : Nat =>
        1 < Chebyshev.theta (N : Real) /\ 2 <= law.referenceClock N /\
        forall r : Nat, r0 <= r -> (r : Real) / law.referenceClock N <= b ->
          0 < law.prefixEsymm N r /\
          0 < Nat.factorialConvolution law.realCoefficient r (law.referenceClock N) /\
          abs (law.densityRatio N r - law.referenceRatio r (law.referenceClock N) -
            ((r : Real) / (law.referenceClock N) ^ 2) *
              (law.nu * nicolasLogMertensOscillation (N : Real))) <=
            K * (abs (law.nu * nicolasLogMertensOscillation (N : Real)) /
              (law.referenceClock N) ^ 2 + 1 / ((r : Real) * (N : Real)))) atTop := by
  choose r0 N0 K hr0 hN0 hK hBound using law.exists_prefixProfile_ratio_linearization b hb
  have hNear : Tendsto (fun N => abs (law.arithmeticClock N - law.referenceClock N))
      atTop (nhds 0) := by
    simpa only [abs_zero] using law.tendsto_clock_difference_zero.abs
  refine Exists.intro r0 (Exists.intro K (And.intro hr0 (And.intro hK ?_)))
  filter_upwards [eventually_ge_atTop N0,
    tendsto_primeProfile_theta_atTop.eventually_gt_atTop 1,
    law.tendsto_referenceClock_atTop.eventually_ge_atTop 2,
    hNear.eventually_lt_const (by norm_num : (0 : Real) < 1)] with N hN hTheta hL hAbs
  refine And.intro hTheta (And.intro hL ?_)
  intro r hr hRange
  have h := hBound r hr N hN (law.arithmeticClock N) (law.referenceClock N) hL hAbs.le hRange
  simpa only [law.prefix_factorialConvolution_eq_esymm,
    law.clock_difference_eq_nicolas N hTheta, densityRatio, referenceRatio] using h

end PrimeFactorOscillations.QuadraticPrimeLaw

/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.AffinePrimeRH
import PrimeFactorOscillations.Helpers.ReciprocalSmoothRatioRH

/-!
# Actual affine prime-pair prefix-mass criteria for RH

The exact residue law includes every exceptional prime. The only displayed
rank parameter is positive; there is no prime-gap, short-interval, or RH
assumption in the family qualification. Arithmetic sampling remains the
separate fixed-prime limiting theorem already established for these laws.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.AffineSumFamily

theorem riemannHypothesis_iff_eventually_prefixMass_ratio
    (F : AffineSumFamily) (alpha : Real) (ha : 0 < alpha) :
    RiemannHypothesis <-> Filter.Eventually (fun N : Nat =>
      let L := (F.arity : Real) * (Real.eulerMascheroniConstant +
        Real.log (Real.log (Chebyshev.theta (N : Real))))
      let r := Nat.floor (alpha * L)
      let s := @List.map Nat.Primes Real (fun p : Nat.Primes => F.localProbability (p : Nat))
        (primeProfilePrefixSet N).toList
      List.bernoulliMass s (s.count 1 + r - 1) / List.bernoulliMass s (s.count 1 + r) <
        F.reciprocalSmoothLaw.quadraticPrimeLaw.referenceRatio r L) Filter.atTop := by
  exact F.reciprocalSmoothLaw.riemannHypothesis_iff_eventually_prefixMass_ratio alpha ha

theorem riemannHypothesis_iff_eventually_prefixMass_ratio_le
    (F : AffineSumFamily) (alpha : Real) (ha : 0 < alpha) :
    RiemannHypothesis <-> Filter.Eventually (fun N : Nat =>
      let L := (F.arity : Real) * (Real.eulerMascheroniConstant +
        Real.log (Real.log (Chebyshev.theta (N : Real))))
      let r := Nat.floor (alpha * L)
      let s := @List.map Nat.Primes Real (fun p : Nat.Primes => F.localProbability (p : Nat))
        (primeProfilePrefixSet N).toList
      List.bernoulliMass s (s.count 1 + r - 1) / List.bernoulliMass s (s.count 1 + r) <=
        F.reciprocalSmoothLaw.quadraticPrimeLaw.referenceRatio r L) Filter.atTop := by
  exact F.reciprocalSmoothLaw.riemannHypothesis_iff_eventually_prefixMass_ratio_le alpha ha

end PrimeFactorOscillations.AffineSumFamily

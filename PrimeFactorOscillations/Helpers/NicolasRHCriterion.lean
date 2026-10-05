/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.NicolasCanonicalSign
import PrimeFactorOscillations.Helpers.NicolasNegativeLimit

/-!
# RH and the actual theta-centered moving-rank density ratio

For each fixed alpha > 0, the eventual strict comparison with the canonical
entire-profile reference is equivalent to RH. This is a centered comparison,
not a theorem supplying bounded gaps or raw prime-factor-density ascents.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations

theorem eventually_densityRatio_thetaClock_lt_reference_of_RH
    (hRH : RiemannHypothesis) (alpha : Real) (ha : 0 < alpha) :
    Filter.Eventually (fun N : Nat =>
      let L := Real.eulerMascheroniConstant +
        Real.log (Real.log (Chebyshev.theta (N : Real)))
      let r := Nat.floor (alpha * L)
      (PrimeFactorUnimodality.densityRatio
        (PrimeFactorUnimodality.primesBelow (N + 1)) r : Real) <
        Nat.factorialConvolution primeProfileRealCoefficient (r - 1) L /
          Nat.factorialConvolution primeProfileRealCoefficient r L) Filter.atTop := by
  choose C _hC hSign using exists_eventually_densityRatio_thetaClock_sign alpha ha
  have hNegative := eventually_nicolasLog_nat_lt_neg_div_of_RH hRH C
  filter_upwards [hSign, hNegative] with N hCompare hNeg
  rw [nicolasLog_nat_eq_primeProfile_clock_difference N hCompare.1] at hNeg
  exact hCompare.2.2.2.2.2 hNeg

theorem riemannHypothesis_iff_eventually_densityRatio_thetaClock_lt_reference
    (alpha : Real) (ha : 0 < alpha) :
    RiemannHypothesis <-> Filter.Eventually (fun N : Nat =>
      let L := Real.eulerMascheroniConstant +
        Real.log (Real.log (Chebyshev.theta (N : Real)))
      let r := Nat.floor (alpha * L)
      (PrimeFactorUnimodality.densityRatio
        (PrimeFactorUnimodality.primesBelow (N + 1)) r : Real) <
        Nat.factorialConvolution primeProfileRealCoefficient (r - 1) L /
          Nat.factorialConvolution primeProfileRealCoefficient r L) Filter.atTop := by
  constructor
  . intro hRH
    exact eventually_densityRatio_thetaClock_lt_reference_of_RH hRH alpha ha
  . intro hEvent
    exact riemannHypothesis_of_eventually_densityRatio_thetaClock_lt_reference
      alpha ha hEvent

end PrimeFactorOscillations

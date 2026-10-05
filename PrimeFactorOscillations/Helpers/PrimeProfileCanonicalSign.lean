/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.PrimeProfileCanonical
import PrimeFactorOscillations.Helpers.PrimeProfileMovingClockSign
import PrimeFactorOscillations.Helpers.PrimeProfileThetaClock

/-!
# Canonical density-ratio comparison at the theta clock

For each positive fixed rank parameter, the actual Erdos 690 density ratio
has the sign of the difference of the actual clocks outside a uniform C/N
error window. All clock limits and denominator positivity are discharged.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations

theorem exists_eventually_densityRatio_thetaClock_sign
    (alpha : Real) (ha : 0 < alpha) :
    exists C : Real, 0 <= C /\ Filter.Eventually (fun N : Nat =>
      let L := Real.eulerMascheroniConstant +
        Real.log (Real.log (Chebyshev.theta (N : Real)))
      let B := (primeProfilePrefixSet N).sum
        (fun p => Real.log (1 + primeProfileWeight (p : Nat)))
      let r := Nat.floor (alpha * L)
      let D := (PrimeFactorUnimodality.densityRatio
        (PrimeFactorUnimodality.primesBelow (N + 1)) r : Real)
      let RR := Nat.factorialConvolution primeProfileRealCoefficient (r - 1) L /
        Nat.factorialConvolution primeProfileRealCoefficient r L
      1 < Chebyshev.theta (N : Real) /\ 0 < r /\
        0 < (PrimeFactorUnimodality.weightEsymm
          (PrimeFactorUnimodality.primesBelow (N + 1)) r : Real) /\
        0 < Nat.factorialConvolution primeProfileRealCoefficient r L /\
        (C / (N : Real) < L - B -> RR < D) /\
        (L - B < -C / (N : Real) -> D < RR)) Filter.atTop := by
  let B : Nat -> Real := fun N => (primeProfilePrefixSet N).sum
    (fun p => Real.log (1 + primeProfileWeight (p : Nat)))
  let L : Nat -> Real := fun N => Real.eulerMascheroniConstant +
    Real.log (Real.log (Chebyshev.theta (N : Real)))
  have hL : Filter.Tendsto L Filter.atTop Filter.atTop :=
    tendsto_primeProfile_thetaClock_atTop
  have hBL : Filter.Tendsto (fun N => B N - L N) Filter.atTop (nhds 0) :=
    tendsto_primePrefixProfile_logSum_sub_thetaClock
  obtain hs := exists_eventually_primePrefixProfile_moving_floor_sign alpha ha B L hL hBL
  choose C hC hevent using hs
  refine Exists.intro C (And.intro hC ?_)
  have htheta := tendsto_primeProfile_theta_atTop.eventually_gt_atTop (1 : Real)
  apply (hevent.and htheta).mono
  intro N hBoth
  have hN := hBoth.1
  let r := Nat.floor (alpha * L N)
  have hfinite : 0 < (PrimeFactorUnimodality.weightEsymm
      (PrimeFactorUnimodality.primesBelow (N + 1)) r : Real) := by
    rw [<- primePrefixProfile_factorialConvolution_eq_weightEsymm N r]
    exact hN.2.1
  refine And.intro hBoth.2 (And.intro hN.1
    (And.intro hfinite (And.intro hN.2.2.1 (And.intro ?_ ?_))))
  . intro hF
    rw [densityRatio_eq_primePrefixProfile_factorialConvolution]
    exact hN.2.2.2.1 hF
  . intro hF
    rw [densityRatio_eq_primePrefixProfile_factorialConvolution]
    exact hN.2.2.2.2 hF

end PrimeFactorOscillations

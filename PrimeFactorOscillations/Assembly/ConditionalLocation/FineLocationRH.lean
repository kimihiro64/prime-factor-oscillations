/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.ConditionalLocation.LastAscentFineTracking
import PrimeFactorOscillations.Helpers.IntegerClockWave

/-!
# Actual last-ascent tracking and its RH wave

Constructs the reference roots and combines the full local-coverage proof
with the RH wave, retaining all arithmetic hypotheses explicitly.
-/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace PrimeFactorOscillations
open Filter
open PrimeFactorUnimodality

/-- Full local-coverage consumer: the reference roots are constructed,
the actual last ascent is tracked on its square-root scale, and RH supplies
the complete wave at the unchanged endpoint P-1. -/
theorem exists_last_ascent_reference_tracking_and_RH_wave (H : Nat) (hH : 2 <= H)
    (hMin : Filter.Eventually (fun i : Nat => H <= primeGap i) atTop)
    (hCoverage : Filter.Eventually (fun x : Real => exists i : Nat,
      x < (primeAt i : Real) /\ (primeAt i : Real) <= x + gapCoverageLength x /\
      primeGap i = H) atTop) :
    exists A : Real, exists u : Nat -> Real, 0 < A /\
      Filter.Eventually (fun r : Nat =>
        abs (u r - (r : Real) / ((H : Real) + 1)) <= A /\
        (0 < u r /\ ((H : Real) + 1) / 2 <= (r : Real) / u r /\
          (r : Real) / u r <= 2 * ((H : Real) + 1)) /\
        Nat.factorialConvolution primeProfileRealCoefficient (r - 1) (u r) /
          Nat.factorialConvolution primeProfileRealCoefficient r (u r) = (H : Real) + 1) atTop /\
      Tendsto (fun k : Nat =>
        (Real.exp (Real.exp (u (k - 1) - Real.eulerMascheroniConstant)) -
          nicolasPrimeProductClock (lastAscentPrime (ordinaryDensity k) - 1 : Nat)) /
            Real.sqrt (lastAscentPrime (ordinaryDensity k))) atTop (nhds 0) /\
      (RiemannHypothesis -> Tendsto (fun k : Nat =>
        (Real.exp (Real.exp (u (k - 1) - Real.eulerMascheroniConstant)) -
          Chebyshev.theta (lastAscentPrime (ordinaryDensity k) - 1 : Nat)) /
            Real.sqrt (lastAscentPrime (ordinaryDensity k)) -
          (2 + nicolasZeroWave (lastAscentPrime (ordinaryDensity k) - 1 : Nat)))
        atTop (nhds 0)) := by
  have hs : 0 < (H : Real) + 1 := by positivity
  choose A u hA hRoot using exists_primeProfile_reference_root_sequence ((H : Real) + 1) hs
  have hTrack := tendsto_last_ascent_reference_clock_error H hH hMin hCoverage u
    (hRoot.mono (fun r hr => hr.2))
  refine Exists.intro A (Exists.intro u (And.intro hA (And.intro hRoot
    (And.intro hTrack ?_))))
  intro hRH
  exact tendsto_integer_clock_reference_wave
    (fun k => lastAscentPrime (ordinaryDensity k))
    (fun k => Real.exp (Real.exp (u (k - 1) - Real.eulerMascheroniConstant)))
    (tendsto_last_ascent_of_local_gap_coverage H hH hMin hCoverage) hTrack hRH

end PrimeFactorOscillations

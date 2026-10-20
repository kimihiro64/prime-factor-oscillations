/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.PrimeProfileClockShift

/-!
# Canonical clocks for the shared positive-excursion comparison

The past reference clock L(M-H) matches the larger actual prefix M.
These limits feed the signed lower sandwich for every bounded permutation.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations

open Filter

/-- A fixed past shift retains divergence of the canonical reference clock. -/
theorem tendsto_canonical_past_referenceClock_atTop (H : Nat) :
    Tendsto (fun M => canonicalPrimeOddsLaw.referenceClock (M - H)) atTop atTop := by
  have hsub : Tendsto (fun M : Nat => M - H) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    exact (eventually_ge_atTop (b + H)).mono (fun M hM => by omega)
  exact canonicalPrimeOddsLaw.tendsto_referenceClock_atTop.comp hsub

/-- The larger prefix clock differs from the past canonical reference by o(1). -/
theorem tendsto_canonical_past_clock_difference_zero (H : Nat) :
    Tendsto (fun M => canonicalPrimeOddsLaw.arithmeticClock M -
      canonicalPrimeOddsLaw.referenceClock (M - H)) atTop (nhds 0) := by
  have hsub : Tendsto (fun M : Nat => M - H) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    exact (eventually_ge_atTop (b + H)).mono (fun M hM => by omega)
  have hinc0 := (tendsto_canonical_arithmeticClock_increment_zero H).comp hsub
  have hinc : Tendsto (fun M => canonicalPrimeOddsLaw.arithmeticClock M -
      canonicalPrimeOddsLaw.arithmeticClock (M - H)) atTop (nhds 0) := by
    have heq : Filter.EventuallyEq atTop
        (fun M : Nat => canonicalPrimeOddsLaw.arithmeticClock (M - H + H) -
          canonicalPrimeOddsLaw.arithmeticClock (M - H))
        (fun M => canonicalPrimeOddsLaw.arithmeticClock M -
          canonicalPrimeOddsLaw.arithmeticClock (M - H)) := by
      filter_upwards [eventually_ge_atTop H] with M hM
      rw [Nat.sub_add_cancel hM]
    exact (Filter.tendsto_congr' heq).mp hinc0
  have h := (canonicalPrimeOddsLaw.tendsto_clock_difference_zero.comp hsub).add hinc
  have hsame : (fun M : Nat =>
      (canonicalPrimeOddsLaw.arithmeticClock (M - H) -
        canonicalPrimeOddsLaw.referenceClock (M - H)) +
      (canonicalPrimeOddsLaw.arithmeticClock M -
        canonicalPrimeOddsLaw.arithmeticClock (M - H))) =
      (fun M => canonicalPrimeOddsLaw.arithmeticClock M -
        canonicalPrimeOddsLaw.referenceClock (M - H)) := by
    funext M
    ring
  simpa only [Function.comp_def, hsame, add_zero] using h

end PrimeFactorOscillations

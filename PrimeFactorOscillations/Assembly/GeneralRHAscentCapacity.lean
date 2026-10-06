/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.GeneralRHAscentEnvelope
import PrimeFactorOscillations.Assembly.RHAscentCapacity

/-!
# Reversal-count capacity at a general eventual lower gap

The same attained reversal maximum and actual last ascent satisfy the
reference-root upper bound with threshold H+1. The unconditional
reversal lower supply and every finite exceptional prime are retained.
-/

set_option autoImplicit false
set_option Elab.async false
namespace PrimeFactorOscillations

theorem exists_ordinary_last_ascent_and_capacity_of_RH_gap_lower
    (H : Nat) (hGaps : exists Q : Nat, forall i : Nat,
      Q <= PrimeFactorUnimodality.primeAt i -> H <= PrimeFactorUnimodality.primeGap i)
    (hRH : RiemannHypothesis) :
    exists (c A : Real) (K : Nat), 0 < c /\ 0 < A /\ 2 <= K /\
      forall k : Nat, K <= k -> exists N i : Nat, exists u : Real,
        HasReversalNumber (ordinaryDensity k) N /\
        Real.exp (Real.exp (c * (k : Real))) <= (N : Real) /\
        ordinaryDensity k i < ordinaryDensity k (i + 1) /\
        (forall j : Nat, ordinaryDensity k j < ordinaryDensity k (j + 1) -> j <= i) /\
        Set.Ioo (((k - 1 : Nat) : Real) / ((H : Real) + 1) - A)
          (((k - 1 : Nat) : Real) / ((H : Real) + 1) + A) u /\
        Nat.factorialConvolution primeProfileRealCoefficient (k - 2) u /
          Nat.factorialConvolution primeProfileRealCoefficient (k - 1) u = (H : Real) + 1 /\
        Chebyshev.theta ((PrimeFactorUnimodality.primeAt i - 1 : Nat) : Real) <
          Real.exp (Real.exp (u - Real.eulerMascheroniConstant)) /\
        N <= Nat.primeCounting (PrimeFactorUnimodality.primeAt i) /\
        Nat.primeCounting (PrimeFactorUnimodality.primeAt i) <=
          primeThetaEndpointCount (Real.exp (Real.exp (u - Real.eulerMascheroniConstant))) := by
  choose c Kl hc hKl hlast using ordinary_eventually_last_ascent_with_reversal_number
  choose A Kr hA hKr hroot using exists_ordinary_ascent_theta_envelope_of_RH_gap_lower H hGaps hRH
  refine Exists.intro c (Exists.intro A (Exists.intro (max Kl Kr)
    (And.intro hc (And.intro hA (And.intro (hKl.trans (le_max_left _ _)) ?_)))))
  intro k hk
  have hkl : Kl <= k := (le_max_left _ _).trans hk
  have hkr : Kr <= k := (le_max_right _ _).trans hk
  choose N i hN hlo hi hmax hcount using hlast k hkl
  choose u hu heq hcover using hroot k hkr
  have htheta := hcover i hi
  exact Exists.intro N (Exists.intro i (Exists.intro u
    (And.intro hN (And.intro hlo (And.intro hi (And.intro hmax
      (And.intro hu (And.intro heq (And.intro htheta (And.intro hcount
        (primeCounting_le_primeThetaEndpointCount (PrimeFactorUnimodality.primeAt i)
          (Real.exp (Real.exp (u - Real.eulerMascheroniConstant))) htheta)))))))))))

end PrimeFactorOscillations


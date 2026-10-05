/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.RHAscentCapacity
import PrimeFactorOscillations.Helpers.PrimeCountingLocation

/-!
# PNT location bounds for the actual last ordinary ascent

The uniform count-to-theta estimate applies to the actual attained reversal
maximum. Its lower location bound is unconditional; RH supplies the matching
full-reference upper envelope with the same actual last ascent.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations

theorem ordinary_eventually_last_ascent_lower_location :
    exists c : Real, 0 < c /\ forall epsilon : Real, 0 < epsilon ->
      exists K : Nat, 2 <= K /\ forall k : Nat, K <= k ->
        exists N i : Nat,
          HasReversalNumber (ordinaryDensity k) N /\
          Real.exp (Real.exp (c * (k : Real))) <= (N : Real) /\
          ordinaryDensity k i < ordinaryDensity k (i + 1) /\
          (forall j : Nat, ordinaryDensity k j < ordinaryDensity k (j + 1) -> j <= i) /\
          N <= Nat.primeCounting (PrimeFactorUnimodality.primeAt i) /\
          (1 - epsilon) * (N : Real) * Real.log (N : Real) <=
            Chebyshev.theta ((PrimeFactorUnimodality.primeAt i - 1 : Nat) : Real) := by
  choose c K0 hc hK0 hbase using ordinary_eventually_last_ascent_with_reversal_number
  refine Exists.intro c (And.intro hc ?_)
  intro epsilon he
  choose N0 hN0 hlocation using eventually_count_log_count_le_thetaPrefix epsilon he
  have hgrow : Filter.Tendsto (fun k : Nat => Real.exp (Real.exp (c * (k : Real))))
      Filter.atTop Filter.atTop := by
    simpa only [Function.comp_def] using
      Real.tendsto_exp_atTop.comp (Real.tendsto_exp_atTop.comp
        ((tendsto_natCast_atTop_atTop :
          Filter.Tendsto (fun k : Nat => (k : Real)) Filter.atTop Filter.atTop).const_mul_atTop hc))
  choose Kg hKg using (hgrow.eventually (Filter.eventually_ge_atTop (N0 : Real))).exists_forall_of_atTop
  refine Exists.intro (max K0 Kg) (And.intro (hK0.trans (le_max_left _ _)) ?_)
  intro k hk
  have hk0 : K0 <= k := (le_max_left _ _).trans hk
  have hkg : Kg <= k := (le_max_right _ _).trans hk
  choose N i hN hlo hi hlast hcount using hbase k hk0
  have hNge : N0 <= N := by exact_mod_cast (hKg k hkg).trans hlo
  refine Exists.intro N (Exists.intro i ?_)
  refine And.intro hN (And.intro hlo (And.intro hi (And.intro hlast ?_)))
  exact And.intro hcount (hlocation N hNge (PrimeFactorUnimodality.primeAt i) hcount)

theorem exists_ordinary_last_ascent_location_sandwich_of_RH (hRH : RiemannHypothesis) :
    exists c A : Real, 0 < c /\ 0 < A /\
      forall epsilon : Real, 0 < epsilon -> exists K : Nat, 2 <= K /\
        forall k : Nat, K <= k -> exists N i : Nat, exists u : Real,
          HasReversalNumber (ordinaryDensity k) N /\
          Real.exp (Real.exp (c * (k : Real))) <= (N : Real) /\
          ordinaryDensity k i < ordinaryDensity k (i + 1) /\
          (forall j : Nat, ordinaryDensity k j < ordinaryDensity k (j + 1) -> j <= i) /\
          Set.Ioo (((k - 1 : Nat) : Real) / 3 - A)
            (((k - 1 : Nat) : Real) / 3 + A) u /\
          Nat.factorialConvolution primeProfileRealCoefficient (k - 2) u /
            Nat.factorialConvolution primeProfileRealCoefficient (k - 1) u = 3 /\
          (1 - epsilon) * (N : Real) * Real.log (N : Real) <=
            Chebyshev.theta ((PrimeFactorUnimodality.primeAt i - 1 : Nat) : Real) /\
          Chebyshev.theta ((PrimeFactorUnimodality.primeAt i - 1 : Nat) : Real) <
            Real.exp (Real.exp (u - Real.eulerMascheroniConstant)) /\
          N <= Nat.primeCounting (PrimeFactorUnimodality.primeAt i) /\
          Nat.primeCounting (PrimeFactorUnimodality.primeAt i) <=
            primeThetaEndpointCount (Real.exp (Real.exp (u - Real.eulerMascheroniConstant))) := by
  choose c A K0 hc hA hK0 hbase using exists_ordinary_last_ascent_and_capacity_of_RH hRH
  refine Exists.intro c (Exists.intro A (And.intro hc (And.intro hA ?_)))
  intro epsilon he
  choose N0 hN0 hlocation using eventually_count_log_count_le_thetaPrefix epsilon he
  have hgrow : Filter.Tendsto (fun k : Nat => Real.exp (Real.exp (c * (k : Real))))
      Filter.atTop Filter.atTop := by
    simpa only [Function.comp_def] using
      Real.tendsto_exp_atTop.comp (Real.tendsto_exp_atTop.comp
        ((tendsto_natCast_atTop_atTop :
          Filter.Tendsto (fun k : Nat => (k : Real)) Filter.atTop Filter.atTop).const_mul_atTop hc))
  choose Kg hKg using (hgrow.eventually (Filter.eventually_ge_atTop (N0 : Real))).exists_forall_of_atTop
  refine Exists.intro (max K0 Kg) (And.intro (hK0.trans (le_max_left _ _)) ?_)
  intro k hk
  have hk0 : K0 <= k := (le_max_left _ _).trans hk
  have hkg : Kg <= k := (le_max_right _ _).trans hk
  choose N i u hN hlo hi hlast hu heq htheta hcount hcapacity using hbase k hk0
  have hNge : N0 <= N := by exact_mod_cast (hKg k hkg).trans hlo
  have hLower := hlocation N hNge (PrimeFactorUnimodality.primeAt i) hcount
  refine Exists.intro N (Exists.intro i (Exists.intro u ?_))
  refine And.intro hN (And.intro hlo (And.intro hi (And.intro hlast ?_)))
  refine And.intro hu (And.intro heq (And.intro hLower ?_))
  exact And.intro htheta (And.intro hcount hcapacity)

end PrimeFactorOscillations

/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.RHAscentLocation
import PrimeFactorOscillations.Helpers.ThetaEndpointAsymptotic

/-!
# Asymptotic RH capacity for the actual ordinary reversal maximum

The strict theta endpoint count has leading term T/log(T). Its eventual
estimate is applied at the same moving reference root as the actual last
ascent and attained reversal count; all constants precede epsilon.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations

theorem exists_ordinary_last_ascent_asymptotic_capacity_of_RH (hRH : RiemannHypothesis) :
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
            primeThetaEndpointCount (Real.exp (Real.exp (u - Real.eulerMascheroniConstant))) /\
          (N : Real) <= (1 + epsilon) *
            (Real.exp (Real.exp (u - Real.eulerMascheroniConstant)) /
              Real.log (Real.exp (Real.exp (u - Real.eulerMascheroniConstant)))) := by
  choose c A hc hA hbase using exists_ordinary_last_ascent_location_sandwich_of_RH hRH
  refine Exists.intro c (Exists.intro A (And.intro hc (And.intro hA ?_)))
  intro epsilon he
  choose K0 hK0 hdata using hbase epsilon he
  have hratio := tendsto_primeThetaEndpointCount_div_mainTerm.eventually
    (gt_mem_nhds (show (1 : Real) < 1 + epsilon by linarith))
  have hbound : Filter.Eventually (fun T : Real =>
      (primeThetaEndpointCount T : Real) <= (1 + epsilon) * (T / Real.log T))
      Filter.atTop := by
    filter_upwards [hratio, Filter.eventually_gt_atTop (1 : Real)] with T hr hT
    have hmain : 0 < T / Real.log T :=
      div_pos (zero_lt_one.trans hT) (Real.log_pos hT)
    have hmul := mul_lt_mul_of_pos_right hr hmain
    have hlog : 0 < Real.log T := Real.log_pos hT
    have heq : (primeThetaEndpointCount T : Real) / (T / Real.log T) *
        (T / Real.log T) = primeThetaEndpointCount T := by field_simp
    rw [heq] at hmul
    exact hmul.le
  choose T0 hT0 using hbound.exists_forall_of_atTop
  choose Kg hKg using exists_nat_ge (3 * (T0 + A + Real.eulerMascheroniConstant) + 1)
  refine Exists.intro (max K0 Kg) (And.intro (hK0.trans (le_max_left _ _)) ?_)
  intro k hk
  have hk0 : K0 <= k := (le_max_left _ _).trans hk
  have hkg : Kg <= k := (le_max_right _ _).trans hk
  have hk2 : 2 <= k := hK0.trans hk0
  choose N i u hN hlo hi hlast hu heq hLower htheta hcount hcapacity using hdata k hk0
  have hpred : ((k - 1 : Nat) : Real) = (k : Real) - 1 := by
    rw [Nat.cast_sub (show 1 <= k by omega), Nat.cast_one]
  have hkgR : (Kg : Real) <= k := by exact_mod_cast hkg
  have hu0 : T0 <= u - Real.eulerMascheroniConstant := by
    have hlower := hu.1
    rw [hpred] at hlower
    linarith
  have hexp1 : u - Real.eulerMascheroniConstant <=
      Real.exp (u - Real.eulerMascheroniConstant) := by
    linarith only [Real.add_one_le_exp (u - Real.eulerMascheroniConstant)]
  have hexp2 : Real.exp (u - Real.eulerMascheroniConstant) <=
      Real.exp (Real.exp (u - Real.eulerMascheroniConstant)) := by
    linarith only [Real.add_one_le_exp (Real.exp (u - Real.eulerMascheroniConstant))]
  have hTge := hu0.trans (hexp1.trans hexp2)
  have hcap := hT0 (Real.exp (Real.exp (u - Real.eulerMascheroniConstant))) hTge
  have hNB : (N : Real) <=
      primeThetaEndpointCount (Real.exp (Real.exp (u - Real.eulerMascheroniConstant))) := by
    exact_mod_cast hcount.trans hcapacity
  refine Exists.intro N (Exists.intro i (Exists.intro u ?_))
  refine And.intro hN (And.intro hlo (And.intro hi (And.intro hlast ?_)))
  refine And.intro hu (And.intro heq (And.intro hLower ?_))
  exact And.intro htheta (And.intro hcount (And.intro hcapacity (hNB.trans hcap)))

end PrimeFactorOscillations

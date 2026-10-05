/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.NicolasIntegerExcursions
import PrimeFactorOscillations.Helpers.PrimeProfileCanonicalSign
import PrimeFactorOscillations.Helpers.PrimeProfileLogProduct

/-!
# The false-RH direction of the actual moving-rank criterion

The exact finite Nicolas logarithm equals the difference of the clocks used
by the maintained density-ratio comparison. Its proved reciprocal-scale
excursions dominate that comparison's full error margin.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations

open Robin1984

theorem nicolasLog_nat_eq_primeProfile_clock_difference
    (N : Nat) (hTheta : 1 < Chebyshev.theta (N : Real)) :
    nicolasLogMertensOscillation (N : Real) =
      Real.eulerMascheroniConstant +
        Real.log (Real.log (Chebyshev.theta (N : Real))) -
      (primeProfilePrefixSet N).sum
        (fun p => Real.log (1 + primeProfileWeight (p : Nat))) := by
  classical
  have hPrefix : Nat.primesLE N = (Finset.Ioc 0 N).filter Nat.Prime := by
    ext p
    simp only [Nat.mem_primesLE, Finset.mem_filter, Finset.mem_Ioc]
    constructor
    . intro hp
      exact And.intro (And.intro hp.2.pos hp.1) hp.2
    . intro hp
      exact And.intro hp.1.2 hp.2
  unfold nicolasLogMertensOscillation nicolasFunction nicolasMertensProduct
  rw [Nat.floor_natCast, hPrefix]
  exact primePrefixProfile_logProduct_eq_clock_difference N
    Real.eulerMascheroniConstant (Chebyshev.theta (N : Real)) hTheta

theorem densityRatio_thetaClock_cofinally_above_reference_of_not_RH
    (alpha : Real) (ha : 0 < alpha) (hNotRH : Not RiemannHypothesis)
    (N0 : Nat) :
    exists N : Nat, N0 <= N /\
      (let L := Real.eulerMascheroniConstant +
        Real.log (Real.log (Chebyshev.theta (N : Real)))
       let r := Nat.floor (alpha * L)
       Nat.factorialConvolution primeProfileRealCoefficient (r - 1) L /
           Nat.factorialConvolution primeProfileRealCoefficient r L <
         (PrimeFactorUnimodality.densityRatio
           (PrimeFactorUnimodality.primesBelow (N + 1)) r : Real)) := by
  choose C hC hEvent using exists_eventually_densityRatio_thetaClock_sign alpha ha
  choose N1 hN1 using Filter.eventually_atTop.mp hEvent
  choose N hN hLog using nicolasLog_scaled_unbounded_of_not_RH
    hNotRH C (max N0 (max N1 1))
  have hCut : max N1 1 <= N := le_trans (le_max_right N0 (max N1 1)) hN
  have hnOne : 1 <= N := le_trans (le_max_right N1 1) hCut
  have hnOneReal : (1 : Real) <= (N : Real) := by exact_mod_cast hnOne
  have hnPos : 0 < (N : Real) := by linarith
  have hCompare := hN1 N (le_trans (le_max_left N1 1) hCut)
  have hMargin : C / (N : Real) < nicolasLogMertensOscillation (N : Real) := by
    by_contra hNot
    have hUpper := mul_le_mul_of_nonneg_left (le_of_not_gt hNot) hnPos.le
    have hCancel : (N : Real) * (C / (N : Real)) = C := by
      field_simp [hnPos.ne']
    rw [hCancel] at hUpper
    linarith
  rw [nicolasLog_nat_eq_primeProfile_clock_difference N hCompare.1] at hMargin
  refine Exists.intro N (And.intro (le_trans (le_max_left N0 (max N1 1)) hN) ?_)
  exact hCompare.2.2.2.2.1 hMargin

theorem riemannHypothesis_of_eventually_densityRatio_thetaClock_lt_reference
    (alpha : Real) (ha : 0 < alpha)
    (hEvent : Filter.Eventually (fun N : Nat =>
      let L := Real.eulerMascheroniConstant +
        Real.log (Real.log (Chebyshev.theta (N : Real)))
      let r := Nat.floor (alpha * L)
      (PrimeFactorUnimodality.densityRatio
        (PrimeFactorUnimodality.primesBelow (N + 1)) r : Real) <
        Nat.factorialConvolution primeProfileRealCoefficient (r - 1) L /
          Nat.factorialConvolution primeProfileRealCoefficient r L) Filter.atTop) :
    RiemannHypothesis := by
  by_contra hNotRH
  choose N0 hN0 using Filter.eventually_atTop.mp hEvent
  choose N hN hAbove using
    densityRatio_thetaClock_cofinally_above_reference_of_not_RH alpha ha hNotRH N0
  exact lt_asymm hAbove (hN0 N hN)

end PrimeFactorOscillations

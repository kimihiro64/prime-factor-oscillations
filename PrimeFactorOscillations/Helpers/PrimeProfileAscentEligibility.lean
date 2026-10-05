/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.PrimeDensitySteps
import PrimeFactorOscillations.Helpers.PrimeProfileUniformSign

/-!
# RH reference eligibility of actual ordinary-density ascents

The compact-band comparison is joined to the exact prime-step criterion.
Positive symmetric coefficients supply the necessary rank-support condition.
The conclusion concerns the actual next gap at the same prime endpoint.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations

open Filter

theorem ordinary_ascent_reference_gap_bound_of_RH
    (hRH : RiemannHypothesis) (a b : Real) (ha : 0 < a) (hab : a <= b) :
    exists Q : Nat, 3 <= Q /\ forall i : Nat,
      Q <= PrimeFactorUnimodality.primeAt i ->
      let L := Real.eulerMascheroniConstant +
        Real.log (Real.log (Chebyshev.theta
          ((PrimeFactorUnimodality.primeAt i - 1 : Nat) : Real)))
      forall k : Nat, a <= ((k - 1 : Nat) : Real) / L ->
        ((k - 1 : Nat) : Real) / L <= b ->
        ordinaryDensity k i < ordinaryDensity k (i + 1) ->
        (PrimeFactorUnimodality.primeGap i : Real) + 1 <
          Nat.factorialConvolution primeProfileRealCoefficient (k - 2) L /
            Nat.factorialConvolution primeProfileRealCoefficient (k - 1) L := by
  have hEvent := eventually_densityRatio_thetaClock_lt_reference_uniform_of_RH hRH a b ha hab
  have hNat := (tendsto_natCast_atTop_atTop :
    Tendsto (fun N : Nat => (N : Real)) atTop atTop).eventually hEvent
  choose N0 hN0 using eventually_atTop.mp hNat
  refine Exists.intro (N0 + 3) (And.intro (by omega) ?_)
  intro i hi
  let p := PrimeFactorUnimodality.primeAt i
  have hpBound : N0 + 3 <= p := hi
  have hpOne : 1 <= p := by omega
  have hN : N0 <= p - 1 := by omega
  have hPrefix : p - 1 + 1 = p := Nat.sub_add_cancel hpOne
  have hAll := hN0 (p - 1) hN
  dsimp only at hAll
  rw [Nat.floor_natCast, hPrefix] at hAll
  dsimp only
  intro k hLow hHigh hAscent
  have hRank := hAll.2.2 (k - 1) hLow hHigh
  have hkTwo : 2 <= k := by
    by_contra hNot
    have hZero : k - 1 = 0 := by omega
    rw [hZero] at hLow
    norm_num at hLow
    linarith
  have hDegree : k - 1 <= (PrimeFactorUnimodality.primesBelow p).length := by
    by_contra hNot
    have hLength : (PrimeFactorUnimodality.primesBelow p).length < k - 1 :=
      lt_of_not_ge hNot
    have hZero : PrimeFactorUnimodality.weightEsymm
        (PrimeFactorUnimodality.primesBelow p) (k - 1) = 0 := by
      unfold PrimeFactorUnimodality.weightEsymm
      apply Multiset.esymm_of_card_lt
      simpa only [Multiset.coe_card, List.length_map] using hLength
    have hPositive : 0 < PrimeFactorUnimodality.weightEsymm
        (PrimeFactorUnimodality.primesBelow p) (k - 1) := by
      exact_mod_cast hRank.1
    rw [hZero] at hPositive
    exact (lt_irrefl (0 : Rat)) hPositive
  have hIndexBound : k - 2 + 1 <= i := by
    dsimp [p] at hDegree
    rw [PrimeFactorUnimodality.primesBelow_primeAt_length] at hDegree
    omega
  have hIndex : k - 2 + 1 = k - 1 := by omega
  have hRankIndex : k - 2 + 2 = k := by omega
  have hAscentExact : PrimeFactorUnimodality.primeFactorDensity (k - 2 + 2) i <
      PrimeFactorUnimodality.primeFactorDensity (k - 2 + 2) (i + 1) := by
    simpa only [ordinaryDensity, hRankIndex] using hAscent
  have hRatio := (PrimeFactorUnimodality.primeDensityStep_iff_ratio_gap
    (k - 2) i hIndexBound).mp hAscentExact
  rw [hIndex] at hRatio
  have hReal : (PrimeFactorUnimodality.primeGap i : Real) + 1 <
      (PrimeFactorUnimodality.densityRatio
        (PrimeFactorUnimodality.primesBelow p) (k - 1) : Real) := by
    exact_mod_cast hRatio
  have hReference := hRank.2.2
  have hPrevious : k - 1 - 1 = k - 2 := by omega
  rw [hPrevious] at hReference
  exact hReal.trans hReference

end PrimeFactorOscillations

/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.PrimeProfileSharedExcursions
import PrimeFactorOscillations.Helpers.PrimeCyclePrefixClockSign

/-!
# The canonical RH criterion for one-boundary prime cycle prefixes

The complete coefficient comparison consumes the signed Nicolas clock
response. Both directions retain its signal; no uniform additive bound on
the transported prime coordinates is required. A concrete progression
construction must supply the exact PrimeCyclePrefix boundary identity.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.PrimeCyclePrefix

open Filter Robin1984
open BombieriVinogradov.ComplexAnalysis

/-- RH gives the canonical upper sign, with every moving-rank denominator positive. -/
theorem eventually_ratio_lt_reference_of_RH (f : PrimeCyclePrefix)
    (alpha : Real) (ha : 0 < alpha) (hRH : RiemannHypothesis) :
    Filter.Eventually (fun N : Nat =>
      let r := Nat.floor (alpha * canonicalPrimeOddsLaw.referenceClock N)
      let cN : Nat -> Real := fun j => (taylorCoefficient (f.complexPrefix N) 0 j).re
      0 < r /\
      0 < Nat.factorialConvolution cN r (canonicalPrimeOddsLaw.arithmeticClock N) /\
      0 < Nat.factorialConvolution canonicalPrimeOddsLaw.realCoefficient r
        (canonicalPrimeOddsLaw.referenceClock N) /\
      Nat.factorialConvolution cN (r - 1) (canonicalPrimeOddsLaw.arithmeticClock N) /
          Nat.factorialConvolution cN r (canonicalPrimeOddsLaw.arithmeticClock N) <
        canonicalPrimeOddsLaw.referenceRatio r (canonicalPrimeOddsLaw.referenceClock N))
      atTop := by
  choose C hC hSign using f.exists_eventually_prefixProfile_moving_floor_sign
    alpha ha canonicalPrimeOddsLaw.arithmeticClock canonicalPrimeOddsLaw.referenceClock
    canonicalPrimeOddsLaw.tendsto_referenceClock_atTop
    canonicalPrimeOddsLaw.tendsto_clock_difference_zero
  filter_upwards [hSign, eventually_nicolasLog_nat_lt_neg_div_of_RH hRH C,
      tendsto_primeProfile_theta_atTop.eventually_gt_atTop (1 : Real)] with N hS hNeg hTheta
  have hClock := canonicalPrimeOddsLaw.clock_difference_eq_nicolas N hTheta
  change canonicalPrimeOddsLaw.referenceClock N - canonicalPrimeOddsLaw.arithmeticClock N =
    1 * nicolasLogMertensOscillation (N : Real) at hClock
  rw [one_mul] at hClock
  have hMargin : canonicalPrimeOddsLaw.referenceClock N -
      canonicalPrimeOddsLaw.arithmeticClock N < -C / (N : Real) := by
    rw [hClock]
    exact hNeg
  exact And.intro hS.1 (And.intro hS.2.1 (And.intro hS.2.2.1 (hS.2.2.2.2 hMargin)))

/-- Even the eventual non-strict canonical upper sign excludes false RH. -/
theorem riemannHypothesis_of_eventually_ratio_le_reference (f : PrimeCyclePrefix)
    (alpha : Real) (ha : 0 < alpha)
    (hEvent : Filter.Eventually (fun N : Nat =>
      let r := Nat.floor (alpha * canonicalPrimeOddsLaw.referenceClock N)
      let cN : Nat -> Real := fun j => (taylorCoefficient (f.complexPrefix N) 0 j).re
      Nat.factorialConvolution cN (r - 1) (canonicalPrimeOddsLaw.arithmeticClock N) /
          Nat.factorialConvolution cN r (canonicalPrimeOddsLaw.arithmeticClock N) <=
        canonicalPrimeOddsLaw.referenceRatio r (canonicalPrimeOddsLaw.referenceClock N))
      atTop) : RiemannHypothesis := by
  by_contra hNotRH
  choose C hC hSign using f.exists_eventually_prefixProfile_moving_floor_sign
    alpha ha canonicalPrimeOddsLaw.arithmeticClock canonicalPrimeOddsLaw.referenceClock
    canonicalPrimeOddsLaw.tendsto_referenceClock_atTop
    canonicalPrimeOddsLaw.tendsto_clock_difference_zero
  have hResponse : Filter.Eventually (fun N : Nat =>
      let r := Nat.floor (alpha * canonicalPrimeOddsLaw.referenceClock N)
      let cN : Nat -> Real := fun j => (taylorCoefficient (f.complexPrefix N) 0 j).re
      C / (N : Real) < nicolasLogMertensOscillation (N : Real) ->
        canonicalPrimeOddsLaw.referenceRatio r (canonicalPrimeOddsLaw.referenceClock N) <
          Nat.factorialConvolution cN (r - 1) (canonicalPrimeOddsLaw.arithmeticClock N) /
            Nat.factorialConvolution cN r (canonicalPrimeOddsLaw.arithmeticClock N)) atTop := by
    filter_upwards [hSign,
        tendsto_primeProfile_theta_atTop.eventually_gt_atTop (1 : Real)] with N hS hTheta
    dsimp only
    intro hF
    have hClock := canonicalPrimeOddsLaw.clock_difference_eq_nicolas N hTheta
    change canonicalPrimeOddsLaw.referenceClock N - canonicalPrimeOddsLaw.arithmeticClock N =
      1 * nicolasLogMertensOscillation (N : Real) at hClock
    rw [one_mul] at hClock
    exact hS.2.2.2.1 (by rw [hClock]; exact hF)
  choose N0 hN0 using eventually_atTop.mp
    (hResponse.and (hEvent.and (eventually_ge_atTop (1 : Nat))))
  choose N hN hPeak using nicolasLog_scaled_unbounded_of_not_RH hNotRH C N0
  have hAll := hN0 N hN
  have hn : (0 : Real) < (N : Real) := by exact_mod_cast hAll.2.2
  have hF : C / (N : Real) < nicolasLogMertensOscillation (N : Real) := by
    by_contra h
    have hUpper := mul_le_mul_of_nonneg_left (le_of_not_gt h) hn.le
    have hCancel : (N : Real) * (C / N) = C := by field_simp
    rw [hCancel] at hUpper
    linarith only [hPeak, hUpper]
  exact (not_lt_of_ge hAll.2.1) (hAll.1 hF)

/-- Every one-boundary prime-cycle prefix model has the canonical RH criterion. -/
theorem riemannHypothesis_iff_eventually_ratio_lt_reference (f : PrimeCyclePrefix)
    (alpha : Real) (ha : 0 < alpha) :
    RiemannHypothesis <-> Filter.Eventually (fun N : Nat =>
      let r := Nat.floor (alpha * canonicalPrimeOddsLaw.referenceClock N)
      let cN : Nat -> Real := fun j => (taylorCoefficient (f.complexPrefix N) 0 j).re
      Nat.factorialConvolution cN (r - 1) (canonicalPrimeOddsLaw.arithmeticClock N) /
          Nat.factorialConvolution cN r (canonicalPrimeOddsLaw.arithmeticClock N) <
        canonicalPrimeOddsLaw.referenceRatio r (canonicalPrimeOddsLaw.referenceClock N))
      atTop := by
  constructor
  { intro hRH
    exact (f.eventually_ratio_lt_reference_of_RH alpha ha hRH).mono
      (fun N hN => hN.2.2.2) }
  { intro hEvent
    apply f.riemannHypothesis_of_eventually_ratio_le_reference alpha ha
    exact hEvent.mono (fun N hN => hN.le) }

end PrimeFactorOscillations.PrimeCyclePrefix

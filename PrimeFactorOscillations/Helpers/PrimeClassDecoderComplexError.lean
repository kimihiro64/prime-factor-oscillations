/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.PrimeClassDecoderErrorBudget
import PrimeFactorOscillations.Helpers.PrimeClassDecoderErrorExponents

/-!
# The full growing-disc decoder error theorem

The empirical polynomial uses literal integer sample counts and the exact
integer logarithm, degree and radius selectors. Both error exponents are
derived, and the eventual threshold is uniform over the whole disc.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.PrimeClassSampling

open Filter
open PrimeFactorOscillations.PrimeClassDecoder

theorem finite_decoding_complex_error
    (P : Set Nat) (sigma h c eta : Real)
    (hs : 0 < sigma) (hs1 : sigma < 1)
    (hsum : Summable (classPowerWeight P sigma))
    (hh : 0 < h) (hc : 0 < c) (heta : 0 < eta)
    (hsampling : eta < 1 - sigma - h * c)
    (htail : eta < c * (1 / sigma - h)) :
    Filter.Eventually (fun N : Nat => forall z : Complex,
      norm z <= 2 * (decoderRadius h N : Real) ->
        norm (truncatedSampleProfile P N (decoderRank c N) z - classEulerProfile P z) <=
          (Real.exp (2 * tsum (classPowerWeight P sigma)) + 2) * (N : Real) ^ (-eta))
      atTop := by
  let S := tsum (classPowerWeight P sigma)
  let A := S / sigma
  have hdelta : 0 < 1 / sigma - h := by
    by_contra hn
    have hnonpos : 1 / sigma - h <= 0 := le_of_not_gt hn
    have hmul := mul_nonpos_of_nonneg_of_nonpos hc.le hnonpos
    linarith
  have hsample_limit := decoder_sampling_growth_exponent_tendsto h c hh hc
  have htail_limit := decoder_tail_exponent_tendsto sigma h c A hh hc
  have hslope_limit := decoderTailSlope_atTop sigma h c A hh hc hdelta
  have hsample_event := (tendsto_order.mp hsample_limit).2 (1 - sigma - eta)
    (by nlinarith : c * h < 1 - sigma - eta)
  have htail_event := (tendsto_order.mp htail_limit).1 eta htail
  filter_upwards [hsample_event, htail_event,
    hslope_limit.eventually (eventually_ge_atTop (Real.log 2)),
    (decoderRadius_real_atTop h hh).eventually (eventually_ge_atTop 1),
    eventually_ge_atTop (2 : Nat)] with N hsampleN htailN hslopeN hR hN2
  intro z hz
  have hN : 0 < N := lt_of_lt_of_le (by norm_num : (0 : Nat) < 2) hN2
  have hNreal : (0 : Real) < (N : Real) := by exact_mod_cast hN
  have hN1 : (1 : Real) < (N : Real) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : (1 : Nat) < 2) hN2)
  have hlogN : 0 < Real.log (N : Real) := Real.log_pos hN1
  let r := 2 * (decoderRadius h N : Real)
  let M := decoderRank c N
  let a := decoderTailSlope sigma h c A N
  have hr : 1 <= r := by dsimp [r]; linarith
  have hrpos : 0 < r := by linarith
  have ha : 0 < a := lt_of_lt_of_le (Real.log_pos (by norm_num : (1 : Real) < 2)) hslopeN
  have hsampling_power : (M : Real) * Real.log r <=
      (1 - sigma - eta) * Real.log (N : Real) := by
    have hmul := mul_le_mul_of_nonneg_right hsampleN.le hlogN.le
    have hcancel : ((M : Real) * Real.log r / Real.log (N : Real)) *
        Real.log (N : Real) = (M : Real) * Real.log r := by field_simp
    rw [hcancel] at hmul
    exact hmul
  have htail_power : eta * Real.log (N : Real) <= a * ((M + 1 : Nat) : Real) := by
    have hmul := mul_le_mul_of_nonneg_right htailN.le hlogN.le
    have hcancel : (a * ((M + 1 : Nat) : Real) / Real.log (N : Real)) *
        Real.log (N : Real) = a * ((M + 1 : Nat) : Real) := by field_simp
    rw [hcancel] at hmul
    exact hmul
  have hsample_bound := samplingPowerBudget_le (N : Real) r sigma eta S M
    hNreal hrpos hsampling_power
  have htail_bound := geometricTailBudget_le (N : Real) a eta (M + 1)
    hNreal hslopeN htail_power
  have hdisc := norm_truncatedSample_sub_classEulerProfile_le P N M hN sigma r hs hs1
    hsum hr ha z hz
  change norm (truncatedSampleProfile P N M z - classEulerProfile P z) <=
    ((N : Real) ^ (sigma - 1) * Real.exp (2 * S)) * r ^ M +
      Real.exp (-a * ((M + 1 : Nat) : Real)) / (1 - Real.exp (-a)) at hdisc
  calc
    _ <= ((N : Real) ^ (sigma - 1) * Real.exp (2 * S)) * r ^ M +
        Real.exp (-a * ((M + 1 : Nat) : Real)) / (1 - Real.exp (-a)) := hdisc
    _ <= Real.exp (2 * S) * (N : Real) ^ (-eta) + 2 * (N : Real) ^ (-eta) :=
      add_le_add hsample_bound htail_bound
    _ = _ := by ring

theorem finite_decoding_complex_error_balanced
    (P : Set Nat) (sigma h eta : Real)
    (hs : 0 < sigma) (hs1 : sigma < 1)
    (hsum : Summable (classPowerWeight P sigma))
    (hh : 0 < h) (heta : 0 < eta)
    (hbalanced : eta < (1 - sigma) * (1 - h * sigma)) :
    Filter.Eventually (fun N : Nat => forall z : Complex,
      norm z <= 2 * (decoderRadius h N : Real) ->
        norm (truncatedSampleProfile P N (decoderRank (sigma * (1 - sigma)) N) z -
          classEulerProfile P z) <=
            (Real.exp (2 * tsum (classPowerWeight P sigma)) + 2) * (N : Real) ^ (-eta))
      atTop := by
  apply finite_decoding_complex_error P sigma h (sigma * (1 - sigma)) eta hs hs1 hsum hh
    (mul_pos hs (sub_pos.mpr hs1)) heta
  case hsampling =>
    have hid : 1 - sigma - h * (sigma * (1 - sigma)) =
        (1 - sigma) * (1 - h * sigma) := by ring
    rwa [hid]
  case htail =>
    have hid : sigma * (1 - sigma) * (1 / sigma - h) =
        (1 - sigma) * (1 - h * sigma) := by
      field_simp
    rwa [hid]


end PrimeFactorOscillations.PrimeClassSampling

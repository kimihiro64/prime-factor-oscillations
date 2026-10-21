/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.PrimeClassDecoderMissedFraction

/-!
# Complete critical-capacity classification

This statement collects every clause of the critical decoding theorem,
including arbitrary-coefficient polynomial decoders above a positive
counting index. The actual sample law is retained in admissibility.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.PrimeClassSampling

open Filter
open PrimeFactorOscillations.PrimeClassDecoder

structure IntegerDecoderCapacityClassification (P : Set Nat) : Prop where
  exact_capacity : integerDecoderCapacity P =
    Inv.inv (ENNReal.ofReal (primeClassConvergenceExponent P))
  admissible_below : forall h : Rat, 0 < h ->
    (h : Real) * primeClassConvergenceExponent P < 1 -> integerDecoderAdmissible P h
  excluded_above : forall h : Rat,
    1 < (h : Real) * primeClassConvergenceExponent P -> Not (integerDecoderAdmissible P h)
  counting_index : forall alpha : Real, 0 < alpha -> alpha < 1 ->
    Tendsto (primeClassLogCount P) atTop (nhds alpha) ->
      primeClassConvergenceExponent P = alpha
  missed_fraction : forall alpha h c : Real, 0 < alpha -> 0 < h -> 0 <= c ->
    Tendsto (primeClassLogCount P) atTop (nhds alpha) ->
    1 < h * alpha -> forall Q : Nat -> Polynomial Real,
    Filter.Eventually (fun N : Nat =>
      And (Not (Q N = 0)) ((Q N).natDegree <= decoderRank c N)) atTop ->
    Tendsto (fun N : Nat =>
      ((polynomialMissedClassLabels P (decoderRadius h N) (Q N)).card : Real) /
        ((primeClassPrefix P (decoderRadius h N + 1)).card : Real)) atTop (nhds 1)

theorem integer_decoder_capacity_classification
    (P : Set Nat) (s0 : Real) (hs0 : 0 < s0) (hs01 : s0 < 1)
    (hsum0 : Summable (classPowerWeight P s0)) :
    IntegerDecoderCapacityClassification P := by
  exact {
    exact_capacity := integerDecoderCapacity_eq_inverse_convergenceExponent P s0 hs0 hs01 hsum0
    admissible_below := fun h hh hcritical =>
      integerDecoderAdmissible_below_critical_exponent P s0 hs0 hs01 hsum0 h hh hcritical
    excluded_above := fun h hcritical =>
      integerDecoder_not_admissible_above_critical_exponent P h hcritical
    counting_index := fun alpha ha ha1 hindex =>
      primeClassConvergenceExponent_eq_counting_index P alpha ha ha1 hindex
    missed_fraction := fun alpha h c ha hh hc hindex hcritical Q hQ =>
      polynomial_decoder_missed_fraction_tendsto_one P alpha h c ha hh hc hindex hcritical Q hQ
  }

end PrimeFactorOscillations.PrimeClassSampling

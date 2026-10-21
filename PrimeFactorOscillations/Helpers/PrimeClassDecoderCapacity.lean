/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.PrimeClassDecoderComplete

/-!
# Admissible decoding powers and their actual degree budget

The admissibility property uses one fixed positive rational c and the
literal sampled integer decoder for every sufficiently large input.
Its forward construction consumes the complete decoder theorem; the
converse begins with the exact polynomial degree obstruction.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.PrimeClassSampling

open Filter
open PrimeFactorOscillations.PrimeClassDecoder

def integerDecoderAdmissible (P : Set Nat) (h : Rat) : Prop :=
  And (0 < h) (exists c : Rat, And (0 < c)
    (Filter.Eventually (fun N : Nat =>
      integerDecodedPrimeLabels (decoderRadius (h : Real) N)
        (decoderRank (c : Real) N) (sampleCount P N) =
          primeClassPrefix P (decoderRadius (h : Real) N + 1)) atTop))

theorem integerDecoderAdmissible_of_summable_power
    (P : Set Nat) (sigma : Real) (h : Rat)
    (hs : 0 < sigma) (hs1 : sigma < 1) (hsum : Summable (classPowerWeight P sigma))
    (hh : 0 < h) (hpower : (h : Real) * sigma < 1) :
    integerDecoderAdmissible P h := by
  have hhR : (0 : Real) < (h : Real) := by exact_mod_cast hh
  have hupper : (0 : Real) < (1 - sigma) / (h : Real) :=
    div_pos (by linarith) hhR
  choose c hc using exists_rat_btwn hupper
  have hcQ : (0 : Rat) < c := by exact_mod_cast hc.1
  apply And.intro hh
  apply Exists.intro c
  apply And.intro hcQ
  filter_upwards [finite_integer_prime_decoding_complete P sigma h c
    hs hs1 hsum hh hcQ hpower hc.2] with N hN
  have houtput := hN.executable_exact
  rw [executableIntegerPrimeDecoder_eq h c (le_of_lt hcQ),
    rationalIntegerPrimeDecoder_eq h c (le_of_lt hh) (le_of_lt hcQ),
    integerPrimeDecoder_eq] at houtput
  exact houtput

theorem integerDecoderAdmissible_degree_budget
    (P : Set Nat) (h : Rat) (had : integerDecoderAdmissible P h) :
    exists c : Rat, And (0 < c)
      (Filter.Eventually (fun N : Nat =>
        (primeClassPrefix P (decoderRadius (h : Real) N + 1)).card <=
          decoderRank (c : Real) N) atTop) := by
  choose c hc using had.2
  apply Exists.intro c
  apply And.intro hc.1
  filter_upwards [hc.2, eventually_ge_atTop 1] with N hN hN1
  have hdegree := card_integerDecodedSampleLabels_le P N (decoderRank (c : Real) N)
    (decoderRadius (h : Real) N) (by omega)
  rw [hN] at hdegree
  exact hdegree

end PrimeFactorOscillations.PrimeClassSampling

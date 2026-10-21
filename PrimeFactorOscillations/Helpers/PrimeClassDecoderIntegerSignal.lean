/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.PrimeClassDecoderSignTransfer

/-!
# The surviving model parity belongs to the literal integer probes

The complex sampled polynomial is identified with the existing empirical
count polynomial. Its exact N*2^M normalization transfers the quantitative
sign result to the literal integer finite sums, simultaneously in the range.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.PrimeClassSampling

open Filter
open PrimeFactorOscillations.PrimeClassDecoder

theorem truncatedSampleProfile_real_eq_empiricalPolynomial
    (P : Set Nat) (N M : Nat) (x : Real) :
    truncatedSampleProfile P N M (x : Complex) =
      (((empiricalPolynomial N M (sampleCount P N)).eval x : Real) : Complex) := by
  rw [empiricalPolynomial, Polynomial.eval_mul, Polynomial.eval_C,
    countPolynomial_eval, Finset.mul_sum]
  unfold truncatedSampleProfile
  push_cast
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem integerProbe_eq_scaled_truncatedSample
    (P : Set Nat) (N M n : Nat) (hN : 0 < N) :
    (integerProbe M (sampleCount P N) n : Real) = (N : Real) * (2 : Real) ^ M *
      (truncatedSampleProfile P N M (((-(n : Real) - 1 / 2 : Real) : Complex))).re := by
  rw [truncatedSampleProfile_real_eq_empiricalPolynomial, Complex.ofReal_re]
  exact integerProbe_eq_scaled_empiricalPolynomial N M (sampleCount P N) n hN

theorem integerProbe_halfInteger_signed_pos
    (P : Set Nat) (sigma h c eta : Real) (hs : 0 < sigma) (hs1 : sigma < 1)
    (hsum : Summable (classPowerWeight P sigma))
    (hh : 0 < h) (hc : 0 < c) (heta : 0 < eta) (hpower : h * sigma < 1)
    (hsampling : eta < 1 - sigma - h * c) (htail : eta < c * (1 / sigma - h)) :
    Filter.Eventually (fun N : Nat => forall n : Nat, n <= decoderRadius h N ->
      And (0 < (-1 : Real) ^ (primeClassPrefix P (n + 1)).card *
          (integerProbe (decoderRank c N) (sampleCount P N) n : Real))
        (Not (integerProbe (decoderRank c N) (sampleCount P N) n = 0))) atTop := by
  have hsign := truncatedSample_halfInteger_signed_pos P sigma h c eta hs hs1 hsum
    hh hc heta hpower hsampling htail
  filter_upwards [hsign, eventually_ge_atTop (1 : Nat)] with N hsignN hN1
  intro n hn
  have hN : 0 < N := by omega
  have hnorm : 0 < (N : Real) * (2 : Real) ^ decoderRank c N :=
    mul_pos (by exact_mod_cast hN) (pow_pos (by norm_num) _)
  have hmul := mul_pos hnorm (hsignN n hn)
  have hpositive : 0 < (-1 : Real) ^ (primeClassPrefix P (n + 1)).card *
      (integerProbe (decoderRank c N) (sampleCount P N) n : Real) := by
    rw [integerProbe_eq_scaled_truncatedSample P N (decoderRank c N) n hN]
    nlinarith
  refine And.intro hpositive ?_
  intro hz
  rw [hz, Int.cast_zero, mul_zero] at hpositive
  exact lt_irrefl 0 hpositive

end PrimeFactorOscillations.PrimeClassSampling

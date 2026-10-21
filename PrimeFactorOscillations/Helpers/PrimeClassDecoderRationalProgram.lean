/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.PrimeClassDecoderCertified
import PrimeFactorOscillations.Helpers.PrimeClassDecoderRootSearch

/-!
# An executable decoder from rational parameters and observed counts

Both integer selectors are computed from N,h,c. The resulting program
has no class-membership or primality argument. Its output equals the
analytic decoder, with the full certificate for evaluation and sign tests.
The cost certificate measures that evaluation stage.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.PrimeClassDecoder

def rationalDecoderRadiusFromRat (h : Rat) (N : Nat) : Nat :=
  fastRationalDecoderRadius h.num.toNat h.den N

def rationalIntegerPrimeDecoder (h c : Rat) (N : Nat) (C : Nat -> Nat) : Finset Nat :=
  integerPrimeDecoder (rationalDecoderRadiusFromRat h N) (rationalDecoderRank c N) C

theorem nonnegativeRat_cast_eq_num_div_den (h : Rat) (hh : 0 <= h) :
    (h : Real) = (h.num.toNat : Real) / (h.den : Real) := by
  rw [Rat.cast_def]
  have hnum : (h.num.toNat : Real) = (h.num : Real) := by
    exact_mod_cast Int.toNat_of_nonneg (Rat.num_nonneg.mpr hh)
  rw [hnum]

theorem rationalDecoderRadiusFromRat_eq (h : Rat) (hh : 0 <= h) (N : Nat) :
    rationalDecoderRadiusFromRat h N = decoderRadius (h : Real) N := by
  unfold rationalDecoderRadiusFromRat
  rw [fastRationalDecoderRadius_eq _ _ _ (Nat.succ_le_of_lt (Rat.den_pos h))]
  rw [<- nonnegativeRat_cast_eq_num_div_den h hh]

theorem rationalIntegerPrimeDecoder_eq
    (h c : Rat) (hh : 0 <= h) (hc : 0 <= c) (N : Nat) (C : Nat -> Nat) :
    rationalIntegerPrimeDecoder h c N C =
      integerPrimeDecoder (decoderRadius (h : Real) N) (decoderRank (c : Real) N) C := by
  unfold rationalIntegerPrimeDecoder
  rw [rationalDecoderRadiusFromRat_eq h hh, rationalDecoderRank_eq c hc]

end PrimeFactorOscillations.PrimeClassDecoder

namespace PrimeFactorOscillations.PrimeClassSampling

open Filter
open PrimeFactorOscillations.PrimeClassDecoder

theorem rational_integer_prime_decoding
    (P : Set Nat) (sigma : Real) (h c : Rat) (hs : 0 < sigma) (hs1 : sigma < 1)
    (hsum : Summable (classPowerWeight P sigma))
    (hh : 0 < h) (hc : 0 < c) (hpower : (h : Real) * sigma < 1)
    (hcBound : (c : Real) < (1 - sigma) / (h : Real)) :
    Filter.Eventually (fun N : Nat =>
      And (FiniteIntegerDecoderCertificate P N (h : Real) (c : Real))
        (rationalIntegerPrimeDecoder h c N (sampleCount P N) =
          primeClassPrefix P (rationalDecoderRadiusFromRat h N + 1))) atTop := by
  have hhR : (0 : Real) < (h : Real) := by exact_mod_cast hh
  have hcR : (0 : Real) < (c : Real) := by exact_mod_cast hc
  filter_upwards [finite_integer_prime_decoding_certificate P sigma (h : Real) (c : Real)
    hs hs1 hsum hhR hcR hpower hcBound] with N hN
  apply And.intro hN
  rw [rationalIntegerPrimeDecoder_eq h c (le_of_lt hh) (le_of_lt hc),
    rationalDecoderRadiusFromRat_eq h (le_of_lt hh)]
  exact (hN.all_prefixes (decoderRadius (h : Real) N) (Nat.le_refl _)).1

end PrimeFactorOscillations.PrimeClassSampling

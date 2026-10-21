/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.PrimeClassDecoderBits
import PrimeFactorOscillations.Helpers.PrimeClassDecoderExact

/-!
# Computable integer decoding and every prefix count

The decoder is executable from R,M and the observed counts alone.
It makes no class-membership or primality queries. A congruence theorem
proves that coefficients above M cannot affect its output. Every prefix
uses the same observed data and the same eventual analytic threshold.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.PrimeClassDecoder

def integerPrimeDecoder (R M : Nat) (C : Nat -> Nat) : Finset Nat :=
  ((Finset.Icc 1 R).filter (fun n =>
    (integerHornerState C (-((2 * (n - 1) + 1 : Nat) : Int)) M (M + 1)).accumulator *
      (integerHornerState C (-((2 * n + 1 : Nat) : Int)) M (M + 1)).accumulator < 0)).image
        Nat.succ

theorem integerPrimeDecoder_eq (R M : Nat) (C : Nat -> Nat) :
    integerPrimeDecoder R M C = integerDecodedPrimeLabels R M C := by
  unfold integerPrimeDecoder
  simp only [integerHornerState_eq_integerProbe]
  rfl

theorem integerProbe_eq_of_counts_agree
    (R M : Nat) (C D : Nat -> Nat) (hCD : forall k, k <= M -> C k = D k) :
    integerProbe M C R = integerProbe M D R := by
  unfold integerProbe
  apply Finset.sum_congr rfl
  intro k hk
  rw [hCD k (Nat.le_of_lt_succ (Finset.mem_range.mp hk))]

theorem integerPrimeDecoder_eq_of_counts_agree
    (R M : Nat) (C D : Nat -> Nat) (hCD : forall k, k <= M -> C k = D k) :
    integerPrimeDecoder R M C = integerPrimeDecoder R M D := by
  classical
  rw [integerPrimeDecoder_eq, integerPrimeDecoder_eq]
  unfold integerDecodedPrimeLabels integerSignChangeIndices
  congr 1
  apply Finset.filter_congr
  intro n hn
  rw [integerProbe_eq_of_counts_agree (n - 1) M C D hCD,
    integerProbe_eq_of_counts_agree n M C D hCD]

theorem card_integerDecodedPrimeLabels_eq_signChanges
    (R M : Nat) (C : Nat -> Nat) :
    (integerDecodedPrimeLabels R M C).card = (integerSignChangeIndices R M C).card := by
  classical
  unfold integerDecodedPrimeLabels
  exact Finset.card_image_of_injective _ Nat.succ_injective

def integerHornerCompleteOperations (R M : Nat) : Nat :=
  (R + 1) * (5 * (M + 1) + 4) + 2 * R

theorem integerHorner_complete_operation_bound (R M : Nat) (hR : 1 <= R) (hM : 1 <= M) :
    integerHornerCompleteOperations R M <= 30 * R * M := by
  unfold integerHornerCompleteOperations
  have hr : R + 1 <= 2 * R := by omega
  have hm : 5 * (M + 1) + 4 <= 14 * M := by omega
  calc
    (R + 1) * (5 * (M + 1) + 4) + 2 * R <= (2 * R) * (14 * M) + 2 * R := by
      gcongr
    _ <= 30 * R * M := by nlinarith

end PrimeFactorOscillations.PrimeClassDecoder

namespace PrimeFactorOscillations.PrimeClassSampling

open Filter
open PrimeFactorOscillations.PrimeClassDecoder

theorem finite_integer_prime_decoding_all_prefixes
    (P : Set Nat) (sigma h c : Real) (hs : 0 < sigma) (hs1 : sigma < 1)
    (hsum : Summable (classPowerWeight P sigma))
    (hh : 0 < h) (hc : 0 < c) (hpower : h * sigma < 1)
    (hcBound : c < (1 - sigma) / h) :
    Filter.Eventually (fun N : Nat => forall r : Nat, r <= decoderRadius h N ->
      And (integerPrimeDecoder r (decoderRank c N) (sampleCount P N) =
          primeClassPrefix P (r + 1))
        ((integerSignChangeIndices r (decoderRank c N) (sampleCount P N)).card =
          (primeClassPrefix P (r + 1)).card)) atTop := by
  filter_upwards [finite_integer_prime_decoding P sigma h c hs hs1 hsum hh hc hpower hcBound]
    with N hN
  intro r hr
  have hpos : forall j : Nat, j <= r ->
      0 < (-1 : Real) ^ (primeClassPrefix P (j + 1)).card *
        (integerProbe (decoderRank c N) (sampleCount P N) j : Real) := by
    intro j hj
    exact (hN.1 j (hj.trans hr)).1
  have hset := integerDecodedPrimeLabels_eq_prefix_of_signed_pos P N (decoderRank c N) r hpos
  apply And.intro
  case left =>
    rw [integerPrimeDecoder_eq]
    exact hset
  case right =>
    rw [<- card_integerDecodedPrimeLabels_eq_signChanges, hset]

end PrimeFactorOscillations.PrimeClassSampling

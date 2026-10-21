/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.PrimeClassDecoderLabelSteps

/-!
# Exact finite integer decoding of an arbitrary summable prime class

The complete sampling, independent supply, integer normalization and
adjacent parity arguments yield the actual decoded prime-label set.
All fixed parameters satisfy the paper's full admissible domain.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.PrimeClassSampling

open Filter
open PrimeFactorOscillations.PrimeClassDecoder

noncomputable def classPrimeLabelIndices (P : Set Nat) (R : Nat) : Finset Nat := by
  classical
  exact (Finset.Icc 1 R).filter (fun n =>
    And (Nat.Prime (n + 1)) (Membership.mem P (n + 1)))

theorem classPrimeLabelImage_eq_prefix (P : Set Nat) (R : Nat) :
    (classPrimeLabelIndices P R).image Nat.succ = primeClassPrefix P (R + 1) := by
  classical
  unfold classPrimeLabelIndices
  apply Finset.ext
  intro p
  constructor
  case mp =>
    intro hp
    choose n hn using Finset.mem_image.mp hp
    have hfilter := Finset.mem_filter.mp hn.1
    have hIcc := Finset.mem_Icc.mp hfilter.1
    have hEq : n + 1 = p := hn.2
    rw [<- hEq]
    apply Finset.mem_filter.mpr
    exact And.intro (Finset.mem_Icc.mpr (And.intro (by omega) (by omega))) hfilter.2
  case mpr =>
    intro hp
    have hfilter := Finset.mem_filter.mp hp
    have hIcc := Finset.mem_Icc.mp hfilter.1
    apply Finset.mem_image.mpr
    apply Exists.intro (p - 1)
    apply And.intro
    case left =>
      apply Finset.mem_filter.mpr
      have hEq : p - 1 + 1 = p := by omega
      exact And.intro (Finset.mem_Icc.mpr (And.intro (by omega) (by omega)))
        (by simpa only [hEq] using hfilter.2)
    case right => omega

theorem integerDecodedPrimeLabels_eq_prefix_of_signed_pos
    (P : Set Nat) (N M R : Nat)
    (hpos : forall j : Nat, j <= R ->
      0 < (-1 : Real) ^ (primeClassPrefix P (j + 1)).card *
        (integerProbe M (sampleCount P N) j : Real)) :
    integerDecodedPrimeLabels R M (sampleCount P N) = primeClassPrefix P (R + 1) := by
  classical
  have hindices : integerSignChangeIndices R M (sampleCount P N) =
      (Finset.Icc 1 R).filter (fun n =>
        And (Nat.Prime (n + 1)) (Membership.mem P (n + 1))) := by
    apply Finset.ext
    intro n
    by_cases hn : Membership.mem (Finset.Icc 1 R) n
    case pos =>
      have hIcc := Finset.mem_Icc.mp hn
      simp only [integerSignChangeIndices, Finset.mem_filter, hn, true_and]
      exact integerProbe_adjacent_neg_iff P N M R n hIcc.1 hIcc.2 hpos
    case neg => simp [integerSignChangeIndices, hn]
  unfold integerDecodedPrimeLabels
  rw [hindices]
  exact classPrimeLabelImage_eq_prefix P R

theorem exists_decoder_error_eta
    (sigma h c : Real) (hs : 0 < sigma)
    (hh : 0 < h) (hc : 0 < c) (hpower : h * sigma < 1)
    (hcBound : c < (1 - sigma) / h) :
    exists eta : Real, And (0 < eta)
      (And (eta < 1 - sigma - h * c) (eta < c * (1 / sigma - h))) := by
  have hmul := mul_lt_mul_of_pos_right hcBound hh
  have hcancel : ((1 - sigma) / h) * h = 1 - sigma := by field_simp
  rw [hcancel] at hmul
  have hd1 : 0 < 1 - sigma - h * c := by nlinarith
  have hscale := mul_lt_mul_of_pos_right hpower (one_div_pos.mpr hs)
  have hid : h * sigma * (1 / sigma) = h := by field_simp
  rw [hid, one_mul] at hscale
  have hd2 : 0 < c * (1 / sigma - h) := mul_pos hc (by linarith)
  have hmin : 0 < min (1 - sigma - h * c) (c * (1 / sigma - h)) := lt_min hd1 hd2
  apply Exists.intro (min (1 - sigma - h * c) (c * (1 / sigma - h)) / 2)
  apply And.intro (half_pos hmin)
  apply And.intro
  case left => exact (half_lt_self hmin).trans_le (min_le_left _ _)
  case right => exact (half_lt_self hmin).trans_le (min_le_right _ _)

theorem finite_integer_prime_decoding
    (P : Set Nat) (sigma h c : Real) (hs : 0 < sigma) (hs1 : sigma < 1)
    (hsum : Summable (classPowerWeight P sigma))
    (hh : 0 < h) (hc : 0 < c) (hpower : h * sigma < 1)
    (hcBound : c < (1 - sigma) / h) :
    Filter.Eventually (fun N : Nat =>
      And (forall n : Nat, n <= decoderRadius h N ->
          And (0 < (-1 : Real) ^ (primeClassPrefix P (n + 1)).card *
              (integerProbe (decoderRank c N) (sampleCount P N) n : Real))
            (Not (integerProbe (decoderRank c N) (sampleCount P N) n = 0)))
        (And (forall n : Nat, 1 <= n -> n <= decoderRadius h N ->
            (integerProbe (decoderRank c N) (sampleCount P N) (n - 1) *
              integerProbe (decoderRank c N) (sampleCount P N) n < 0 <->
                And (Nat.Prime (n + 1)) (Membership.mem P (n + 1))))
          (integerDecodedPrimeLabels (decoderRadius h N) (decoderRank c N) (sampleCount P N) =
            primeClassPrefix P (decoderRadius h N + 1)))) atTop := by
  choose eta heta using exists_decoder_error_eta sigma h c hs hh hc hpower hcBound
  have hsign := integerProbe_halfInteger_signed_pos P sigma h c eta hs hs1 hsum
    hh hc heta.1 hpower heta.2.1 heta.2.2
  filter_upwards [hsign] with N hsignN
  have hpos : forall j : Nat, j <= decoderRadius h N ->
      0 < (-1 : Real) ^ (primeClassPrefix P (j + 1)).card *
        (integerProbe (decoderRank c N) (sampleCount P N) j : Real) := by
    intro j hj
    exact (hsignN j hj).1
  apply And.intro hsignN
  apply And.intro
  case left =>
    intro n hn hnR
    exact integerProbe_adjacent_neg_iff P N (decoderRank c N) (decoderRadius h N) n hn hnR hpos
  case right =>
    exact integerDecodedPrimeLabels_eq_prefix_of_signed_pos P N (decoderRank c N) (decoderRadius h N) hpos

end PrimeFactorOscillations.PrimeClassSampling

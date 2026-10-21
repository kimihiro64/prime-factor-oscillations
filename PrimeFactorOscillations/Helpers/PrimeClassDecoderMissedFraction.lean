/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.PrimeClassCountingLower

/-!
# The full missed fraction above the polynomial decoding capacity

The denominator is the actual class count. The degree comparison applies
to every sequence of nonzero real polynomials, with arbitrary coefficients.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.PrimeClassSampling

open Filter
open PrimeFactorOscillations.PrimeClassDecoder

theorem decoderRank_div_actual_count_tendsto_zero
    (P : Set Nat) (alpha h c : Real) (hh : 0 < h) (hc : 0 <= c)
    (hindex : Tendsto (primeClassLogCount P) atTop (nhds alpha))
    (hcritical : 1 < h * alpha) :
    Tendsto (fun N : Nat => (decoderRank c N : Real) /
      ((primeClassPrefix P (decoderRadius h N + 1)).card : Real)) atTop (nhds 0) := by
  have hunit : h * (1 / h) = 1 := by field_simp
  have hinv : 1 / h < alpha := by nlinarith
  choose t ht using exists_between hinv
  have ht0 : 0 < t := lt_trans (one_div_pos.mpr hh) ht.1
  have hgain : 0 < h * t - 1 := by nlinarith
  have hX := decoderRadius_succ_atTop h hh
  have hlow := hX.eventually
    (primeClassPrefix_eventually_rpow_le_countOne P alpha t hindex ht.2)
  have hpow : Tendsto (fun N : Nat =>
      ((decoderRadius h N + 1 : Nat) : Real) ^ t) atTop atTop :=
    (tendsto_rpow_atTop ht0).comp (tendsto_natCast_atTop_atTop.comp hX)
  have hlimit : Tendsto (fun N : Nat => 2 * c *
      (binaryCutoff N : Real) ^ (1 - h * t)) atTop (nhds 0) := by
    have heq : 1 - h * t = -(h * t - 1) := by ring
    rw [heq]
    simpa only [mul_zero, Function.comp_apply] using
      ((tendsto_rpow_neg_atTop hgain).comp binaryCutoff_real_atTop).const_mul (2 * c)
  apply squeeze_zero' (Filter.Eventually.of_forall (fun N =>
    div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))) _ hlimit
  filter_upwards [hlow, hpow.eventually (eventually_ge_atTop 2),
    binaryCutoff_real_atTop.eventually (eventually_gt_atTop 0)] with N hN hpowN hU
  have hcountpos : (0 : Real) <
      ((primeClassPrefix P (decoderRadius h N + 1)).card : Real) := by linarith
  have hroot : (binaryCutoff N : Real) ^ h <=
      ((decoderRadius h N + 1 : Nat) : Real) := by
    have hf := Nat.lt_floor_add_one ((binaryCutoff N : Real) ^ h)
    simpa only [decoderRadius, Nat.cast_add, Nat.cast_one] using le_of_lt hf
  have hrootpow : (binaryCutoff N : Real) ^ (h * t) <=
      ((decoderRadius h N + 1 : Nat) : Real) ^ t := by
    rw [Real.rpow_mul (le_of_lt hU)]
    exact Real.rpow_le_rpow (Real.rpow_nonneg (le_of_lt hU) h) hroot (le_of_lt ht0)
  have hden : (binaryCutoff N : Real) ^ (h * t) / 2 <=
      ((primeClassPrefix P (decoderRadius h N + 1)).card : Real) := by nlinarith
  have hdenpos : 0 < (binaryCutoff N : Real) ^ (h * t) / 2 :=
    div_pos (Real.rpow_pos_of_pos hU _) (by norm_num)
  calc
    (decoderRank c N : Real) / ((primeClassPrefix P (decoderRadius h N + 1)).card : Real) <=
        (c * (binaryCutoff N : Real)) /
          ((primeClassPrefix P (decoderRadius h N + 1)).card : Real) :=
      div_le_div_of_nonneg_right (decoderRank_le_binaryCutoff c hc N) (le_of_lt hcountpos)
    _ <= (c * (binaryCutoff N : Real)) / ((binaryCutoff N : Real) ^ (h * t) / 2) :=
      div_le_div_of_nonneg_left (mul_nonneg hc (le_of_lt hU)) hdenpos hden
    _ = 2 * c * (binaryCutoff N : Real) ^ (1 - h * t) := by
      rw [Real.rpow_sub hU, Real.rpow_one]
      field_simp

noncomputable def polynomialMissedClassLabels
    (P : Set Nat) (R : Nat) (q : Polynomial Real) : Finset Nat := by
  classical
  exact SDiff.sdiff (primeClassPrefix P (R + 1)) (decodedPrimeLabels R q)

theorem polynomial_decoder_missed_fraction_tendsto_one
    (P : Set Nat) (alpha h c : Real) (ha : 0 < alpha) (hh : 0 < h) (hc : 0 <= c)
    (hindex : Tendsto (primeClassLogCount P) atTop (nhds alpha))
    (hcritical : 1 < h * alpha) (Q : Nat -> Polynomial Real)
    (hQ : Filter.Eventually (fun N : Nat =>
      And (Not (Q N = 0)) ((Q N).natDegree <= decoderRank c N)) atTop) :
    Tendsto (fun N : Nat =>
      ((polynomialMissedClassLabels P (decoderRadius h N) (Q N)).card : Real) /
        ((primeClassPrefix P (decoderRadius h N + 1)).card : Real)) atTop (nhds 1) := by
  classical
  let S := fun N => primeClassPrefix P (decoderRadius h N + 1)
  let D := fun N => decodedPrimeLabels (decoderRadius h N) (Q N)
  have hbudget := decoderRank_div_actual_count_tendsto_zero P alpha h c hh hc hindex hcritical
  have hintersection : Tendsto (fun N : Nat =>
      ((Inter.inter (S N) (D N)).card : Real) / ((S N).card : Real)) atTop (nhds 0) := by
    apply squeeze_zero' (Filter.Eventually.of_forall (fun N =>
      div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))) _ hbudget
    filter_upwards [hQ] with N hN
    have hsub : forall p, Membership.mem (Inter.inter (S N) (D N)) p -> Membership.mem (D N) p :=
      fun p hp => (Finset.mem_inter.mp hp).2
    have hcard := (Finset.card_le_card hsub).trans
      ((card_decodedPrimeLabels_le_natDegree (decoderRadius h N) (Q N) hN.1).trans hN.2)
    exact div_le_div_of_nonneg_right (by exact_mod_cast hcard) (Nat.cast_nonneg _)
  have hcountTop := (primeClassPrefix_card_real_atTop_of_counting_index P alpha ha hindex).comp
    (decoderRadius_succ_atTop h hh)
  have hlimit : Tendsto (fun N : Nat =>
      1 - ((Inter.inter (S N) (D N)).card : Real) / ((S N).card : Real))
      atTop (nhds ((1 : Real) - 0)) := tendsto_const_nhds.sub hintersection
  have heq : Filter.EventuallyEq atTop
      (fun N : Nat => 1 - ((Inter.inter (S N) (D N)).card : Real) / ((S N).card : Real))
      (fun N : Nat =>
        ((polynomialMissedClassLabels P (decoderRadius h N) (Q N)).card : Real) /
          ((primeClassPrefix P (decoderRadius h N + 1)).card : Real)) := by
    filter_upwards [hcountTop.eventually (eventually_gt_atTop 0)] with N hN
    have hcard := Finset.card_sdiff_add_card_inter (S N) (D N)
    have hcardR : ((SDiff.sdiff (S N) (D N)).card : Real) +
        ((Inter.inter (S N) (D N)).card : Real) = ((S N).card : Real) := by exact_mod_cast hcard
    change 1 - ((Inter.inter (S N) (D N)).card : Real) / ((S N).card : Real) =
      ((SDiff.sdiff (S N) (D N)).card : Real) / ((S N).card : Real)
    have hne : Not (((S N).card : Real) = 0) := ne_of_gt hN
    field_simp
    linarith
  exact Filter.Tendsto.congr' heq (by simpa only [sub_zero] using hlimit)

end PrimeFactorOscillations.PrimeClassSampling

/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.PrimeClassDecoderErrorExponents

/-!
# Preprocessing is lower order than the evaluation budget

For every fixed positive h,c, any fixed multiple of U_N+R_N+1 is
eventually at most R_N*M_N. This charges a linear logarithmic-cutoff
algorithm and a root search linear in the actual radius.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.PrimeClassDecoder

open Filter

theorem log_log_div_decoderRadius_tendsto_zero (h : Real) (hh : 0 < h) :
    Tendsto (fun N : Nat => Real.log (Real.log (N : Real)) / (decoderRadius h N : Real))
      atTop (nhds 0) := by
  have hr := decoderRadius_real_atTop h hh
  have hsmall := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hr
  change Tendsto (fun N : Nat => Real.log (decoderRadius h N : Real) /
    (decoderRadius h N : Real)) atTop (nhds 0) at hsmall
  have hone : Tendsto (fun _ : Nat => (1 : Real)) atTop (nhds 1) := tendsto_const_nhds
  have hinv := hone.div (log_decoderRadius_div_log_log_tendsto h hh) (ne_of_gt hh)
  have hlim := hsmall.mul hinv
  have heq : Filter.EventuallyEq atTop
      (fun N : Nat => (Real.log (decoderRadius h N : Real) / (decoderRadius h N : Real)) *
        (1 / (Real.log (decoderRadius h N : Real) / Real.log (Real.log (N : Real)))))
      (fun N : Nat => Real.log (Real.log (N : Real)) / (decoderRadius h N : Real)) := by
    filter_upwards [hr.eventually (eventually_gt_atTop 1)] with N hR
    have hR0 : (0 : Real) < (decoderRadius h N : Real) := by linarith
    have hlR : 0 < Real.log (decoderRadius h N : Real) := Real.log_pos hR
    field_simp [ne_of_gt hR0, ne_of_gt hlR]
  exact Filter.Tendsto.congr' heq (by simpa only [zero_mul, Pi.div_apply] using hlim)

theorem log_div_decoder_evaluation_budget_tendsto_zero
    (h c : Real) (hh : 0 < h) (hc : 0 < c) :
    Tendsto (fun N : Nat => Real.log (N : Real) /
      ((decoderRadius h N : Real) * (decoderRank c N : Real))) atTop (nhds 0) := by
  have hone : Tendsto (fun _ : Nat => (1 : Real)) atTop (nhds 1) := tendsto_const_nhds
  have hinv := hone.div (decoderRank_log_scale_tendsto c hc) (ne_of_gt hc)
  have hlim := (log_log_div_decoderRadius_tendsto_zero h hh).mul hinv
  have hll : Tendsto (fun N : Nat => Real.log (Real.log (N : Real))) atTop atTop :=
    Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have heq : Filter.EventuallyEq atTop
      (fun N : Nat => (Real.log (Real.log (N : Real)) / (decoderRadius h N : Real)) *
        (1 / ((decoderRank c N : Real) * Real.log (Real.log (N : Real)) / Real.log (N : Real))))
      (fun N : Nat => Real.log (N : Real) /
        ((decoderRadius h N : Real) * (decoderRank c N : Real))) := by
    filter_upwards [(decoderRadius_real_atTop h hh).eventually (eventually_gt_atTop 0),
      (decoderRank_real_atTop c hc).eventually (eventually_gt_atTop 0),
      hll.eventually (eventually_gt_atTop 0)] with N hR hM hL
    field_simp [ne_of_gt hR, ne_of_gt hM, ne_of_gt hL]
  exact Filter.Tendsto.congr' heq (by simpa only [zero_mul, Pi.div_apply] using hlim)

theorem binaryCutoff_div_decoder_evaluation_budget_tendsto_zero
    (h c : Real) (hh : 0 < h) (hc : 0 < c) :
    Tendsto (fun N : Nat => (binaryCutoff N : Real) /
      ((decoderRadius h N : Real) * (decoderRank c N : Real))) atTop (nhds 0) := by
  have hlim := binaryCutoff_div_log_tendsto.mul
    (log_div_decoder_evaluation_budget_tendsto_zero h c hh hc)
  have hlogN : Tendsto (fun N : Nat => Real.log (N : Real)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have heq : Filter.EventuallyEq atTop
      (fun N : Nat => ((binaryCutoff N : Real) / Real.log (N : Real)) *
        (Real.log (N : Real) / ((decoderRadius h N : Real) * (decoderRank c N : Real))))
      (fun N : Nat => (binaryCutoff N : Real) /
        ((decoderRadius h N : Real) * (decoderRank c N : Real))) := by
    filter_upwards [hlogN.eventually (eventually_gt_atTop 0)] with N hN
    field_simp [ne_of_gt hN]
  exact Filter.Tendsto.congr' heq (by simpa only [mul_zero] using hlim)

theorem preprocessing_div_decoder_evaluation_budget_tendsto_zero
    (h c : Real) (hh : 0 < h) (hc : 0 < c) :
    Tendsto (fun N : Nat => ((binaryCutoff N : Real) + (decoderRadius h N : Real) + 1) /
      ((decoderRadius h N : Real) * (decoderRank c N : Real))) atTop (nhds 0) := by
  have hone : Tendsto (fun _ : Nat => (1 : Real)) atTop (nhds 1) := tendsto_const_nhds
  have hR := hone.div_atTop (decoderRadius_real_atTop h hh)
  have hM := hone.div_atTop (decoderRank_real_atTop c hc)
  have hlim := ((binaryCutoff_div_decoder_evaluation_budget_tendsto_zero h c hh hc).add hM).add
    (hR.mul hM)
  have heq : Filter.EventuallyEq atTop
      (fun N : Nat => (binaryCutoff N : Real) /
          ((decoderRadius h N : Real) * (decoderRank c N : Real)) +
        1 / (decoderRank c N : Real) +
        ((1 / (decoderRadius h N : Real)) * (1 / (decoderRank c N : Real))))
      (fun N : Nat => ((binaryCutoff N : Real) + (decoderRadius h N : Real) + 1) /
        ((decoderRadius h N : Real) * (decoderRank c N : Real))) := by
    filter_upwards [(decoderRadius_real_atTop h hh).eventually (eventually_gt_atTop 0),
      (decoderRank_real_atTop c hc).eventually (eventually_gt_atTop 0)] with N hR hM
    field_simp [ne_of_gt hR, ne_of_gt hM]
  exact Filter.Tendsto.congr' heq (by simpa only [add_zero, zero_add, mul_zero] using hlim)

theorem preprocessing_eventually_le_evaluation_budget
    (h c K : Real) (hh : 0 < h) (hc : 0 < c) :
    Filter.Eventually (fun N : Nat =>
      K * ((binaryCutoff N : Real) + (decoderRadius h N : Real) + 1) <=
        (decoderRadius h N : Real) * (decoderRank c N : Real)) atTop := by
  have hlim := (preprocessing_div_decoder_evaluation_budget_tendsto_zero h c hh hc).const_mul K
  have hlim0 : Tendsto (fun N : Nat => K *
      (((binaryCutoff N : Real) + (decoderRadius h N : Real) + 1) /
        ((decoderRadius h N : Real) * (decoderRank c N : Real)))) atTop (nhds 0) := by
    simpa only [mul_zero] using hlim
  have hupper := hlim0.eventually (eventually_lt_nhds (by norm_num : (0 : Real) < 1))
  filter_upwards [hupper,
    (decoderRadius_real_atTop h hh).eventually (eventually_gt_atTop 0),
    (decoderRank_real_atTop c hc).eventually (eventually_gt_atTop 0)] with N hN hR hM
  have hscaled := mul_lt_mul_of_pos_right hN (mul_pos hR hM)
  have hcancel :
      (K * (((binaryCutoff N : Real) + (decoderRadius h N : Real) + 1) /
        ((decoderRadius h N : Real) * (decoderRank c N : Real)))) *
          ((decoderRadius h N : Real) * (decoderRank c N : Real)) =
      K * ((binaryCutoff N : Real) + (decoderRadius h N : Real) + 1) := by
    field_simp [ne_of_gt hR, ne_of_gt hM]
  rw [hcancel, one_mul] at hscaled
  exact le_of_lt hscaled

end PrimeFactorOscillations.PrimeClassDecoder

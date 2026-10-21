/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.PrimeClassDecoderRadius
import PrimeFactorOscillations.Helpers.PrimeClassDecoderRankLog

/-!
# Both losses in the growing-disc estimate

The sampling loss charges the complete degree times log radius. The model
tail charges the successor degree and its full exponential slope.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.PrimeClassDecoder

open Filter

noncomputable def decoderTailSlope (sigma h c A : Real) (N : Nat) : Real :=
  Real.log ((decoderRank c N + 1 : Nat) : Real) / sigma -
    Real.log (2 * (decoderRadius h N : Real)) - A

theorem decoder_sampling_growth_exponent_tendsto
    (h c : Real) (hh : 0 < h) (hc : 0 < c) :
    Tendsto (fun N : Nat => (decoderRank c N : Real) *
      Real.log (2 * (decoderRadius h N : Real)) / Real.log (N : Real))
      atTop (nhds (c * h)) := by
  have hlimit := (decoderRank_log_scale_tendsto c hc).mul
    (log_twice_decoderRadius_div_log_log_tendsto h hh)
  have hll : Tendsto (fun N : Nat => Real.log (Real.log (N : Real))) atTop atTop :=
    Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have heq : Filter.EventuallyEq atTop
      (fun N : Nat => ((decoderRank c N : Real) *
          Real.log (Real.log (N : Real)) / Real.log (N : Real)) *
        (Real.log (2 * (decoderRadius h N : Real)) / Real.log (Real.log (N : Real))))
      (fun N : Nat => (decoderRank c N : Real) *
        Real.log (2 * (decoderRadius h N : Real)) / Real.log (N : Real)) := by
    filter_upwards [hll.eventually (eventually_gt_atTop 0)] with N hN
    field_simp [ne_of_gt hN]
  exact Filter.Tendsto.congr' heq hlimit

theorem decoderRank_succ_log_scale_tendsto
    (c : Real) (hc : 0 < c) :
    Tendsto (fun N : Nat => ((decoderRank c N + 1 : Nat) : Real) *
      Real.log (Real.log (N : Real)) / Real.log (N : Real)) atTop (nhds c) := by
  have hsmall := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp
    (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := Real)))
  change Tendsto (fun N : Nat => Real.log (Real.log (N : Real)) /
    Real.log (N : Real)) atTop (nhds 0) at hsmall
  have h := (decoderRank_log_scale_tendsto c hc).add hsmall
  have heq : (fun N : Nat => (decoderRank c N : Real) *
        Real.log (Real.log (N : Real)) / Real.log (N : Real) +
      Real.log (Real.log (N : Real)) / Real.log (N : Real)) =
      (fun N : Nat => ((decoderRank c N + 1 : Nat) : Real) *
        Real.log (Real.log (N : Real)) / Real.log (N : Real)) := by
    funext N
    push_cast
    ring
  rw [heq] at h
  simpa only [add_zero] using h

theorem decoderTailSlope_log_scale_tendsto
    (sigma h c A : Real) (hh : 0 < h) (hc : 0 < c) :
    Tendsto (fun N : Nat => decoderTailSlope sigma h c A N /
      Real.log (Real.log (N : Real))) atTop (nhds (1 / sigma - h)) := by
  have hll : Tendsto (fun N : Nat => Real.log (Real.log (N : Real))) atTop atTop :=
    Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have hsmall : Tendsto (fun N : Nat => A / Real.log (Real.log (N : Real)))
      atTop (nhds 0) := tendsto_const_nhds.div_atTop hll
  have hlimit := (((log_decoderRank_succ_div_log_log_tendsto c hc).div_const sigma).sub
    (log_twice_decoderRadius_div_log_log_tendsto h hh)).sub hsmall
  have heq : (fun N : Nat =>
      (Real.log ((decoderRank c N + 1 : Nat) : Real) /
          Real.log (Real.log (N : Real))) / sigma -
        Real.log (2 * (decoderRadius h N : Real)) / Real.log (Real.log (N : Real)) -
        A / Real.log (Real.log (N : Real))) =
      (fun N : Nat => decoderTailSlope sigma h c A N /
        Real.log (Real.log (N : Real))) := by
    funext N
    unfold decoderTailSlope
    ring
  rw [heq] at hlimit
  simpa only [sub_zero] using hlimit

theorem decoder_tail_exponent_tendsto
    (sigma h c A : Real) (hh : 0 < h) (hc : 0 < c) :
    Tendsto (fun N : Nat => decoderTailSlope sigma h c A N *
      ((decoderRank c N + 1 : Nat) : Real) / Real.log (N : Real))
      atTop (nhds (c * (1 / sigma - h))) := by
  have hlimit := (decoderTailSlope_log_scale_tendsto sigma h c A hh hc).mul
    (decoderRank_succ_log_scale_tendsto c hc)
  have hll : Tendsto (fun N : Nat => Real.log (Real.log (N : Real))) atTop atTop :=
    Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have heq : Filter.EventuallyEq atTop
      (fun N : Nat => decoderTailSlope sigma h c A N / Real.log (Real.log (N : Real)) *
        (((decoderRank c N + 1 : Nat) : Real) *
          Real.log (Real.log (N : Real)) / Real.log (N : Real)))
      (fun N : Nat => decoderTailSlope sigma h c A N *
        ((decoderRank c N + 1 : Nat) : Real) / Real.log (N : Real)) := by
    filter_upwards [hll.eventually (eventually_gt_atTop 0)] with N hN
    field_simp [ne_of_gt hN]
  exact Filter.Tendsto.congr' heq (by simpa only [mul_comm] using hlimit)

theorem decoderTailSlope_atTop
    (sigma h c A : Real) (hh : 0 < h) (hc : 0 < c) (hdelta : 0 < 1 / sigma - h) :
    Tendsto (decoderTailSlope sigma h c A) atTop atTop := by
  have hll : Tendsto (fun N : Nat => Real.log (Real.log (N : Real))) atTop atTop :=
    Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have hlimit := Filter.Tendsto.atTop_mul_pos hdelta hll
    (decoderTailSlope_log_scale_tendsto sigma h c A hh hc)
  have heq : Filter.EventuallyEq atTop
      (fun N : Nat => Real.log (Real.log (N : Real)) *
        (decoderTailSlope sigma h c A N / Real.log (Real.log (N : Real))))
      (decoderTailSlope sigma h c A) := by
    filter_upwards [hll.eventually (eventually_gt_atTop 0)] with N hN
    field_simp [ne_of_gt hN]
  exact Filter.Tendsto.congr' heq hlimit

end PrimeFactorOscillations.PrimeClassDecoder

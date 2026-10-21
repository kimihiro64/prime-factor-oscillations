/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.PrimeClassDecoderLogCutoffs

/-!
# The exact decoder rank has the advertised logarithmic scale

The nested binary logarithms remain integer-valued throughout. The floor
in the rank formula is charged before taking its normalized limit.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.PrimeClassDecoder

open Filter

noncomputable def decoderRank (c : Real) (N : Nat) : Nat :=
  Nat.floor (c * ((binaryCutoff N : Real) / (iteratedBinaryCutoff N : Real)))

theorem iteratedBinaryCutoff_real_atTop :
    Tendsto (fun N : Nat => (iteratedBinaryCutoff N : Real)) atTop atTop :=
  binaryCutoff_real_atTop.comp binaryCutoff_atTop

theorem iteratedBinaryCutoff_div_log_log_tendsto :
    Tendsto (fun N : Nat => (iteratedBinaryCutoff N : Real) /
      Real.log (Real.log (N : Real))) atTop (nhds (1 / Real.log 2)) := by
  have hfirst := binaryCutoff_div_log_tendsto.comp binaryCutoff_atTop
  change Tendsto (fun N : Nat => (iteratedBinaryCutoff N : Real) /
    Real.log (binaryCutoff N : Real)) atTop (nhds (1 / Real.log 2)) at hfirst
  have h := hfirst.mul log_binaryCutoff_div_log_log_tendsto
  have heq : Filter.EventuallyEq atTop
      (fun N : Nat => (iteratedBinaryCutoff N : Real) / Real.log (binaryCutoff N : Real) *
        (Real.log (binaryCutoff N : Real) / Real.log (Real.log (N : Real))))
      (fun N : Nat => (iteratedBinaryCutoff N : Real) / Real.log (Real.log (N : Real))) := by
    filter_upwards [(Real.tendsto_log_atTop.comp binaryCutoff_real_atTop).eventually
      (eventually_gt_atTop 0)] with N hN
    change 0 < Real.log (binaryCutoff N : Real) at hN
    field_simp [ne_of_gt hN]
  exact Filter.Tendsto.congr' heq (by simpa only [mul_one] using h)

theorem real_self_div_log_atTop :
    Tendsto (fun x : Real => x / Real.log x) atTop atTop := by
  have hsmall := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  have hwithin : Tendsto (fun x : Real => Real.log x / x) atTop
      (nhdsWithin 0 (Set.Ioi 0)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine And.intro hsmall ?_
    filter_upwards [eventually_gt_atTop (1 : Real)] with x hx
    exact div_pos (Real.log_pos hx) (by linarith)
  have h := hwithin.inv_tendsto_nhdsGT_zero
  change Tendsto (fun x : Real => Inv.inv (Real.log x / x)) atTop atTop at h
  simpa only [inv_div] using h

theorem binaryCutoff_div_iterated_atTop :
    Tendsto (fun N : Nat => (binaryCutoff N : Real) /
      (iteratedBinaryCutoff N : Real)) atTop atTop := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hfirst := real_self_div_log_atTop.comp binaryCutoff_real_atTop
  change Tendsto (fun N : Nat => (binaryCutoff N : Real) /
    Real.log (binaryCutoff N : Real)) atTop atTop at hfirst
  have hratio := binaryCutoff_div_log_tendsto.comp binaryCutoff_atTop
  change Tendsto (fun N : Nat => (iteratedBinaryCutoff N : Real) /
    Real.log (binaryCutoff N : Real)) atTop (nhds (1 / Real.log 2)) at hratio
  have hsecond : Tendsto (fun N : Nat => Real.log (binaryCutoff N : Real) /
      (iteratedBinaryCutoff N : Real)) atTop (nhds (Real.log 2)) := by
    have h := (tendsto_const_nhds : Tendsto (fun _ : Nat => (1 : Real)) atTop (nhds 1)).div
      hratio (by positivity : Not ((1 : Real) / Real.log 2 = 0))
    change Tendsto (fun N : Nat => (1 : Real) / ((iteratedBinaryCutoff N : Real) /
      Real.log (binaryCutoff N : Real))) atTop (nhds (1 / (1 / Real.log 2))) at h
    simpa only [one_div, inv_div, div_one, inv_inv] using h
  have h := Filter.Tendsto.atTop_mul_pos hlog2 hfirst hsecond
  have heq : Filter.EventuallyEq atTop
      (fun N : Nat => (binaryCutoff N : Real) / Real.log (binaryCutoff N : Real) *
        (Real.log (binaryCutoff N : Real) / (iteratedBinaryCutoff N : Real)))
      (fun N : Nat => (binaryCutoff N : Real) / (iteratedBinaryCutoff N : Real)) := by
    filter_upwards [(Real.tendsto_log_atTop.comp binaryCutoff_real_atTop).eventually
      (eventually_gt_atTop 0)] with N hN
    change 0 < Real.log (binaryCutoff N : Real) at hN
    field_simp [ne_of_gt hN]
  exact Filter.Tendsto.congr' heq h

theorem decoderRank_log_scale_tendsto
    (c : Real) (hc : 0 < c) :
    Tendsto (fun N : Nat => (decoderRank c N : Real) *
      Real.log (Real.log (N : Real)) / Real.log (N : Real)) atTop (nhds c) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hfloor := (tendsto_nat_floor_mul_div_atTop hc.le).comp
    binaryCutoff_div_iterated_atTop
  change Tendsto (fun N : Nat => (decoderRank c N : Real) /
    ((binaryCutoff N : Real) / (iteratedBinaryCutoff N : Real))) atTop (nhds c) at hfloor
  have h := (hfloor.mul binaryCutoff_div_log_tendsto).div
    iteratedBinaryCutoff_div_log_log_tendsto
    (by positivity : Not ((1 : Real) / Real.log 2 = 0))
  have hlog : Tendsto (fun N : Nat => Real.log (N : Real)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have heq : Filter.EventuallyEq atTop
      (fun N : Nat => ((decoderRank c N : Real) /
          ((binaryCutoff N : Real) / (iteratedBinaryCutoff N : Real)) *
        ((binaryCutoff N : Real) / Real.log (N : Real))) /
          ((iteratedBinaryCutoff N : Real) / Real.log (Real.log (N : Real))))
      (fun N : Nat => (decoderRank c N : Real) *
        Real.log (Real.log (N : Real)) / Real.log (N : Real)) := by
    filter_upwards [binaryCutoff_real_atTop.eventually (eventually_gt_atTop 0),
      iteratedBinaryCutoff_real_atTop.eventually (eventually_gt_atTop 0),
      hlog.eventually (eventually_gt_atTop 0),
      (Real.tendsto_log_atTop.comp hlog).eventually (eventually_gt_atTop 0)] with N hU hV hN hNN
    field_simp
  apply Filter.Tendsto.congr' heq
  convert h using 1
  field_simp

end PrimeFactorOscillations.PrimeClassDecoder

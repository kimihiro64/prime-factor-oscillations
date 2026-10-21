/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.PrimeClassDecoderRankCutoffs

/-!
# The logarithm of the actual rank cutoff

The nested cutoff and both integer roundings contribute vanishing terms
after division by log log N. The successor is retained in the tail bound.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.PrimeClassDecoder

open Filter

theorem decoderRank_real_atTop
    (c : Real) (hc : 0 < c) :
    Tendsto (fun N : Nat => (decoderRank c N : Real)) atTop atTop := by
  have hp := Filter.Tendsto.const_mul_atTop hc binaryCutoff_div_iterated_atTop
  have hfloor := (Asymptotics.isEquivalent_nat_floor (R := Real)).comp_tendsto hp
  exact hfloor.symm.tendsto_atTop hp

theorem log_iteratedBinaryCutoff_div_log_log_tendsto_zero :
    Tendsto (fun N : Nat => Real.log (iteratedBinaryCutoff N : Real) /
      Real.log (Real.log (N : Real))) atTop (nhds 0) := by
  have hsmall := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp
    iteratedBinaryCutoff_real_atTop
  change Tendsto (fun N : Nat => Real.log (iteratedBinaryCutoff N : Real) /
    (iteratedBinaryCutoff N : Real)) atTop (nhds 0) at hsmall
  have h := hsmall.mul iteratedBinaryCutoff_div_log_log_tendsto
  have heq : Filter.EventuallyEq atTop
      (fun N : Nat => Real.log (iteratedBinaryCutoff N : Real) /
          (iteratedBinaryCutoff N : Real) *
        ((iteratedBinaryCutoff N : Real) / Real.log (Real.log (N : Real))))
      (fun N : Nat => Real.log (iteratedBinaryCutoff N : Real) /
        Real.log (Real.log (N : Real))) := by
    filter_upwards [iteratedBinaryCutoff_real_atTop.eventually (eventually_gt_atTop 0)]
      with N hN
    field_simp [ne_of_gt hN]
  exact Filter.Tendsto.congr' heq (by simpa only [zero_mul] using h)

theorem log_decoderRank_argument_div_log_log_tendsto
    (c : Real) (hc : 0 < c) :
    Tendsto (fun N : Nat => Real.log (c * ((binaryCutoff N : Real) /
      (iteratedBinaryCutoff N : Real))) / Real.log (Real.log (N : Real)))
      atTop (nhds 1) := by
  have hll : Tendsto (fun N : Nat => Real.log (Real.log (N : Real))) atTop atTop :=
    Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have hsmall : Tendsto (fun N : Nat => Real.log c /
      Real.log (Real.log (N : Real))) atTop (nhds 0) := tendsto_const_nhds.div_atTop hll
  have h := (hsmall.add log_binaryCutoff_div_log_log_tendsto).sub
    log_iteratedBinaryCutoff_div_log_log_tendsto_zero
  have heq : Filter.EventuallyEq atTop
      (fun N : Nat => Real.log c / Real.log (Real.log (N : Real)) +
        Real.log (binaryCutoff N : Real) / Real.log (Real.log (N : Real)) -
        Real.log (iteratedBinaryCutoff N : Real) / Real.log (Real.log (N : Real)))
      (fun N : Nat => Real.log (c * ((binaryCutoff N : Real) /
        (iteratedBinaryCutoff N : Real))) / Real.log (Real.log (N : Real))) := by
    filter_upwards [binaryCutoff_real_atTop.eventually (eventually_gt_atTop 0),
      iteratedBinaryCutoff_real_atTop.eventually (eventually_gt_atTop 0)] with N hU hV
    rw [Real.log_mul (ne_of_gt hc) (div_ne_zero (ne_of_gt hU) (ne_of_gt hV)),
      Real.log_div (ne_of_gt hU) (ne_of_gt hV)]
    ring
  exact Filter.Tendsto.congr' heq (by simpa only [zero_add, sub_zero] using h)

theorem log_decoderRank_succ_div_log_log_tendsto
    (c : Real) (hc : 0 < c) :
    Tendsto (fun N : Nat => Real.log ((decoderRank c N + 1 : Nat) : Real) /
      Real.log (Real.log (N : Real))) atTop (nhds 1) := by
  simp only [Nat.cast_add, Nat.cast_one]
  let f := fun N : Nat => c * ((binaryCutoff N : Real) / (iteratedBinaryCutoff N : Real))
  have hp : Tendsto f atTop atTop :=
    Filter.Tendsto.const_mul_atTop hc binaryCutoff_div_iterated_atTop
  have hnorm : Tendsto (fun N : Nat => norm (f N)) atTop atTop := by
    apply Filter.Tendsto.congr' _ hp
    filter_upwards [hp.eventually (eventually_ge_atTop 0)] with N hN
    simp only [Real.norm_eq_abs, abs_of_nonneg hN]
  have hfloor := (Asymptotics.isEquivalent_nat_floor (R := Real)).comp_tendsto hp
  have hequiv := (hfloor.add_const_of_norm_tendsto_atTop (c := (1 : Real)) hnorm).log hp
  have hlp := Real.tendsto_log_atTop.comp hp
  have hn : Filter.Eventually (fun N : Nat => Not (Real.log (f N) = 0)) atTop := by
    filter_upwards [hlp.eventually (eventually_gt_atTop 0)] with N hN
    exact ne_of_gt hN
  have hfirst := (Asymptotics.isEquivalent_iff_tendsto_one hn).mp hequiv
  change Tendsto (fun N : Nat => Real.log ((decoderRank c N : Real) + 1) /
    Real.log (f N)) atTop (nhds 1) at hfirst
  have h := hfirst.mul (log_decoderRank_argument_div_log_log_tendsto c hc)
  have heq : Filter.EventuallyEq atTop
      (fun N : Nat => Real.log ((decoderRank c N : Real) + 1) / Real.log (f N) *
        (Real.log (f N) / Real.log (Real.log (N : Real))))
      (fun N : Nat => Real.log ((decoderRank c N : Real) + 1) /
        Real.log (Real.log (N : Real))) := by
    filter_upwards [hn] with N hN
    field_simp [hN]
  exact Filter.Tendsto.congr' heq (by simpa only [one_mul] using h)

end PrimeFactorOscillations.PrimeClassDecoder

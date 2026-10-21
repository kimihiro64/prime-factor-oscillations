/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.PrimeClassDecoderRankCutoffs

/-!
# Integer radii retain the full power parameter

For every positive real h the floored radius tends to infinity, and the
logarithm of twice that radius has normalized limit h. No h < 1 restriction
is introduced by rounding the radius.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.PrimeClassDecoder

open Filter

noncomputable def decoderRadius (h : Real) (N : Nat) : Nat :=
  Nat.floor ((binaryCutoff N : Real) ^ h)

theorem decoderRadius_real_atTop
    (h : Real) (hh : 0 < h) :
    Tendsto (fun N : Nat => (decoderRadius h N : Real)) atTop atTop := by
  have hp := (tendsto_rpow_atTop hh).comp binaryCutoff_real_atTop
  have heq := (Asymptotics.isEquivalent_nat_floor (R := Real)).comp_tendsto hp
  exact heq.symm.tendsto_atTop hp

theorem log_decoderRadius_div_log_log_tendsto
    (h : Real) (hh : 0 < h) :
    Tendsto (fun N : Nat => Real.log (decoderRadius h N : Real) /
      Real.log (Real.log (N : Real))) atTop (nhds h) := by
  have hp := (tendsto_rpow_atTop hh).comp binaryCutoff_real_atTop
  have hlp := Real.tendsto_log_atTop.comp hp
  have hequiv := ((Asymptotics.isEquivalent_nat_floor (R := Real)).comp_tendsto hp).log hp
  have hn : Filter.Eventually (fun N : Nat =>
      Not (Real.log ((binaryCutoff N : Real) ^ h) = 0)) atTop := by
    filter_upwards [hlp.eventually (eventually_gt_atTop 0)] with N hN
    exact ne_of_gt hN
  have hfirst := (Asymptotics.isEquivalent_iff_tendsto_one hn).mp hequiv
  change Tendsto (fun N : Nat => Real.log (decoderRadius h N : Real) /
    Real.log ((binaryCutoff N : Real) ^ h)) atTop (nhds 1) at hfirst
  have hlimit := (hfirst.mul_const h).mul log_binaryCutoff_div_log_log_tendsto
  have heq : Filter.EventuallyEq atTop
      (fun N : Nat => Real.log (decoderRadius h N : Real) /
          Real.log ((binaryCutoff N : Real) ^ h) * h *
        (Real.log (binaryCutoff N : Real) / Real.log (Real.log (N : Real))))
      (fun N : Nat => Real.log (decoderRadius h N : Real) /
        Real.log (Real.log (N : Real))) := by
    filter_upwards [binaryCutoff_real_atTop.eventually (eventually_gt_atTop 1)] with N hN
    have hU : (0 : Real) < (binaryCutoff N : Real) := by linarith
    have hlogU : 0 < Real.log (binaryCutoff N : Real) := Real.log_pos hN
    rw [Real.log_rpow hU]
    field_simp [ne_of_gt hh, ne_of_gt hlogU]
  exact Filter.Tendsto.congr' heq (by simpa only [one_mul, mul_one] using hlimit)

theorem log_twice_decoderRadius_div_log_log_tendsto
    (h : Real) (hh : 0 < h) :
    Tendsto (fun N : Nat => Real.log (2 * (decoderRadius h N : Real)) /
      Real.log (Real.log (N : Real))) atTop (nhds h) := by
  have hll : Tendsto (fun N : Nat => Real.log (Real.log (N : Real))) atTop atTop :=
    Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have hsmall : Tendsto (fun N : Nat => Real.log 2 /
      Real.log (Real.log (N : Real))) atTop (nhds 0) := tendsto_const_nhds.div_atTop hll
  have hlimit := hsmall.add (log_decoderRadius_div_log_log_tendsto h hh)
  have heq : Filter.EventuallyEq atTop
      (fun N : Nat => Real.log 2 / Real.log (Real.log (N : Real)) +
        Real.log (decoderRadius h N : Real) / Real.log (Real.log (N : Real)))
      (fun N : Nat => Real.log (2 * (decoderRadius h N : Real)) /
        Real.log (Real.log (N : Real))) := by
    filter_upwards [(decoderRadius_real_atTop h hh).eventually (eventually_gt_atTop 0)]
      with N hN
    rw [Real.log_mul (by norm_num : Not ((2 : Real) = 0)) (ne_of_gt hN), add_div]
  exact Filter.Tendsto.congr' heq (by simpa only [zero_add] using hlimit)

end PrimeFactorOscillations.PrimeClassDecoder

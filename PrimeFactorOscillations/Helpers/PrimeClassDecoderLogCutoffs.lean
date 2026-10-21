/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.FieldSimp
import PrimeFactorOscillations.Helpers.PrimeClassDecoderIntegerProbes

/-!
# Literal integer logarithmic cutoffs for the decoder

The cutoffs use Nat.log, so these limits apply to the exact integer
selectors in the paper, rather than to substituted real logarithms.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.PrimeClassDecoder

open Filter

def binaryCutoff (N : Nat) : Nat := Nat.log 2 N

def iteratedBinaryCutoff (N : Nat) : Nat := Nat.log 2 (binaryCutoff N)

theorem binaryCutoff_equivalent_logb :
    Asymptotics.IsEquivalent atTop (fun N : Nat => (binaryCutoff N : Real))
      (fun N : Nat => Real.logb 2 (N : Real)) := by
  have hlog : Tendsto (fun N : Nat => Real.logb 2 (N : Real)) atTop atTop :=
    (Real.tendsto_logb_atTop (by norm_num : (1 : Real) < 2)).comp
      tendsto_natCast_atTop_atTop
  have h := (Asymptotics.isEquivalent_nat_floor (R := Real)).comp_tendsto hlog
  have heq : (fun N : Nat => (Nat.floor (Real.logb 2 (N : Real)) : Real)) =
      (fun N : Nat => (binaryCutoff N : Real)) := by
    funext N
    exact congrArg (fun n : Nat => (n : Real)) (Real.natFloor_logb_natCast 2 N)
  change Asymptotics.IsEquivalent atTop
    (fun N : Nat => (Nat.floor (Real.logb 2 (N : Real)) : Real))
    (fun N : Nat => Real.logb 2 (N : Real)) at h
  rwa [heq] at h

theorem binaryCutoff_real_atTop :
    Tendsto (fun N : Nat => (binaryCutoff N : Real)) atTop atTop := by
  have hlog : Tendsto (fun N : Nat => Real.logb 2 (N : Real)) atTop atTop :=
    (Real.tendsto_logb_atTop (by norm_num : (1 : Real) < 2)).comp
      tendsto_natCast_atTop_atTop
  exact binaryCutoff_equivalent_logb.symm.tendsto_atTop hlog

theorem binaryCutoff_atTop : Tendsto binaryCutoff atTop atTop := by
  apply tendsto_atTop.mpr
  intro n
  filter_upwards [binaryCutoff_real_atTop.eventually (eventually_ge_atTop (n : Real))]
    with N hN
  exact_mod_cast hN

theorem binaryCutoff_div_log_tendsto :
    Tendsto (fun N : Nat => (binaryCutoff N : Real) / Real.log (N : Real))
      atTop (nhds (1 / Real.log 2)) := by
  have hlog : Tendsto (fun N : Nat => Real.log (N : Real)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlogb : Tendsto (fun N : Nat => Real.logb 2 (N : Real)) atTop atTop :=
    (Real.tendsto_logb_atTop (by norm_num : (1 : Real) < 2)).comp
      tendsto_natCast_atTop_atTop
  have hfloor := (tendsto_nat_floor_div_atTop (R := Real)).comp hlogb
  have hlimit := hfloor.div_const (Real.log 2)
  have heq : Filter.EventuallyEq atTop
      (fun N : Nat => ((Nat.floor (Real.logb 2 (N : Real)) : Nat) : Real) /
        Real.logb 2 (N : Real) / Real.log 2)
      (fun N : Nat => (binaryCutoff N : Real) / Real.log (N : Real)) := by
    filter_upwards [hlog.eventually (eventually_gt_atTop 0)] with N hN
    rw [show (2 : Real) = ((2 : Nat) : Real) from rfl, Real.natFloor_logb_natCast]
    simp only [binaryCutoff, Real.logb]
    field_simp [ne_of_gt hN, ne_of_gt (Real.log_pos (by norm_num : (1 : Real) < 2))]
  exact Filter.Tendsto.congr' heq hlimit

theorem log_binaryCutoff_div_log_log_tendsto :
    Tendsto (fun N : Nat => Real.log (binaryCutoff N : Real) /
      Real.log (Real.log (N : Real))) atTop (nhds 1) := by
  have hlog : Tendsto (fun N : Nat => Real.log (N : Real)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hll : Tendsto (fun N : Nat => Real.log (Real.log (N : Real))) atTop atTop :=
    Real.tendsto_log_atTop.comp hlog
  have hlogb : Tendsto (fun N : Nat => Real.logb 2 (N : Real)) atTop atTop :=
    (Real.tendsto_logb_atTop (by norm_num : (1 : Real) < 2)).comp
      tendsto_natCast_atTop_atTop
  have hloglogb := Real.tendsto_log_atTop.comp hlogb
  have hequiv := binaryCutoff_equivalent_logb.log hlogb
  have hz : Filter.Eventually (fun N : Nat =>
      Not (Real.log (Real.logb 2 (N : Real)) = 0)) atTop := by
    filter_upwards [hloglogb.eventually (eventually_gt_atTop 0)] with N hN
    exact ne_of_gt hN
  have hfirst := (Asymptotics.isEquivalent_iff_tendsto_one hz).mp hequiv
  change Tendsto (fun N : Nat => Real.log (binaryCutoff N : Real) /
    Real.log (Real.logb 2 (N : Real))) atTop (nhds 1) at hfirst
  have hsmall : Tendsto (fun N : Nat => Real.log (Real.log 2) /
      Real.log (Real.log (N : Real))) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop hll
  have hsecond : Tendsto (fun N : Nat =>
      Real.log (Real.logb 2 (N : Real)) / Real.log (Real.log (N : Real)))
      atTop (nhds 1) := by
    have h : Tendsto (fun N : Nat =>
        (1 : Real) - Real.log (Real.log 2) / Real.log (Real.log (N : Real)))
        atTop (nhds (1 - 0)) := tendsto_const_nhds.sub hsmall
    have heq : Filter.EventuallyEq atTop
        (fun N : Nat => 1 - Real.log (Real.log 2) / Real.log (Real.log (N : Real)))
        (fun N : Nat => Real.log (Real.logb 2 (N : Real)) /
          Real.log (Real.log (N : Real))) := by
      filter_upwards [hlog.eventually (eventually_gt_atTop 0),
        hll.eventually (eventually_gt_atTop 0)] with N hN hNN
      rw [Real.logb, Real.log_div (ne_of_gt hN) (ne_of_gt (Real.log_pos (by norm_num)))]
      field_simp
    exact Filter.Tendsto.congr' heq (by simpa only [sub_zero] using h)
  have hboth := hfirst.mul hsecond
  have heq : Filter.EventuallyEq atTop
      (fun N : Nat => Real.log (binaryCutoff N : Real) /
          Real.log (Real.logb 2 (N : Real)) *
        (Real.log (Real.logb 2 (N : Real)) / Real.log (Real.log (N : Real))))
      (fun N : Nat => Real.log (binaryCutoff N : Real) /
        Real.log (Real.log (N : Real))) := by
    filter_upwards [hz] with N hN
    field_simp
  exact Filter.Tendsto.congr' heq (by simpa only [one_mul] using hboth)

end PrimeFactorOscillations.PrimeClassDecoder

/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.ThetaEndpointAsymptotic
import PrimeFactorOscillations.Mathlib.Analysis.SpecialFunctions.Log.DoubleExponential

/-!
# Double-logarithm normalization of the actual theta endpoint count

The actual PNT endpoint asymptotic yields a quantitative logarithmic error.
The threshold is uniform in the separate positive-rank comparison parameter.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations

open Filter

theorem eventually_primeThetaEndpointCount_loglog_error :
    Filter.Eventually (fun v : Real =>
      1 < (primeThetaEndpointCount (Real.exp (Real.exp v)) : Real) /\
      abs (Real.log (Real.log (primeThetaEndpointCount (Real.exp (Real.exp v)) : Real)) - v) <=
        4 * v / Real.exp v) atTop := by
  have hgrow : Tendsto (fun v : Real => Real.exp (Real.exp v)) atTop atTop := by
    simpa only [Function.comp_def] using Real.tendsto_exp_atTop.comp Real.tendsto_exp_atTop
  have hlim := tendsto_primeThetaEndpointCount_div_mainTerm.comp hgrow
  have hL := hlim.eventually (lt_mem_nhds (show (1 : Real) / 2 < 1 by norm_num))
  have hU := hlim.eventually (gt_mem_nhds (show (1 : Real) < 2 by norm_num))
  filter_upwards [hL, hU, eventually_ge_atTop (16 : Real)] with v hL hU hv
  simp only [Function.comp_apply, Real.log_exp] at hL hU
  have hw : 0 < Real.exp v := Real.exp_pos _
  have hT : 0 < Real.exp (Real.exp v) := Real.exp_pos _
  have hmain : 0 < Real.exp (Real.exp v) / Real.exp v := div_pos hT hw
  have hcancel :
      ((primeThetaEndpointCount (Real.exp (Real.exp v)) : Real) /
        (Real.exp (Real.exp v) / Real.exp v)) *
          (Real.exp (Real.exp v) / Real.exp v) =
            primeThetaEndpointCount (Real.exp (Real.exp v)) := by field_simp
  have hl := mul_lt_mul_of_pos_right hL hmain
  have hu := mul_lt_mul_of_pos_right hU hmain
  rw [hcancel] at hl hu
  have hlower : Real.exp (Real.exp v) / (2 * Real.exp v) <=
      (primeThetaEndpointCount (Real.exp (Real.exp v)) : Real) := by
    calc
      Real.exp (Real.exp v) / (2 * Real.exp v) =
          ((1 : Real) / 2) * (Real.exp (Real.exp v) / Real.exp v) := by ring
      _ <= (primeThetaEndpointCount (Real.exp (Real.exp v)) : Real) := hl.le
  have hw2 : (2 : Real) <= Real.exp v := by linarith [Real.add_one_le_exp v]
  have hupper : (primeThetaEndpointCount (Real.exp (Real.exp v)) : Real) <=
      Real.exp (Real.exp v) := by
    calc
      (primeThetaEndpointCount (Real.exp (Real.exp v)) : Real) <=
          2 * (Real.exp (Real.exp v) / Real.exp v) := hu.le
      _ <= Real.exp v * (Real.exp (Real.exp v) / Real.exp v) :=
        mul_le_mul_of_nonneg_right hw2 hmain.le
      _ = Real.exp (Real.exp v) := by field_simp
  exact Real.logLog_exp_exp_envelope _ v hv hlower hupper

theorem exists_primeThetaEndpointCount_loglog_rank_error :
    exists V0 : Real, 16 <= V0 /\ forall v : Real, V0 <= v ->
      forall a : Real, 0 <= a -> forall r : Nat, 0 < r -> (r : Real) <= a * v ->
        1 < (primeThetaEndpointCount (Real.exp (Real.exp v)) : Real) /\
        abs (Real.log (Real.log (primeThetaEndpointCount (Real.exp (Real.exp v)) : Real)) - v) <=
          16 * a / (r : Real) := by
  choose V0 hV0 using eventually_primeThetaEndpointCount_loglog_error.exists_forall_of_atTop
  refine Exists.intro (max 16 V0) (And.intro (le_max_left _ _) ?_)
  intro v hv a ha r hr hrv
  have hv16 : 16 <= v := (le_max_left _ _).trans hv
  have hv0 : 0 <= v := by linarith
  have hrR : (0 : Real) < r := by exact_mod_cast hr
  have hw : 0 < Real.exp v := Real.exp_pos _
  have h := hV0 v ((le_max_right _ _).trans hv)
  have hhalf : v / 2 <= Real.exp (v / 2) := by
    linarith only [Real.add_one_le_exp (v / 2)]
  have hquad : v ^ 2 <= 4 * Real.exp v := by
    have hprod := mul_nonneg (sub_nonneg.mpr hhalf)
      (add_nonneg (Real.exp_pos (v / 2)).le (by positivity : 0 <= v / 2))
    have heq : Real.exp (v / 2) ^ 2 = Real.exp v := by
      rw [pow_two, <- Real.exp_add]
      congr 1
      ring
    nlinarith only [hprod, heq]
  have hproduct : (4 * v / Real.exp v) * (r : Real) <= 16 * a := by
    calc
      (4 * v / Real.exp v) * (r : Real) <= (4 * v / Real.exp v) * (a * v) :=
        mul_le_mul_of_nonneg_left hrv (by positivity)
      _ = (4 * a * v ^ 2) / Real.exp v := by ring
      _ <= (4 * a * (4 * Real.exp v)) / Real.exp v :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hquad (by positivity)) hw.le
      _ = 16 * a := by field_simp; ring
  have herror : 4 * v / Real.exp v <= (16 * a) / (r : Real) := by
    apply le_of_mul_le_mul_right _ hrR
    have hcancel : ((16 * a) / (r : Real)) * r = 16 * a := by field_simp
    rw [hcancel]
    exact hproduct
  exact And.intro h.1 (h.2.trans herror)

theorem exists_primeThetaEndpointCount_near_rank_loglog_error
    (s A : Real) (hs : 0 < s) (_hA : 0 <= A) :
    exists r0 : Nat, 0 < r0 /\ forall r : Nat, r0 <= r ->
      forall u : Real, abs (u - (r : Real) / s) <= A ->
        1 < (primeThetaEndpointCount
          (Real.exp (Real.exp (u - Real.eulerMascheroniConstant))) : Real) /\
        abs (Real.log (Real.log (primeThetaEndpointCount
          (Real.exp (Real.exp (u - Real.eulerMascheroniConstant))) : Real)) -
            (u - Real.eulerMascheroniConstant)) <= 32 * s / (r : Real) := by
  choose V0 hV0 hlog using exists_primeThetaEndpointCount_loglog_rank_error
  choose n0 hn0 using exists_nat_ge (max
    (s * (V0 + A + Real.eulerMascheroniConstant))
    (2 * s * (A + Real.eulerMascheroniConstant)))
  refine Exists.intro (n0 + 1) (And.intro (Nat.zero_lt_succ n0) ?_)
  intro r hr u hu
  have hrpos : 0 < r := (Nat.zero_lt_succ n0).trans_le hr
  have hnR : (n0 : Real) <= r := by exact_mod_cast (Nat.le_succ n0).trans hr
  have hlarge1 : s * (V0 + A + Real.eulerMascheroniConstant) <= (r : Real) :=
    (le_max_left _ _).trans (hn0.trans hnR)
  have hlarge2 : 2 * s * (A + Real.eulerMascheroniConstant) <= (r : Real) :=
    (le_max_right _ _).trans (hn0.trans hnR)
  have hprod := mul_le_mul_of_nonneg_left (abs_le.mp hu).1 hs.le
  have hcancel : ((r : Real) / s) * s = r := by field_simp
  have hv : V0 <= u - Real.eulerMascheroniConstant := by
    apply le_of_mul_le_mul_left _ hs
    nlinarith only [hprod, hcancel, hlarge1]
  have hrv : (r : Real) <= (2 * s) * (u - Real.eulerMascheroniConstant) := by
    nlinarith only [hprod, hcancel, hlarge2]
  have h := hlog (u - Real.eulerMascheroniConstant) hv (2 * s) (by positivity) r hrpos hrv
  have hfactor : (16 : Real) * (2 * s) = 32 * s := by ring
  simpa only [hfactor] using h

end PrimeFactorOscillations

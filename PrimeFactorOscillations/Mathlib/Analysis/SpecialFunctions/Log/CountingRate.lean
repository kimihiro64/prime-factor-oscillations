/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Mathlib.Analysis.SpecialFunctions.Log.DoubleLogGauge

/-! # Growth exponents of nonnegative counts bounded by their endpoint -/

set_option autoImplicit false
set_option Elab.async false

namespace Real

/-- Explicit eventual lower levels for the prime-value normalization. -/
theorem eventually_le_log_log_nat (A : Real) :
    exists K : Nat, forall X : Nat, K <= X ->
      A <= Real.log (Real.log (X : Real)) := by
  choose K hK using exists_nat_gt (Real.exp (Real.exp A))
  refine Exists.intro K ?_
  intro X hX
  have hXR : (K : Real) <= X := by exact_mod_cast hX
  have hlarge := hK.le.trans hXR
  have hlog := Real.log_le_log (Real.exp_pos _) hlarge
  rw [Real.log_exp] at hlog
  have hloglog := Real.log_le_log (Real.exp_pos _) hlog
  simpa only [Real.log_exp] using hloglog

/-- Linear count growth gives every shifted-model coefficient strictly above one. -/
theorem eventually_linear_count_le_double_exp_log_log
    (n : Nat -> Real) (hn : forall X, 0 <= n X)
    (hlinear : forall X : Nat, n X <= X) (b : Real) (hb : 1 < b) :
    exists K : Nat, forall X : Nat, K <= X ->
      3 + n X <= Real.exp (Real.exp (b * Real.log (Real.log (X : Real)))) := by
  have hd : 0 < b - 1 := by linarith
  choose K hK using eventually_le_log_log_nat (max 1 (Real.log 2 / (b - 1)))
  refine Exists.intro (max 3 K) ?_
  intro X hX
  have hX3 : (3 : Real) <= X := by exact_mod_cast (le_max_left 3 K).trans hX
  have hXp : (0 : Real) < X := by linarith
  have hLX : 0 < Real.log (X : Real) := Real.log_pos (by linarith)
  have hNN := hn X
  have hNX := hlinear X
  have hsquare : 3 + n X <= (X : Real) * X := by
    nlinarith only [hX3, hNX, sq_nonneg ((X : Real) - 2)]
  have hlog := Real.log_le_log (show 0 < 3 + n X by linarith) hsquare
  rw [Real.log_mul (ne_of_gt hXp) (ne_of_gt hXp)] at hlog
  have hloglog := Real.log_le_log (Real.log_pos (show 1 < 3 + n X by linarith)) hlog
  rw [show Real.log (X : Real) + Real.log (X : Real) =
    2 * Real.log (X : Real) by ring,
    Real.log_mul (by norm_num) (ne_of_gt hLX)] at hloglog
  have hthreshold := (le_max_right 1 (Real.log 2 / (b - 1))).trans
    (hK X ((le_max_right 3 K).trans hX))
  have hmul := mul_le_mul_of_nonneg_right hthreshold hd.le
  have hc : (Real.log 2 / (b - 1)) * (b - 1) = Real.log 2 := by
    field_simp [ne_of_gt hd]
  rw [hc] at hmul
  apply (log_log_add_three_le_iff_double_exp (n X)
    (b * Real.log (Real.log (X : Real))) hNN).mp
  nlinarith only [hloglog, hmul]

/-- Nonnegative counts with a finite model upper bound have nonnegative
prime-value growth exponent, including counts that stay bounded or vanish. -/
theorem nonneg_limsup_log_log_count (n : Nat -> Real)
    (hn : forall X, 0 <= n X)
    (hu : exists A : Real, exists K : Nat, forall X : Nat, K <= X ->
      3 + n X <= Real.exp (Real.exp (A * Real.log (Real.log (X : Real))))) :
    0 <= Filter.limsup
      (fun X : Nat => Real.log (Real.log (3 + n X)) /
        Real.log (Real.log (X : Real))) Filter.atTop := by
  apply (le_limsup_log_log_div_gauge_iff n
    (fun X : Nat => Real.log (Real.log (X : Real)))
    hn (eventually_le_log_log_nat 1) hu 0).mpr
  intro a ha K
  choose Ka hKa using eventually_le_log_log_nat
    ((Real.log (Real.log 2) - 1) / a)
  let X := max K Ka
  have ht := hKa X (le_max_right K Ka)
  have hm := mul_le_mul_of_nonpos_left ht ha.le
  have hc : a * ((Real.log (Real.log 2) - 1) / a) =
      Real.log (Real.log 2) - 1 := by field_simp [ne_of_lt ha]
  have hinner : a * Real.log (Real.log (X : Real)) < Real.log (Real.log 2) := by
    nlinarith only [hm, hc]
  have he := Real.exp_lt_exp.mpr (Real.exp_lt_exp.mpr hinner)
  rw [Real.exp_log (Real.log_pos (by norm_num : (1 : Real) < 2)),
    Real.exp_log (by norm_num : (0 : Real) < 2)] at he
  refine Exists.intro X (And.intro (le_max_left K Ka) ?_)
  exact he.trans (show (2 : Real) < 3 + n X by linarith only [hn X])

/-- Every nonnegative count bounded by X has exponent in the closed unit interval. -/
theorem limsup_log_log_linear_count_bounds (n : Nat -> Real)
    (hn : forall X, 0 <= n X) (hlinear : forall X : Nat, n X <= X) :
    0 <= Filter.limsup
      (fun X : Nat => Real.log (Real.log (3 + n X)) /
        Real.log (Real.log (X : Real))) Filter.atTop /\
    Filter.limsup
      (fun X : Nat => Real.log (Real.log (3 + n X)) /
        Real.log (Real.log (X : Real))) Filter.atTop <= 1 := by
  have hmodel := eventually_linear_count_le_double_exp_log_log n hn hlinear 2 (by norm_num)
  have hu : exists A : Real, exists K : Nat, forall X : Nat, K <= X ->
      3 + n X <= Real.exp (Real.exp (A * Real.log (Real.log (X : Real)))) :=
    Exists.intro (2 : Real) hmodel
  refine And.intro (nonneg_limsup_log_log_count n hn hu) ?_
  apply (limsup_log_log_div_gauge_le_iff n
    (fun X : Nat => Real.log (Real.log (X : Real)))
    hn (eventually_le_log_log_nat 1) hu 1).mpr
  exact fun b hb => eventually_linear_count_le_double_exp_log_log n hn hlinear b hb

/-- A uniformly bounded count has zero prime-value growth exponent. -/
theorem limsup_log_log_bounded_count_eq_zero
    (n : Nat -> Real) (hn : forall X, 0 <= n X)
    (C : Real) (hC : 0 <= C) (hbound : forall X, n X <= C) :
    Filter.limsup
      (fun X : Nat => Real.log (Real.log (3 + n X)) /
        Real.log (Real.log (X : Real))) Filter.atTop = 0 := by
  have hmodel : forall b : Real, 0 < b -> exists K : Nat,
      forall X : Nat, K <= X ->
        3 + n X <= Real.exp (Real.exp (b * Real.log (Real.log (X : Real)))) := by
    intro b hb
    choose K hK using eventually_le_log_log_nat (Real.log (Real.log (3 + C)) / b)
    refine Exists.intro K ?_
    intro X hX
    have hm := mul_le_mul_of_nonneg_right (hK X hX) hb.le
    have hc : (Real.log (Real.log (3 + C)) / b) * b =
        Real.log (Real.log (3 + C)) := by field_simp [ne_of_gt hb]
    rw [hc] at hm
    have hlog : Real.log (Real.log (3 + C)) <=
        b * Real.log (Real.log (X : Real)) := by nlinarith only [hm]
    have he := (log_log_add_three_le_iff_double_exp C
      (b * Real.log (Real.log (X : Real))) hC).mp hlog
    linarith only [hbound X, he]
  have hu : exists A : Real, exists K : Nat, forall X : Nat, K <= X ->
      3 + n X <= Real.exp (Real.exp (A * Real.log (Real.log (X : Real)))) :=
    Exists.intro (1 : Real) (hmodel 1 (by norm_num))
  apply le_antisymm
  next =>
    apply (limsup_log_log_div_gauge_le_iff n
      (fun X : Nat => Real.log (Real.log (X : Real)))
      hn (eventually_le_log_log_nat 1) hu 0).mpr
    exact hmodel
  next => exact nonneg_limsup_log_log_count n hn hu

end Real

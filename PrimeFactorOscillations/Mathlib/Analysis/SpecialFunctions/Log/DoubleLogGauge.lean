/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Mathlib.Analysis.SpecialFunctions.Log.DoubleLogRate

/-! # Exact limsup characterizations with a positive normalization gauge -/

set_option autoImplicit false
set_option Elab.async false

namespace Real

/-- Strict lower comparison follows from the exact upper comparison. -/
theorem lt_normalized_log_log_add_three_iff (x t a : Real)
    (hx : 0 <= x) (ht : 0 < t) :
    a < Real.log (Real.log (3 + x)) / t <->
      Real.exp (Real.exp (a * t)) < 3 + x := by
  constructor
  next =>
    intro h
    by_contra hn
    have hle := (normalized_log_log_add_three_le_iff x t a hx ht).mpr (le_of_not_gt hn)
    exact (not_lt_of_ge hle) h
  next =>
    intro h
    by_contra hn
    have hle := (normalized_log_log_add_three_le_iff x t a hx ht).mp (le_of_not_gt hn)
    exact (not_lt_of_ge hle) h

private theorem gauge_rate_bounds (n t : Nat -> Real)
    (hn : forall k, 0 <= n k)
    (ht : exists K : Nat, forall k : Nat, K <= k -> 1 <= t k)
    (hu : exists A : Real, exists K : Nat, forall k : Nat, K <= k ->
      3 + n k <= Real.exp (Real.exp (A * t k))) :
    Filter.IsCoboundedUnder (fun a b : Real => a <= b) Filter.atTop
      (fun k : Nat => Real.log (Real.log (3 + n k)) / t k) /\
    Filter.IsBoundedUnder (fun a b : Real => a <= b) Filter.atTop
      (fun k : Nat => Real.log (Real.log (3 + n k)) / t k) := by
  choose Kt hKt using ht
  choose A Ku hKu using hu
  constructor
  next =>
    apply Filter.isCoboundedUnder_le_of_eventually_le Filter.atTop
      (x := min 0 (Real.log (Real.log 3)))
    apply Filter.eventually_atTop.mpr
    exact Exists.intro Kt (fun k hk =>
      normalized_log_log_add_three_lower (n k) (t k) (hn k) (hKt k hk))
  next =>
    apply Filter.isBoundedUnder_of_eventually_le (a := A)
    apply Filter.eventually_atTop.mpr
    refine Exists.intro (max Kt Ku) ?_
    intro k hk
    have ht1 := hKt k ((le_max_left Kt Ku).trans hk)
    exact (normalized_log_log_add_three_le_iff (n k) (t k) A (hn k)
      (by linarith)).mpr (hKu k ((le_max_right Kt Ku).trans hk))

/-- An exact upper-growth characterization retaining the additive shift.
This works for both the rank gauge k and the prime-value gauge log(log X). -/
theorem limsup_log_log_div_gauge_le_iff (n t : Nat -> Real)
    (hn : forall k, 0 <= n k)
    (ht : exists K : Nat, forall k : Nat, K <= k -> 1 <= t k)
    (hu : exists A : Real, exists K : Nat, forall k : Nat, K <= k ->
      3 + n k <= Real.exp (Real.exp (A * t k)))
    (L : Real) :
    Filter.limsup (fun k : Nat => Real.log (Real.log (3 + n k)) / t k)
        Filter.atTop <= L <->
      forall b : Real, L < b -> exists K : Nat, forall k : Nat, K <= k ->
        3 + n k <= Real.exp (Real.exp (b * t k)) := by
  have bounds := gauge_rate_bounds n t hn ht hu
  choose Kt hKt using ht
  constructor
  next =>
    intro hlim b hb
    have hev := Filter.eventually_lt_of_limsup_lt (hlim.trans_lt hb) bounds.2
    choose K hK using Filter.eventually_atTop.mp hev
    refine Exists.intro (max Kt K) ?_
    intro k hk
    have ht1 := hKt k ((le_max_left Kt K).trans hk)
    exact (normalized_log_log_add_three_le_iff (n k) (t k) b (hn k)
      (by linarith)).mp (hK k ((le_max_right Kt K).trans hk)).le
  next =>
    intro hbound
    apply (Filter.limsup_le_iff bounds.1 bounds.2).mpr
    intro y hy
    let b : Real := (L + y) / 2
    have hLb : L < b := by dsimp only [b]; linarith
    have hby : b < y := by dsimp only [b]; linarith
    choose K hK using hbound b hLb
    apply Filter.eventually_atTop.mpr
    refine Exists.intro (max Kt K) ?_
    intro k hk
    have ht1 := hKt k ((le_max_left Kt K).trans hk)
    have hr := (normalized_log_log_add_three_le_iff (n k) (t k) b (hn k)
      (by linarith)).mpr (hK k ((le_max_right Kt K).trans hk))
    exact hr.trans_lt hby

/-- The lower limsup direction is characterized by arbitrarily late supply;
it does not assume an all-large-scale or dyadic supply. -/
theorem le_limsup_log_log_div_gauge_iff (n t : Nat -> Real)
    (hn : forall k, 0 <= n k)
    (ht : exists K : Nat, forall k : Nat, K <= k -> 1 <= t k)
    (hu : exists A : Real, exists K : Nat, forall k : Nat, K <= k ->
      3 + n k <= Real.exp (Real.exp (A * t k)))
    (L : Real) :
    L <= Filter.limsup (fun k : Nat => Real.log (Real.log (3 + n k)) / t k)
        Filter.atTop <->
      forall a : Real, a < L -> forall K : Nat, exists k : Nat, K <= k /\
        Real.exp (Real.exp (a * t k)) < 3 + n k := by
  have bounds := gauge_rate_bounds n t hn ht hu
  choose Kt hKt using ht
  constructor
  next =>
    intro hlim a ha K
    have hfreq := (Filter.le_limsup_iff bounds.1 bounds.2).mp hlim a ha
    choose k hk using (Filter.frequently_atTop.mp hfreq) (max K Kt)
    have ht1 := hKt k ((le_max_right K Kt).trans hk.1)
    refine Exists.intro k (And.intro ((le_max_left K Kt).trans hk.1) ?_)
    exact (lt_normalized_log_log_add_three_iff (n k) (t k) a (hn k)
      (by linarith)).mp hk.2
  next =>
    intro hsupply
    apply (Filter.le_limsup_iff bounds.1 bounds.2).mpr
    intro a ha
    apply Filter.frequently_atTop.mpr
    intro K
    choose k hk using hsupply a ha (max K Kt)
    have ht1 := hKt k ((le_max_right K Kt).trans hk.1)
    refine Exists.intro k (And.intro ((le_max_left K Kt).trans hk.1) ?_)
    exact (lt_normalized_log_log_add_three_iff (n k) (t k) a (hn k)
      (by linarith)).mpr hk.2

end Real

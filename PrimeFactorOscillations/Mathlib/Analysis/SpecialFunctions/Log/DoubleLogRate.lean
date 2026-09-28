/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Topology.Order.LiminfLimsup
import PrimeFactorOscillations.Mathlib.Analysis.SpecialFunctions.Exp.DoubleExpGrowth

/-! # Double-logarithmic rates and eventual growth bounds -/

set_option autoImplicit false
set_option Elab.async false

namespace Real

/-- Exponentiating twice exactly translates the shifted double logarithm. -/
theorem log_log_add_three_le_iff_double_exp (x t : Real) (hx : 0 <= x) :
    Real.log (Real.log (3 + x)) <= t <->
      3 + x <= Real.exp (Real.exp t) := by
  have hpos : 0 < 3 + x := by linarith
  have hlog : 0 < Real.log (3 + x) := Real.log_pos (by linarith)
  constructor
  next =>
    intro h
    have h1 := Real.exp_le_exp.mpr h
    rw [Real.exp_log hlog] at h1
    have h2 := Real.exp_le_exp.mpr h1
    rwa [Real.exp_log hpos] at h2
  next =>
    intro h
    have h1 := Real.log_le_log hpos h
    rw [Real.log_exp] at h1
    have h2 := Real.log_le_log hlog h1
    simpa only [Real.log_exp] using h2

/-- The normalization requires a strictly positive denominator. -/
theorem normalized_log_log_add_three_le_iff (x t a : Real)
    (hx : 0 <= x) (ht : 0 < t) :
    Real.log (Real.log (3 + x)) / t <= a <->
      3 + x <= Real.exp (Real.exp (a * t)) := by
  have hc : (Real.log (Real.log (3 + x)) / t) * t =
      Real.log (Real.log (3 + x)) := by field_simp [ne_of_gt ht]
  rw [<- log_log_add_three_le_iff_double_exp x (a * t) hx]
  constructor
  next =>
    intro h
    have hm := mul_le_mul_of_nonneg_right h ht.le
    rwa [hc] at hm
  next =>
    intro h
    by_contra hn
    have hgt : a < Real.log (Real.log (3 + x)) / t := lt_of_not_ge hn
    have hm := mul_lt_mul_of_pos_right hgt ht
    rw [hc] at hm
    exact (not_lt_of_ge h) hm

/-- A fixed lower bound suffices for conditional-complete-order limsup APIs;
no numerical approximation to log(log 3) is needed. -/
theorem normalized_log_log_add_three_lower (x t : Real)
    (hx : 0 <= x) (ht : 1 <= t) :
    min 0 (Real.log (Real.log 3)) <= Real.log (Real.log (3 + x)) / t := by
  let m : Real := min 0 (Real.log (Real.log 3))
  have hm0 : m <= 0 := min_le_left _ _
  have hmL : m <= Real.log (Real.log 3) := min_le_right _ _
  have hlog1 : Real.log 3 <= Real.log (3 + x) :=
    Real.log_le_log (by norm_num) (by linarith)
  have hlog2 : Real.log (Real.log 3) <= Real.log (Real.log (3 + x)) :=
    Real.log_le_log (Real.log_pos (by norm_num)) hlog1
  have hneg := mul_nonpos_of_nonpos_of_nonneg hm0 (sub_nonneg.mpr ht)
  have hmt : m * t <= Real.log (Real.log (3 + x)) := by
    nlinarith only [hneg, hmL, hlog2]
  have htpos : 0 < t := by linarith
  have hc : (Real.log (Real.log (3 + x)) / t) * t =
      Real.log (Real.log (3 + x)) := by field_simp [ne_of_gt htpos]
  change m <= Real.log (Real.log (3 + x)) / t
  by_contra hn
  have hgt : Real.log (Real.log (3 + x)) / t < m := lt_of_not_ge hn
  have hm := mul_lt_mul_of_pos_right hgt htpos
  rw [hc] at hm
  exact (not_lt_of_ge hmt) hm

/-- The normalized sequence is bounded from below on a tail. -/
theorem isCoboundedUnder_log_log_add_three_div_nat
    (n : Nat -> Real) (hn : forall k, 0 <= n k) :
    Filter.IsCoboundedUnder (fun a b : Real => a <= b) Filter.atTop
      (fun k : Nat => Real.log (Real.log (3 + n k)) / k) := by
  apply Filter.isCoboundedUnder_le_of_eventually_le Filter.atTop
    (x := min 0 (Real.log (Real.log 3)))
  apply Filter.eventually_atTop.mpr
  refine Exists.intro 1 ?_
  intro k hk
  exact normalized_log_log_add_three_lower (n k) k (hn k) (by exact_mod_cast hk)

/-- An eventual count bound gives every slightly larger normalized rate. -/
theorem eventually_log_log_rate_le_of_double_exp (n : Nat -> Real)
    (hn : forall k, 0 <= n k) (a b : Real) (ha : 0 <= a) (hab : a < b)
    (hbound : exists K : Nat, forall k : Nat, K <= k ->
      n k <= Real.exp (Real.exp (a * k))) :
    exists K : Nat, forall k : Nat, K <= k ->
      Real.log (Real.log (3 + n k)) / k <= b := by
  choose K0 hK0 using hbound
  choose K1 hK1 using eventually_mul_double_exp_add_one_le a b 4 ha hab (by norm_num)
  refine Exists.intro (max 1 (max K0 K1)) ?_
  intro k hk
  have hkpos : 0 < (k : Real) := by
    exact_mod_cast (show 0 < k by omega)
  apply (normalized_log_log_add_three_le_iff (n k) k b (hn k) hkpos).mpr
  have h0 := hK0 k ((le_max_left K0 K1).trans ((le_max_right 1 (max K0 K1)).trans hk))
  have h1 := hK1 k ((le_max_right K0 K1).trans ((le_max_right 1 (max K0 K1)).trans hk))
  have hE := Real.exp_pos (Real.exp (a * k))
  linarith only [h0, h1, hE]

/-- Upper rate characterization, with boundedness and the nonnegative target
made explicit rather than supplied through default side conditions. -/
theorem limsup_log_log_rate_le_iff_eventual_double_exp
    (n : Nat -> Real) (hn : forall k, 0 <= n k)
    (hbounded : exists A : Real, 0 <= A /\ exists K : Nat,
      forall k : Nat, K <= k -> n k <= Real.exp (Real.exp (A * k)))
    (L : Real) (hL : 0 <= L) :
    Filter.limsup (fun k : Nat => Real.log (Real.log (3 + n k)) / k) Filter.atTop <= L <->
      forall b : Real, L < b -> exists K : Nat, forall k : Nat, K <= k ->
        n k <= Real.exp (Real.exp (b * k)) := by
  have hco := isCoboundedUnder_log_log_add_three_div_nat n hn
  choose A hA using hbounded
  choose K0 hK0 using eventually_log_log_rate_le_of_double_exp n hn A (A + 1)
    hA.1 (by linarith) hA.2
  have hbd : Filter.IsBoundedUnder (fun a b : Real => a <= b) Filter.atTop
      (fun k : Nat => Real.log (Real.log (3 + n k)) / k) :=
    Filter.isBoundedUnder_of_eventually_le (Filter.eventually_atTop.mpr (Exists.intro K0 hK0))
  constructor
  next =>
    intro hlim b hb
    have hev := Filter.eventually_lt_of_limsup_lt (hlim.trans_lt hb) hbd
    choose K hK using Filter.eventually_atTop.mp hev
    refine Exists.intro (max 1 K) ?_
    intro k hk
    have hkpos : 0 < (k : Real) := by exact_mod_cast (show 0 < k by omega)
    have hr := hK k ((le_max_right 1 K).trans hk)
    have hN := (normalized_log_log_add_three_le_iff (n k) k b (hn k) hkpos).mp hr.le
    linarith only [hN]
  next =>
    intro hbound
    apply (Filter.limsup_le_iff hco hbd).mpr
    intro y hy
    let a : Real := (L + y) / 2
    let b : Real := (a + y) / 2
    have hLa : L < a := by dsimp only [a]; linarith
    have ha : 0 <= a := hL.trans hLa.le
    have hab : a < b := by dsimp only [a, b]; linarith
    have hby : b < y := by dsimp only [a, b]; linarith
    choose K hK using eventually_log_log_rate_le_of_double_exp n hn a b ha hab
      (hbound a hLa)
    apply Filter.eventually_atTop.mpr
    exact Exists.intro K (fun k hk => (hK k hk).trans_lt hby)

end Real

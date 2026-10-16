/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import Mathlib.Analysis.PSeries
import PrimeFactorOscillations.Mathlib.Probability.Distributions.FiniteBernoulliArrayComparison

/-! # Finite logarithmic product comparison

Exact finite supports, uniform low/middle/high range bounds and reciprocal-square
series convergence provide the analytic product inputs for regular local laws.
The finite Bernoulli array comparison library is reexported for its consumers.
-/

set_option autoImplicit false
set_option Elab.async false

open Filter

namespace Real

theorem abs_log_sub_log_le_div_lower (x y m : Real)
    (hm : 0 < m) (hx : m <= x) (hy : m <= y) :
    abs (log x - log y) <= abs (x - y) / m := by
  have hx0 : 0 < x := hm.trans_le hx
  have hy0 : 0 < y := hm.trans_le hy
  have hupper (a b : Real) (ha : 0 < a) (hb : 0 < b) (hbm : m <= b) :
      log a - log b <= abs (a - b) / m := by
    have h := log_le_sub_one_of_pos (div_pos ha hb)
    rw [log_div (ne_of_gt ha) (ne_of_gt hb)] at h
    have hid : a / b - 1 = (a - b) / b := by
      field_simp [ne_of_gt hb]
    rw [hid] at h
    calc
      _ <= (a - b) / b := h
      _ <= abs (a - b) / b :=
        div_le_div_of_nonneg_right (le_abs_self _) hb.le
      _ <= abs (a - b) / m :=
        div_le_div_of_nonneg_left (abs_nonneg _) hm hbm
  have hxy := hupper x y hx0 hy0 hy
  have hyx := hupper y x hy0 hx0 hx
  rw [abs_sub_comm y x] at hyx
  exact abs_le.mpr (And.intro (by linarith only [hyx]) hxy)

theorem log_bernoulliFactor_saturation_bound (a b z : Real)
    (ha : 0 < a) (hb : 0 < b) (hz : 1 < z) :
    abs ((log (1 + (z - 1) * a) - log (1 + (z - 1) * b)) -
      (log a - log b)) <= abs (1 / a - 1 / b) / (z - 1) := by
  have hu : 0 < z - 1 := sub_pos.mpr hz
  have hfa : 0 < 1 + (z - 1) * a := by positivity
  have hfb : 0 < 1 + (z - 1) * b := by positivity
  have haid : log (1 + (z - 1) * a) - log a =
      log (z - 1 + 1 / a) := by
    rw [<- log_div (ne_of_gt hfa) (ne_of_gt ha)]
    congr 1
    field_simp [ne_of_gt ha]
    ring
  have hbid : log (1 + (z - 1) * b) - log b =
      log (z - 1 + 1 / b) := by
    rw [<- log_div (ne_of_gt hfb) (ne_of_gt hb)]
    congr 1
    field_simp [ne_of_gt hb]
    ring
  have hh := abs_log_sub_log_le_div_lower
    (z - 1 + 1 / a) (z - 1 + 1 / b) (z - 1) hu
    (le_add_of_nonneg_right (div_nonneg (by norm_num) ha.le))
    (le_add_of_nonneg_right (div_nonneg (by norm_num) hb.le))
  have hl : (log (1 + (z - 1) * a) - log (1 + (z - 1) * b)) -
      (log a - log b) =
        (log (1 + (z - 1) * a) - log a) -
          (log (1 + (z - 1) * b) - log b) := by ring
  rw [hl, haid, hbid]
  simpa only [add_sub_add_left_eq_sub] using hh

theorem log_bernoulliFactor_difference_bound (a b u : Real)
    (ha : 0 <= a) (hb : 0 <= b) (hu : 0 <= u) :
    abs (log (1 + u * a) - log (1 + u * b)) <= u * abs (a - b) := by
  have hh := abs_log_sub_log_le_div_lower (1 + u * a) (1 + u * b) 1
    (by norm_num) (le_add_of_nonneg_right (mul_nonneg hu ha))
    (le_add_of_nonneg_right (mul_nonneg hu hb))
  have hid : 1 + u * a - (1 + u * b) = u * (a - b) := by ring
  simpa only [hid, abs_mul, abs_of_nonneg hu, div_one] using hh

theorem log_bernoulliFactor_difference_bound_lower (a b u m : Real)
    (hm : 0 < m) (ha : m <= a) (hb : m <= b) (hu : 0 <= u) :
    abs (log (1 + u * a) - log (1 + u * b)) <= abs (a - b) / m := by
  by_cases hu0 : u = 0
  next =>
    rw [hu0]
    simp only [zero_mul, add_zero, sub_self, abs_zero]
    exact div_nonneg (abs_nonneg _) hm.le
  next =>
    have hup : 0 < u := lt_of_le_of_ne hu (Ne.symm hu0)
    have hum : 0 < u * m := mul_pos hup hm
    have hfa : u * m <= 1 + u * a :=
      (mul_le_mul_of_nonneg_left ha hu).trans (by linarith)
    have hfb : u * m <= 1 + u * b :=
      (mul_le_mul_of_nonneg_left hb hu).trans (by linarith)
    have hh := abs_log_sub_log_le_div_lower (1 + u * a) (1 + u * b) (u * m)
      hum hfa hfb
    have hid : 1 + u * a - (1 + u * b) = u * (a - b) := by ring
    rw [hid, abs_mul, abs_of_pos hup] at hh
    have hc : u * abs (a - b) / (u * m) = abs (a - b) / m := by
      field_simp [ne_of_gt hup, ne_of_gt hm]
    rwa [hc] at hh

end Real

namespace Finset

theorem abs_sum_sub_filtered_sum_le_three_ranges
    (S : Finset Nat) (f g : Nat -> Real) (x q y : Nat)
    (hxq : x <= q) (hqy : q <= y) (L M H : Real) (hM : 0 <= M)
    (hclose : forall p, Membership.mem S p -> abs (f p - g p) <= L)
    (hfm : forall p, Membership.mem S p -> abs (f p) <= M / (p : Real))
    (hgm : forall p, Membership.mem S p -> abs (g p) <= M / (p : Real))
    (hfh : forall p, Membership.mem S p -> abs (f p) <= H / (p : Real) ^ 2) :
    abs (S.sum f - (S.filter (fun p => p <= q)).sum g) <=
      (S.filter (fun p => p <= x)).sum (fun _ => L) +
        (S.filter (fun p => x < p /\ p <= y)).sum (fun p => 2 * M / (p : Real)) +
          (S.filter (fun p => y < p)).sum (fun p => H / (p : Real) ^ 2) := by
  classical
  have hid : S.sum f - (S.filter (fun p => p <= q)).sum g =
      S.sum (fun p => f p - if p <= q then g p else 0) := by
    rw [Finset.sum_sub_distrib, Finset.sum_filter]
  rw [hid]
  calc
    _ <= S.sum (fun p => abs (f p - if p <= q then g p else 0)) :=
      Finset.abs_sum_le_sum_abs _ _
    _ <= S.sum (fun p =>
        (if p <= x then L else 0) +
          (if x < p /\ p <= y then 2 * M / (p : Real) else 0) +
            (if y < p then H / (p : Real) ^ 2 else 0)) := by
      apply Finset.sum_le_sum
      intro p hp
      by_cases hpx : p <= x
      next =>
        have hpq : p <= q := hpx.trans hxq
        have hpy : p <= y := hpq.trans hqy
        simpa only [ite_eq_left hpx, ite_eq_left hpq, not_lt_of_ge hpx,
          false_and, ite_false, not_lt_of_ge hpy, add_zero] using hclose p hp
      next =>
        have hxp : x < p := Nat.lt_of_not_ge hpx
        by_cases hpy : p <= y
        next =>
          have hmid := And.intro hxp hpy
          have hnot : Not (y < p) := not_lt_of_ge hpy
          simp only [ite_eq_right hpx, ite_eq_left hmid, ite_eq_right hnot, zero_add, add_zero]
          by_cases hpq : p <= q
          next =>
            rw [ite_eq_left hpq]
            calc
              _ <= abs (f p) + abs (g p) := abs_sub _ _
              _ <= M / (p : Real) + M / (p : Real) :=
                add_le_add (hfm p hp) (hgm p hp)
              _ = _ := by ring
          next =>
            rw [ite_eq_right hpq, sub_zero]
            have hm0 := div_nonneg hM (Nat.cast_nonneg p)
            have htwo : M / (p : Real) <= 2 * M / (p : Real) := by
              calc
                _ <= M / (p : Real) + M / (p : Real) := le_add_of_nonneg_right hm0
                _ = _ := by ring
            exact (hfm p hp).trans htwo
        next =>
          have hyp : y < p := Nat.lt_of_not_ge hpy
          have hpq : Not (p <= q) := by omega
          simp only [ite_eq_right hpx, hpy, and_false, ite_false, ite_eq_left hyp,
            ite_eq_right hpq, sub_zero, zero_add]
          exact hfh p hp
    _ = _ := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
      simp only [Finset.sum_filter]


theorem primeLogSaturation_three_range_bound
    (P n m q H : Nat) (hm : 1 <= m) (hH : 2 <= H)
    (hmq : m <= q) (hqy : q <= m * H ^ 2) (hqn : q <= n)
    (f g : Nat -> Real) (R M D z : Real)
    (hR : 0 <= R) (hM : 0 <= M) (hD : 0 <= D)
    (hzlo : (H : Real) * (m : Real) <= z)
    (hzhi : z <= (H : Real) * ((m : Real) + 1))
    (hclose : forall p, Nat.Prime p -> P < p -> abs (f p - g p) <= R / (z - 1))
    (hfm : forall p, Nat.Prime p -> P < p -> abs (f p) <= M / (p : Real))
    (hgm : forall p, Nat.Prime p -> P < p -> abs (g p) <= M / (p : Real))
    (hfh : forall p, Nat.Prime p -> P < p -> abs (f p) <= z * D / (p : Real) ^ 2) :
    abs ((((n + 1).primesBelow \ (P + 1).primesBelow).sum f) -
      (((q + 1).primesBelow \ (P + 1).primesBelow).sum g)) <=
        2 * R / (H : Real) + 4 * D / (H : Real) +
          2 * M * (((m * H ^ 2 + 1).primesBelow.sum (fun p => 1 / (p : Real))) -
            ((m + 1).primesBelow.sum (fun p => 1 / (p : Real)))) := by
  classical
  let S := (n + 1).primesBelow \ (P + 1).primesBelow
  let y := m * H ^ 2
  let low := S.filter (fun p => p <= m)
  let mid := S.filter (fun p => m < p /\ p <= y)
  let high := S.filter (fun p => y < p)
  let A := (y + 1).primesBelow
  let B := (m + 1).primesBelow
  have hmR : 1 <= (m : Real) := by exact_mod_cast hm
  have hHR : 2 <= (H : Real) := by exact_mod_cast hH
  have hmp : 0 < (m : Real) := by linarith only [hmR]
  have hHp : 0 < (H : Real) := by linarith only [hHR]
  have hHm : 2 <= (H : Real) * (m : Real) := by
    calc
      _ <= (H : Real) * 1 := by simpa using hHR
      _ <= _ := mul_le_mul_of_nonneg_left hmR hHp.le
  have hz2 : 2 <= z := hHm.trans hzlo
  have hzm : 0 < z - 1 := by linarith only [hz2]
  have hz0 : 0 <= z := by linarith only [hz2]
  have hS (p : Nat) (hp : Membership.mem S p) : Nat.Prime p /\ P < p := by
    have hh := Finset.mem_sdiff.mp hp
    have hl := Nat.mem_primesBelow.mp hh.1
    have hnot : Not (p < P + 1) := by
      intro h
      exact hh.2 (Nat.mem_primesBelow.mpr (And.intro h hl.2))
    exact And.intro hl.2 (by omega)
  have hfiltered : S.filter (fun p => p <= q) =
      (q + 1).primesBelow \ (P + 1).primesBelow := by
    apply Finset.ext
    intro p
    constructor
    next =>
      intro hp
      have hh := Finset.mem_filter.mp hp
      have hs := Finset.mem_sdiff.mp hh.1
      have hn := Nat.mem_primesBelow.mp hs.1
      exact Finset.mem_sdiff.mpr (And.intro
        (Nat.mem_primesBelow.mpr (And.intro (by omega) hn.2)) hs.2)
    next =>
      intro hp
      have hh := Finset.mem_sdiff.mp hp
      have hq := Nat.mem_primesBelow.mp hh.1
      apply Finset.mem_filter.mpr
      exact And.intro (Finset.mem_sdiff.mpr (And.intro
        (Nat.mem_primesBelow.mpr (And.intro (by omega) hq.2)) hh.2)) (by omega)
  have hbound := abs_sum_sub_filtered_sum_le_three_ranges S f g m q y hmq hqy
    (R / (z - 1)) M (z * D) hM
    (fun p hp => hclose p (hS p hp).1 (hS p hp).2)
    (fun p hp => hfm p (hS p hp).1 (hS p hp).2)
    (fun p hp => hgm p (hS p hp).1 (hS p hp).2)
    (fun p hp => hfh p (hS p hp).1 (hS p hp).2)
  rw [hfiltered] at hbound
  have hlowSub : forall p, Membership.mem low p -> Membership.mem (Finset.Icc 1 m) p := by
    intro p hp
    have hh := Finset.mem_filter.mp hp
    exact Finset.mem_Icc.mpr (And.intro (hS p hh.1).1.one_le hh.2)
  have hcard : (low.card : Real) <= (m : Real) := by
    have hh := Finset.card_le_card hlowSub
    have hn : low.card <= m := by simpa using hh
    exact_mod_cast hn
  have hlRatio : (m : Real) / (z - 1) <= 2 / (H : Real) := by
    have hnum : (H : Real) * (m : Real) <= 2 * (z - 1) := by
      linarith only [hzlo, hz2]
    calc
      _ = ((H : Real) * (m : Real)) / ((H : Real) * (z - 1)) := by
        field_simp [ne_of_gt hHp, ne_of_gt hzm]
      _ <= (2 * (z - 1)) / ((H : Real) * (z - 1)) :=
        div_le_div_of_nonneg_right hnum (mul_pos hHp hzm).le
      _ = _ := by field_simp [ne_of_gt hHp, ne_of_gt hzm]
  have hl : low.sum (fun _ => R / (z - 1)) <= 2 * R / (H : Real) := by
    calc
      _ = (low.card : Real) * (R / (z - 1)) := by simp
      _ <= (m : Real) * (R / (z - 1)) :=
        mul_le_mul_of_nonneg_right hcard (div_nonneg hR hzm.le)
      _ = R * ((m : Real) / (z - 1)) := by ring
      _ <= R * (2 / (H : Real)) := mul_le_mul_of_nonneg_left hlRatio hR
      _ = _ := by ring
  have hHsq : 1 <= H ^ 2 := by nlinarith only [hH]
  have hmy : m <= y := by dsimp [y]; nlinarith only [hHsq]
  have hy1 : 1 <= y := hm.trans hmy
  have hBA : forall p, Membership.mem B p -> Membership.mem A p := by
    intro p hp
    have hh := Nat.mem_primesBelow.mp hp
    exact Nat.mem_primesBelow.mpr (And.intro (by omega) hh.2)
  have hmidSub : forall p, Membership.mem mid p -> Membership.mem (A \ B) p := by
    intro p hp
    have hh := Finset.mem_filter.mp hp
    have hprime := (hS p hh.1).1
    apply Finset.mem_sdiff.mpr
    exact And.intro
      (Nat.mem_primesBelow.mpr (And.intro (by omega) hprime))
      (by intro h; have hs := (Nat.mem_primesBelow.mp h).1; omega)
  have hmidSum : mid.sum (fun p => 1 / (p : Real)) <=
      ((y + 1).primesBelow.sum (fun p => 1 / (p : Real))) -
        ((m + 1).primesBelow.sum (fun p => 1 / (p : Real))) := by
    have hh := Finset.sum_le_sum_of_subset_of_nonneg (f := fun p : Nat => 1 / (p : Real))
      hmidSub (fun p hp hn => div_nonneg (by norm_num) (Nat.cast_nonneg p))
    have hs : (A \ B).sum (fun p => 1 / (p : Real)) +
        ((m + 1).primesBelow.sum (fun p => 1 / (p : Real))) =
          ((y + 1).primesBelow.sum (fun p => 1 / (p : Real))) :=
      Finset.sum_sdiff hBA
    linarith only [hh, hs]
  have hmid : mid.sum (fun p => 2 * M / (p : Real)) <=
      2 * M * (((y + 1).primesBelow.sum (fun p => 1 / (p : Real))) -
        ((m + 1).primesBelow.sum (fun p => 1 / (p : Real)))) := by
    calc
      _ = (2 * M) * mid.sum (fun p => 1 / (p : Real)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro p hp
        ring
      _ <= _ := mul_le_mul_of_nonneg_left hmidSum (mul_nonneg (by norm_num) hM)
  have htail : high.sum (fun p => 1 / (p : Real) ^ 2) <= 2 / (y : Real) :=
    Finset.sum_reciprocal_nat_sq_tail_le high y hy1
      (fun p hp => (Finset.mem_filter.mp hp).2)
  have hycast : (y : Real) = (m : Real) * (H : Real) ^ 2 := by
    simp only [y, Nat.cast_mul, Nat.cast_pow]
  have hyp : 0 < (y : Real) := by exact_mod_cast (show 0 < y by omega)
  have hzh : z <= 2 * (H : Real) * (m : Real) := by
    calc
      _ <= (H : Real) * ((m : Real) + 1) := hzhi
      _ <= (H : Real) * (2 * (m : Real)) :=
        mul_le_mul_of_nonneg_left (by linarith only [hmR]) hHp.le
      _ = _ := by ring
  have hhRatio : z / (y : Real) <= 2 / (H : Real) := by
    calc
      _ <= (2 * (H : Real) * (m : Real)) / (y : Real) :=
        div_le_div_of_nonneg_right hzh hyp.le
      _ = _ := by
        rw [hycast]
        field_simp [ne_of_gt hHp, ne_of_gt hmp]
  have hh : high.sum (fun p => z * D / (p : Real) ^ 2) <= 4 * D / (H : Real) := by
    calc
      _ = (z * D) * high.sum (fun p => 1 / (p : Real) ^ 2) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro p hp
        ring
      _ <= (z * D) * (2 / (y : Real)) :=
        mul_le_mul_of_nonneg_left htail (mul_nonneg hz0 hD)
      _ = (2 * D) * (z / (y : Real)) := by ring
      _ <= (2 * D) * (2 / (H : Real)) :=
        mul_le_mul_of_nonneg_left hhRatio (mul_nonneg (by norm_num) hD)
      _ = _ := by ring
  have hs := hbound.trans (add_le_add (add_le_add hl hmid) hh)
  change abs (S.sum f - _) <= _
  dsimp only [low, mid, high, y] at hs
  linarith only [hs]

end Finset

namespace Finset

theorem tendsto_primeTail_sum_of_abs_le_sq (P : Nat) (r : Nat -> Real)
    (K : Real) (hK : 0 <= K)
    (hr : forall p, Nat.Prime p -> P < p -> abs (r p) <= K / (p : Real) ^ 2) :
    Tendsto (fun N : Nat => ((N + 1).primesBelow \ (P + 1).primesBelow).sum r)
      atTop (nhds (tsum (fun p : Nat => if Nat.Prime p /\ P < p then r p else 0))) := by
  classical
  let a : Nat -> Real := fun p => if Nat.Prime p /\ P < p then r p else 0
  have hb : Summable (fun p : Nat => K * (1 / (p : Real) ^ 2)) :=
    (Real.summable_one_div_nat_pow.mpr (by decide)).mul_left K
  have ha : Summable a := by
    apply hb.of_norm_bounded
    intro p
    rw [Real.norm_eq_abs]
    dsimp [a]
    by_cases hp : Nat.Prime p /\ P < p
    next =>
      rw [ite_eq_left hp]
      calc
        _ <= K / (p : Real) ^ 2 := hr p hp.1 hp.2
        _ = _ := by ring
    next =>
      rw [ite_eq_right hp, abs_zero]
      exact mul_nonneg hK (div_nonneg (by norm_num) (sq_nonneg _))
  have hmono : Monotone (fun N : Nat => Finset.range (N + 1)) := by
    intro m n hmn p hp
    exact Finset.mem_range.mpr
      ((Finset.mem_range.mp hp).trans_le (Nat.add_le_add_right hmn 1))
  have hsets : Tendsto (fun N : Nat => Finset.range (N + 1)) atTop atTop := by
    apply Filter.tendsto_atTop_finset_of_monotone hmono
    intro p
    exact Exists.intro p (Finset.mem_range.mpr (Nat.lt_succ_self p))
  have ht := ha.hasSum.comp hsets
  apply ht.congr'
  apply Filter.Eventually.of_forall
  intro N
  have hsupport : (N + 1).primesBelow \ (P + 1).primesBelow =
      (Finset.range (N + 1)).filter (fun p => Nat.Prime p /\ P < p) := by
    apply Finset.ext
    intro p
    constructor
    next =>
      intro hp
      have hh := Finset.mem_sdiff.mp hp
      have hn := Nat.mem_primesBelow.mp hh.1
      have hP : P < p := by
        by_contra hnot
        exact hh.2 (Nat.mem_primesBelow.mpr (And.intro (by omega) hn.2))
      exact Finset.mem_filter.mpr
        (And.intro (Finset.mem_range.mpr hn.1) (And.intro hn.2 hP))
    next =>
      intro hp
      have hh := Finset.mem_filter.mp hp
      apply Finset.mem_sdiff.mpr
      exact And.intro (Nat.mem_primesBelow.mpr
        (And.intro (Finset.mem_range.mp hh.1) hh.2.1))
        (by intro h; have hs := (Nat.mem_primesBelow.mp h).1; omega)
  change (Finset.range (N + 1)).sum
    (fun p => if Nat.Prime p /\ P < p then r p else 0) = _
  rw [<- Finset.sum_filter, <- hsupport]

end Finset

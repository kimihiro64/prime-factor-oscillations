/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Mathlib.Probability.Distributions.FiniteBernoulliProductComparison

/-!
# Factorial coefficient bounds and finite exceptional prefixes

Factorial coefficient bounds and finite exceptional prefixes for the peak-height comparison of regular prime Bernoulli laws.
-/

set_option autoImplicit false
set_option Elab.async false

open Filter Topology

namespace List

theorem largestWeightSum_le_card_mul_cap (s : List Real) (r : Nat) (cap : Real)
    (hcap0 : 0 <= cap) (hcap : forall a, List.Mem a s -> a <= cap) :
    largestWeightSum s r <= (r : Real) * cap := by
  have hmap : s.map (fun a => max (a - cap) 0) = s.map (fun _ : Real => 0) := by
    apply List.map_congr_left
    intro a ha
    exact max_eq_right (sub_nonpos.mpr (hcap a ha))
  have hz : (s.map (fun a => max (a - cap) 0)).sum = 0 := by
    rw [hmap]
    simp
  have hh := largestWeightSum_le_threshold_excess s r cap hcap0
  rwa [hz, add_zero] at hh

theorem esymm_factorial_lower_of_cap (s : List Real) (r : Nat) (cap : Real)
    (hs : forall a, List.Mem a s -> 0 <= a) (hcap0 : 0 <= cap)
    (hcap : forall a, List.Mem a s -> a <= cap)
    (hgap : 0 <= s.sum - (r : Real) * cap) :
    (s.sum - (r : Real) * cap) ^ r <=
      (r.factorial : Real) * (s : Multiset Real).esymm r := by
  let a := s.sum - (r : Real) * cap
  have hstep (j : Nat) (hj : j + 1 <= r) :
      a * (s : Multiset Real).esymm j <=
        ((j + 1 : Nat) : Real) * (s : Multiset Real).esymm (j + 1) := by
    have hlarge := largestWeightSum_le_card_mul_cap s j cap hcap0 hcap
    have hJ : (j : Real) * cap <= (r : Real) * cap :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast (show j <= r by omega)) hcap0
    have hc : a <= s.sum - largestWeightSum s j := by dsimp [a]; linarith only [hlarge, hJ]
    have he := Multiset.esymm_nonneg_ordered (s : Multiset Real)
      (fun b hb => hs b hb) j
    have hr := sum_sub_largest_mul_esymm_le s hs (j + 1) (by omega)
    simp only [Nat.add_sub_cancel] at hr
    exact (mul_le_mul_of_nonneg_right hc he).trans hr
  have hi : forall j : Nat, j <= r ->
      a ^ j <= (j.factorial : Real) * (s : Multiset Real).esymm j := by
    intro j
    induction j with
    | zero => intro hj; simp
    | succ j ih =>
        intro hj
        have hp := ih (by omega)
        have ht := hstep j hj
        calc
          _ = a * a ^ j := by rw [pow_succ]; ring
          _ <= a * ((j.factorial : Real) * (s : Multiset Real).esymm j) :=
            mul_le_mul_of_nonneg_left hp hgap
          _ = (j.factorial : Real) * (a * (s : Multiset Real).esymm j) := by ring
          _ <= (j.factorial : Real) *
              (((j + 1 : Nat) : Real) * (s : Multiset Real).esymm (j + 1)) :=
            mul_le_mul_of_nonneg_left ht (Nat.cast_nonneg _)
          _ = _ := by rw [Nat.factorial_succ, Nat.cast_mul]; ring
  exact hi r (le_refl r)

theorem esymm_factorial_upper (s : List Real)
    (hs : forall a, List.Mem a s -> 0 <= a) (r : Nat) :
    (r.factorial : Real) * (s : Multiset Real).esymm r <= s.sum ^ r := by
  have hsum : 0 <= s.sum := List.sum_nonneg hs
  induction r with
  | zero => simp
  | succ r ih =>
      have hh := Multiset.degree_mul_esymm_le_sum_mul_ordered (s : Multiset Real)
        (fun a ha => hs a ha) (r + 1)
      simp only [Nat.add_sub_cancel] at hh
      calc
        _ = (r.factorial : Real) *
            (((r + 1 : Nat) : Real) * (s : Multiset Real).esymm (r + 1)) := by
          rw [Nat.factorial_succ, Nat.cast_mul]
          ring
        _ <= (r.factorial : Real) * (s.sum * (s : Multiset Real).esymm r) :=
          mul_le_mul_of_nonneg_left hh (Nat.cast_nonneg _)
        _ = s.sum * ((r.factorial : Real) * (s : Multiset Real).esymm r) := by ring
        _ <= s.sum * s.sum ^ r := mul_le_mul_of_nonneg_left ih hsum
        _ = _ := by rw [pow_succ]; ring

end List

namespace List

theorem esymm_factorial_lower_of_largest_bound (s : List Real) (r : Nat) (B : Real)
    (hs : forall a, List.Mem a s -> 0 <= a)
    (hB : forall j : Nat, j < r -> largestWeightSum s j <= B)
    (hgap : 0 <= s.sum - B) :
    (s.sum - B) ^ r <= (r.factorial : Real) * (s : Multiset Real).esymm r := by
  let a := s.sum - B
  have hstep (j : Nat) (hj : j + 1 <= r) :
      a * (s : Multiset Real).esymm j <=
        ((j + 1 : Nat) : Real) * (s : Multiset Real).esymm (j + 1) := by
    have hc : a <= s.sum - largestWeightSum s j := by
      dsimp [a]
      linarith only [hB j (by omega)]
    have he := Multiset.esymm_nonneg_ordered (s : Multiset Real) (fun b hb => hs b hb) j
    have hr := sum_sub_largest_mul_esymm_le s hs (j + 1) (by omega)
    simp only [Nat.add_sub_cancel] at hr
    exact (mul_le_mul_of_nonneg_right hc he).trans hr
  have hi : forall j : Nat, j <= r ->
      a ^ j <= (j.factorial : Real) * (s : Multiset Real).esymm j := by
    intro j
    induction j with
    | zero => intro hj; simp
    | succ j ih =>
        intro hj
        have hp := ih (by omega)
        have ht := hstep j hj
        calc
          _ = a * a ^ j := by rw [pow_succ]; ring
          _ <= a * ((j.factorial : Real) * (s : Multiset Real).esymm j) :=
            mul_le_mul_of_nonneg_left hp hgap
          _ = (j.factorial : Real) * (a * (s : Multiset Real).esymm j) := by ring
          _ <= (j.factorial : Real) *
              (((j + 1 : Nat) : Real) * (s : Multiset Real).esymm (j + 1)) :=
            mul_le_mul_of_nonneg_left ht (Nat.cast_nonneg _)
          _ = _ := by rw [Nat.factorial_succ, Nat.cast_mul]; ring
  exact hi r (le_refl r)

theorem bernoulliMass_le_one (s : List Real)
    (hs : forall a, List.Mem a s -> 0 <= a /\ a <= 1) (r : Nat) :
    bernoulliMass s r <= 1 := by
  induction s generalizing r with
  | nil => cases r <;> simp [bernoulliMass]
  | cons a s ih =>
      have ha := hs a (List.Mem.head _)
      have ht : forall b, List.Mem b s -> 0 <= b /\ b <= 1 :=
        fun b hb => hs b (List.Mem.tail _ hb)
      have hma : 0 <= 1 - a := sub_nonneg.mpr ha.2
      cases r with
      | zero =>
          simp only [bernoulliMass]
          calc
            _ <= (1 - a) * 1 := mul_le_mul_of_nonneg_left (ih ht 0) hma
            _ <= 1 := by linarith only [ha.1]
      | succ r =>
          simp only [bernoulliMass]
          calc
            _ <= (1 - a) * 1 + a * 1 :=
              add_le_add (mul_le_mul_of_nonneg_left (ih ht (r + 1)) hma)
                (mul_le_mul_of_nonneg_left (ih ht r) ha.1)
            _ = _ := by ring

end List

namespace Real

theorem one_sub_ge_exp_neg_odds (a : Real) (ha : a < 1) :
    exp (-(a / (1 - a))) <= 1 - a := by
  have hd : 0 < 1 - a := sub_pos.mpr ha
  have hh := log_le_sub_one_of_pos (div_pos (by norm_num : (0 : Real) < 1) hd)
  rw [log_div (by norm_num) (ne_of_gt hd), log_one, zero_sub] at hh
  have hid : 1 / (1 - a) - 1 = a / (1 - a) := by field_simp [ne_of_gt hd]; ring
  rw [hid] at hh
  have hlo : -(a / (1 - a)) <= log (1 - a) := by linarith only [hh]
  have he := exp_le_exp.mpr hlo
  rwa [exp_log hd] at he

end Real

namespace List

theorem survival_prod_ge_exp_neg_odds (s : List Real)
    (hs : forall a, List.Mem a s -> a < 1) :
    Real.exp (-((s.map (fun a => a / (1 - a))).sum)) <=
      (s.map (fun a => 1 - a)).prod := by
  induction s with
  | nil => simp
  | cons a s ih =>
      have ha := hs a (List.Mem.head _)
      have ht : forall b, List.Mem b s -> b < 1 :=
        fun b hb => hs b (List.Mem.tail _ hb)
      simp only [List.map_cons, List.sum_cons, List.prod_cons]
      rw [neg_add, Real.exp_add]
      exact mul_le_mul (Real.one_sub_ge_exp_neg_odds a ha) (ih ht)
        (Real.exp_pos _).le (sub_pos.mpr ha).le

theorem bernoulliMass_lower_largest (s : List Real) (r : Nat) (B : Real)
    (hs : forall a, List.Mem a s -> 0 <= a /\ a < 1)
    (hB : forall j : Nat, j < r ->
      largestWeightSum (s.map (fun a => a / (1 - a))) j <= B)
    (hgap : 0 <= (s.map (fun a => a / (1 - a))).sum - B) :
    Real.exp (-((s.map (fun a => a / (1 - a))).sum)) *
      (((s.map (fun a => a / (1 - a))).sum - B) ^ r / (r.factorial : Real)) <=
        bernoulliMass s r := by
  let w := s.map (fun a => a / (1 - a))
  have hw : forall b, List.Mem b w -> 0 <= b := by
    intro b hb
    have hh := List.mem_map.mp hb
    choose a ha using hh
    rw [<- ha.2]
    exact div_nonneg (hs a ha.1).1 (sub_pos.mpr (hs a ha.1).2).le
  have hp := esymm_factorial_lower_of_largest_bound w r B hw hB hgap
  have hf : 0 < (r.factorial : Real) := by exact_mod_cast Nat.factorial_pos r
  have he : (w.sum - B) ^ r / (r.factorial : Real) <= (w : Multiset Real).esymm r := by
    have hh := div_le_div_of_nonneg_right hp hf.le
    have hid : ((r.factorial : Real) * (w : Multiset Real).esymm r) /
        (r.factorial : Real) = (w : Multiset Real).esymm r := by field_simp [ne_of_gt hf]
    rwa [hid] at hh
  have hsurv := survival_prod_ge_exp_neg_odds s (fun a ha => (hs a ha).2)
  have hV : 0 <= (s.map (fun a => 1 - a)).prod := (Real.exp_pos _).le.trans hsurv
  rw [bernoulliMass_eq_survival_mul_esymm s (fun a ha => ne_of_lt (hs a ha).2) r]
  exact mul_le_mul hsurv he
    (div_nonneg (pow_nonneg hgap r) hf.le) hV

theorem bernoulliMass_upper_power (s : List Real) (r : Nat)
    (hs : forall a, List.Mem a s -> 0 <= a /\ a < 1) :
    bernoulliMass s r <=
      ((s.map (fun a => a / (1 - a))).sum) ^ r / (r.factorial : Real) := by
  let w := s.map (fun a => a / (1 - a))
  have hw : forall b, List.Mem b w -> 0 <= b := by
    intro b hb
    have hh := List.mem_map.mp hb
    choose a ha using hh
    rw [<- ha.2]
    exact div_nonneg (hs a ha.1).1 (sub_pos.mpr (hs a ha.1).2).le
  have hp := esymm_factorial_upper w hw r
  have hf : 0 < (r.factorial : Real) := by exact_mod_cast Nat.factorial_pos r
  have he : (w : Multiset Real).esymm r <= w.sum ^ r / (r.factorial : Real) := by
    have hh := div_le_div_of_nonneg_right hp hf.le
    have hid : ((r.factorial : Real) * (w : Multiset Real).esymm r) /
        (r.factorial : Real) = (w : Multiset Real).esymm r := by field_simp [ne_of_gt hf]
    rwa [hid] at hh
  have hne : forall a, List.Mem a s -> Not (a = 1) := fun a ha => ne_of_lt (hs a ha).2
  have hV : (s.map (fun a => 1 - a)).prod <= 1 := by
    have hh := bernoulliMass_le_one s (fun a ha => And.intro (hs a ha).1 (hs a ha).2.le) 0
    rw [bernoulliMass_eq_survival_mul_esymm s hne 0] at hh
    simpa only [Multiset.esymm_zero, mul_one] using hh
  rw [bernoulliMass_eq_survival_mul_esymm s hne r]
  have he0 := Multiset.esymm_nonneg_ordered (w : Multiset Real) (fun a ha => hw a ha) r
  exact (mul_le_mul_of_nonneg_right hV he0).trans (by simpa only [one_mul] using he)

end List

namespace List

theorem bernoulliMass_append_leading_lower (front tail : List Real)
    (hf : forall a, List.Mem a front -> 0 <= a /\ a <= 1)
    (ht : forall a, List.Mem a tail -> 0 <= a /\ a <= 1) (r : Nat) :
    front.prod * bernoulliMass tail r <=
      bernoulliMass (front ++ tail) (front.length + r) := by
  induction front with
  | nil => simp
  | cons a front ih =>
      have ha := hf a (List.Mem.head _)
      have hrest : forall b, List.Mem b front -> 0 <= b /\ b <= 1 :=
        fun b hb => hf b (List.Mem.tail _ hb)
      have hall : forall b, List.Mem b (front ++ tail) -> 0 <= b /\ b <= 1 := by
        intro b hb
        cases List.mem_append.mp hb with
        | inl hb => exact hrest b hb
        | inr hb => exact ht b hb
      have hnonneg := bernoulliMass_nonneg (front ++ tail) hall (front.length + r + 1)
      have hi := mul_le_mul_of_nonneg_left (ih hrest) ha.1
      have hidx : (front.length + 1) + r = (front.length + r) + 1 := by omega
      simp only [List.prod_cons, List.cons_append, List.length_cons]
      rw [hidx]
      change (a * front.prod) * bernoulliMass tail r <=
        (1 - a) * bernoulliMass (front ++ tail) (front.length + r + 1) +
          a * bernoulliMass (front ++ tail) (front.length + r)
      calc
        _ = a * (front.prod * bernoulliMass tail r) := by ring
        _ <= a * bernoulliMass (front ++ tail) (front.length + r) := hi
        _ <= _ := le_add_of_nonneg_left (mul_nonneg (sub_nonneg.mpr ha.2) hnonneg)

end List
namespace List

theorem bernoulliMass_append_window_upper (front tail : List Real) (k : Nat) (U : Real)
    (hf : forall a, List.Mem a front -> 0 <= a /\ a <= 1) (hU : 0 <= U)
    (ht : forall j : Nat, j <= k -> k <= j + front.length ->
      bernoulliMass tail j <= U) :
    bernoulliMass (front ++ tail) k <= U := by
  induction front generalizing k with
  | nil => simpa only [List.nil_append] using ht k (le_refl k) (by simp)
  | cons a front ih =>
      have ha := hf a (List.Mem.head _)
      have hrest : forall b, List.Mem b front -> 0 <= b /\ b <= 1 :=
        fun b hb => hf b (List.Mem.tail _ hb)
      cases k with
      | zero =>
          have hh : bernoulliMass (front ++ tail) 0 <= U := by
            apply ih 0 hrest
            intro j hj hlen
            exact ht j hj (by simp)
          change (1 - a) * bernoulliMass (front ++ tail) 0 <= U
          calc
            _ <= (1 - a) * U :=
              mul_le_mul_of_nonneg_left hh (sub_nonneg.mpr ha.2)
            _ <= U := by nlinarith only [ha.1, hU]
      | succ k =>
          have hfirst : bernoulliMass (front ++ tail) (k + 1) <= U := by
            apply ih (k + 1) hrest
            intro j hj hlen
            apply ht j hj
            simp only [List.length_cons]
            omega
          have hsecond : bernoulliMass (front ++ tail) k <= U := by
            apply ih k hrest
            intro j hj hlen
            apply ht j (by omega)
            simp only [List.length_cons]
            omega
          change (1 - a) * bernoulliMass (front ++ tail) (k + 1) +
            a * bernoulliMass (front ++ tail) k <= U
          calc
            _ <= (1 - a) * U + a * U :=
              add_le_add (mul_le_mul_of_nonneg_left hfirst (sub_nonneg.mpr ha.2))
                (mul_le_mul_of_nonneg_left hsecond ha.1)
            _ = U := by ring

theorem bernoulliMass_append_power_upper (front tail : List Real) (k : Nat) (S : Real)
    (hf : forall a, List.Mem a front -> 0 <= a /\ a <= 1)
    (ht : forall a, List.Mem a tail -> 0 <= a /\ a < 1)
    (hS : 1 <= S) (hsum : (tail.map (fun a => a / (1 - a))).sum <= S) :
    bernoulliMass (front ++ tail) k <=
      S ^ k / (((k - front.length).factorial : Nat) : Real) := by
  let W := (tail.map (fun a => a / (1 - a))).sum
  have hW : 0 <= W := by
    apply List.sum_nonneg
    intro q hq
    have hh := List.mem_map.mp hq
    choose a ha using hh
    rw [<- ha.2]
    exact div_nonneg (ht a ha.1).1 (sub_pos.mpr (ht a ha.1).2).le
  have hSp : 0 <= S := zero_le_one.trans hS
  have hpower : forall j : Nat, W ^ j <= S ^ j := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
        rw [pow_succ, pow_succ]
        exact mul_le_mul ih hsum hW (pow_nonneg hSp j)
  have hmon (j d : Nat) : S ^ j <= S ^ (j + d) := by
    induction d with
    | zero => simp
    | succ d ih =>
        calc
          _ <= S ^ (j + d) := ih
          _ <= S ^ (j + d) * S := by
            have hh := mul_le_mul_of_nonneg_left hS (pow_nonneg hSp (j + d))
            simpa only [mul_one] using hh
          _ = _ := by rw [show j + (d + 1) = (j + d) + 1 by omega, pow_succ]
  apply bernoulliMass_append_window_upper front tail k
    (S ^ k / (((k - front.length).factorial : Nat) : Real)) hf
    (div_nonneg (pow_nonneg hSp k) (Nat.cast_nonneg _))
  intro j hj hlen
  have hlow : k - front.length <= j := by omega
  have hfac : (((k - front.length).factorial : Nat) : Real) <= (j.factorial : Real) := by
    exact_mod_cast (Nat.factorial_le hlow)
  have hf0 : (0 : Real) < (((k - front.length).factorial : Nat) : Real) := by
    exact_mod_cast Nat.factorial_pos (k - front.length)
  have hj0 : (0 : Real) < (j.factorial : Real) := by
    exact_mod_cast Nat.factorial_pos j
  have hpk : S ^ j <= S ^ k := by
    have hh := hmon j (k - j)
    simpa only [Nat.add_sub_of_le hj] using hh
  calc
    _ <= W ^ j / (j.factorial : Real) := bernoulliMass_upper_power tail j ht
    _ <= S ^ k / (j.factorial : Real) :=
      div_le_div_of_nonneg_right ((hpower j).trans hpk) hj0.le
    _ <= _ := div_le_div_of_nonneg_left (pow_nonneg hSp k) hf0 hfac

end List
namespace List

theorem bernoulliMass_filter_front_nonzero (front tail : List Real) (k : Nat) :
    bernoulliMass
      (front.filter (fun a => decide (Not (a = 0))) ++ tail) k =
        bernoulliMass (front ++ tail) k := by
  classical
  induction front generalizing k with
  | nil => simp
  | cons a front ih =>
      by_cases ha : a = 0
      case pos =>
        subst a
        have hfilter : (0 :: front).filter (fun a => decide (Not (a = 0))) =
            front.filter (fun a => decide (Not (a = 0))) := by simp
        rw [hfilter, List.cons_append, bernoulliMass_zero_cons]
        exact ih k
      case neg =>
        have hfilter : (a :: front).filter (fun b => decide (Not (b = 0))) =
            a :: front.filter (fun b => decide (Not (b = 0))) := by simp [ha]
        rw [hfilter]
        cases k <;> simp only [List.cons_append, bernoulliMass, ih]

theorem bernoulliMass_eq_zero_of_length_lt (s : List Real)
    (k : Nat) (hk : s.length < k) : bernoulliMass s k = 0 := by
  induction s generalizing k with
  | nil => cases k <;> simp_all [bernoulliMass]
  | cons a s ih =>
      cases k with
      | zero => simp at hk
      | succ k =>
          have hlen : s.length < k := by simpa using hk
          rw [bernoulliMass, ih (k + 1) (by omega), ih k hlen]
          ring

end List


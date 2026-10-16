/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import PrimeFactorOscillations.Mathlib.Probability.Distributions.FiniteBernoulliRegularLaws
import PrimeFactorOscillations.Mathlib.RingTheory.MvPolynomial.Symmetric.LargestWeightBounds

/-! # Finite prefix errors for regular Bernoulli odds

Reciprocal-square pointwise errors have a total bound on every retained finite
support above a positive cutoff. The scalar regular-law comparison library is
reexported for applications to the actual Bernoulli odds.
-/

set_option autoImplicit false
set_option Elab.async false

universe u

namespace Finset

/-- The proved shifted reciprocal kernel controls every retained finite
support strictly above a positive natural cutoff. -/
theorem sum_reciprocal_nat_sq_tail_le (S : Finset Nat) (P : Nat) (hP : 1 <= P)
    (hS : forall p, Membership.mem S p -> P < p) :
    S.sum (fun p => 1 / (p : Real) ^ 2) <= 2 / (P : Real) := by
  let M := S.sup (fun p => p) + 1
  let e := fun p : Nat => p - (P + 1)
  have hPpos : 0 < (P : Real) := by
    exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hP)
  have hi : Set.InjOn e (fun p => Membership.mem S p) := by
    intro p hp q hq heq
    have hp' := hS p hp
    have hq' := hS q hq
    dsimp [e] at heq
    omega
  have ht : forall j, Membership.mem (S.image e) j -> Membership.mem (range M) j := by
    intro j hj
    have hpre := mem_image.mp hj
    choose p hp using hpre
    have hm := le_sup (f := fun q : Nat => q) hp.1
    rw [<- hp.2, mem_range]
    dsimp [e, M]
    omega
  have hs : S.sum (fun p => 1 / (p : Real) ^ 2) <=
      (range M).sum (fun j => 1 / ((j : Real) + 1 + (P : Real)) ^ 2) := by
    apply sum_le_sum_of_injOn e hi ht
    next =>
      intro p hp
      have hh := hS p hp
      have hid : (p : Real) = (e p : Real) + 1 + (P : Real) := by
        exact_mod_cast (show p = e p + 1 + P by dsimp [e]; omega)
      rw [hid]
    next =>
      intro j hj hnot
      exact div_nonneg (by norm_num) (sq_nonneg _)
  have hk : (range M).sum (fun j => 1 / ((j : Real) + 1 + (P : Real)) ^ 2) <=
      1 / (P : Real) - 1 / ((M : Real) + (P : Real)) :=
    sum_shifted_reciprocal_sq_le M (P : Real) 1 hPpos (by norm_num)
  have ht0 : 0 <= 1 / ((M : Real) + (P : Real)) :=
    div_nonneg (by norm_num) (add_nonneg (Nat.cast_nonneg M) hPpos.le)
  have hu : 0 <= 1 / (P : Real) := div_nonneg (by norm_num) hPpos.le
  calc
    _ <= (range M).sum (fun j => 1 / ((j : Real) + 1 + (P : Real)) ^ 2) := hs
    _ <= 1 / (P : Real) := by linarith only [hk, ht0]
    _ <= 1 / (P : Real) + 1 / (P : Real) := le_add_of_nonneg_right hu
    _ = _ := by ring

/-- A reciprocal-square pointwise error gives a uniform total-odds error
on the same explicitly retained finite support. -/
theorem abs_sum_sub_reciprocal_reference_le (S : Finset Nat) (P : Nat)
    (hP : 1 <= P) (hS : forall p, Membership.mem S p -> P < p)
    (a : Nat -> Real) (nu K : Real) (hK : 0 <= K)
    (herror : forall p, Membership.mem S p ->
      abs (a p - nu / (p : Real)) <= K / (p : Real) ^ 2) :
    abs (S.sum a - nu * S.sum (fun p => 1 / (p : Real))) <=
      2 * K / (P : Real) := by
  have hs := sum_reciprocal_nat_sq_tail_le S P hP hS
  have hcap : S.sum (fun p => K / (p : Real) ^ 2) <= 2 * K / (P : Real) := by
    calc
      _ = K * S.sum (fun p => 1 / (p : Real) ^ 2) := by
        rw [mul_sum]
        simp only [mul_one_div]
      _ <= K * (2 / (P : Real)) := mul_le_mul_of_nonneg_left hs hK
      _ = _ := by ring
  have hid : S.sum a - nu * S.sum (fun p => 1 / (p : Real)) =
      S.sum (fun p => a p - nu / (p : Real)) := by
    rw [sum_sub_distrib, mul_sum]
    simp only [mul_one_div]
  have hlo : -S.sum (fun p => K / (p : Real) ^ 2) <=
      S.sum (fun p => a p - nu / (p : Real)) := by
    rw [<- sum_neg_distrib]
    exact sum_le_sum (fun p hp => (abs_le.mp (herror p hp)).1)
  have hhi : S.sum (fun p => a p - nu / (p : Real)) <=
      S.sum (fun p => K / (p : Real) ^ 2) :=
    sum_le_sum (fun p hp => (abs_le.mp (herror p hp)).2)
  rw [hid]
  apply abs_le.mpr
  constructor <;> linarith only [hlo, hhi, hcap]

/-- Threshold excess is supported on the retained low subset. -/
theorem sum_positive_excess_le_filtered_sum {alpha : Type u} [DecidableEq alpha]
    (S : Finset alpha) (w : alpha -> Real) (low : alpha -> Prop) [DecidablePred low]
    (t : Real) (ht : 0 <= t)
    (hpos : forall p, Membership.mem S p -> 0 <= w p)
    (hhigh : forall p, Membership.mem S p -> Not (low p) -> w p <= t) :
    S.sum (fun p => max (w p - t) 0) <= (S.filter low).sum w := by
  let f := fun p => max (w p - t) 0
  have hrestrict : S.sum f = (S.filter low).sum f := by
    symm
    apply sum_subset (filter_subset _ _)
    intro p hp hnot
    have hl : Not (low p) := by
      intro hh
      exact hnot (mem_filter.mpr (And.intro hp hh))
    exact max_eq_right (sub_nonpos.mpr (hhigh p hp hl))
  change S.sum f <= (S.filter low).sum w
  rw [hrestrict]
  apply sum_le_sum
  intro p hp
  exact max_le (sub_le_self _ ht) (hpos p (mem_filter.mp hp).1)


end Finset

namespace List

/-- The largest selected weights are controlled by the low-prefix mass and
one explicit threshold cost per selected coordinate. -/
theorem largestWeightSum_le_filtered_prefix {alpha : Type u} [DecidableEq alpha]
    (S : Finset alpha) (w : alpha -> Real) (low : alpha -> Prop) [DecidablePred low]
    (t : Real) (ht : 0 <= t)
    (hpos : forall p, Membership.mem S p -> 0 <= w p)
    (hhigh : forall p, Membership.mem S p -> Not (low p) -> w p <= t)
    (r : Nat) :
    largestWeightSum (S.toList.map w) r <=
      (r : Real) * t + (S.filter low).sum w := by
  have hc := largestWeightSum_le_threshold_excess (S.toList.map w) r t ht
  have hs : ((S.toList.map w).map (fun a => max (a - t) 0)).sum =
      S.sum (fun p => max (w p - t) 0) := by simp
  rw [hs] at hc
  have he := Finset.sum_positive_excess_le_filtered_sum S w low t ht hpos hhigh
  linarith only [hc, he]


/-- A finite exceptional prefix contributes at most its complete odds sum
to the largest-weight allowance. The retained low subset is explicit. -/
theorem largestWeightSum_append_filtered_prefix (front : List Real)
    (S : Finset Nat) (w : Nat -> Real) (low : Nat -> Prop) [DecidablePred low]
    (t : Real) (ht : 0 <= t)
    (hfront : forall b, List.Mem b front -> 0 <= b)
    (hpos : forall p, Membership.mem S p -> 0 <= w p)
    (hhigh : forall p, Membership.mem S p -> Not (low p) -> w p <= t)
    (r : Nat) :
    largestWeightSum (front ++ S.toList.map w) r <=
      (r : Real) * t + front.sum + (S.filter low).sum w := by
  have hc := largestWeightSum_le_threshold_excess (front ++ S.toList.map w) r t ht
  have hf : (front.map (fun a => max (a - t) 0)).sum <= front.sum := by
    simpa using
      (List.sum_le_sum (l := front) (f := fun a => max (a - t) 0) (g := fun a => a)
        (fun a ha => max_le (sub_le_self _ ht) (hfront a ha)))
  have hs : ((S.toList.map w).map (fun a => max (a - t) 0)).sum =
      S.sum (fun p => max (w p - t) 0) := by simp
  simp only [List.map_append, List.sum_append] at hc
  rw [hs] at hc
  have he := Finset.sum_positive_excess_le_filtered_sum S w low t ht hpos hhigh
  linarith only [hc, hf, he]


end List

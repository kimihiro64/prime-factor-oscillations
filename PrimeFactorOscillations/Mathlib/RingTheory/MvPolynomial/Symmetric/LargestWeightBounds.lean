/-
Copyright (c) 2026 Jonas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas
-/
import Mathlib.Data.List.Sort
import PrimeFactorOscillations.Mathlib.RingTheory.MvPolynomial.Symmetric.OrderedBounds

/-! # Symmetric ratio bounds using the largest weights without an input order assumption -/

set_option autoImplicit false
set_option Elab.async false

namespace List

variable {R : Type*} [LinearOrder R]

/-- Sort by the explicitly descending Boolean comparison. No order-dual
type inference is involved. -/
def descendingWeightList (s : List R) : List R :=
  s.mergeSort (fun a b => decide (b <= a))

/-- The intended descending order is proved for the actual selected comparison. -/
theorem descendingWeightList_pairwise (s : List R) :
    (descendingWeightList s).Pairwise (fun a b => b <= a) := by
  have ht : forall a b c : R, decide (b <= a) = true -> decide (c <= b) = true ->
      decide (c <= a) = true := by
    intro a b c hab hbc
    simp only [decide_eq_true_eq] at hab hbc
    simpa only [decide_eq_true_eq] using hbc.trans hab
  have htotal : forall a b : R, (decide (b <= a) || decide (a <= b)) = true := by
    intro a b
    rcases le_total b a with h | h
    next => simp [h]
    next => simp [h]
  simpa only [descendingWeightList, decide_eq_true_eq] using
    List.pairwise_mergeSort (le := fun a b : R => decide (b <= a)) ht htotal s

/-- Sorting preserves the exact finite multiset. -/
theorem descendingWeightList_perm (s : List R) : (descendingWeightList s).Perm s :=
  List.mergeSort_perm s (fun a b => decide (b <= a))

variable [Field R]

/-- The deleted-weight allowance is the sum of the largest requested number
of entries, including all available entries when the request exceeds length. -/
def largestWeightSum (s : List R) (r : Nat) : R :=
  ((descendingWeightList s).take r).sum

variable [IsStrictOrderedRing R]

/-- The exact polynomial upper bound requires no order assumption on the input. -/
theorem sum_sub_largest_mul_esymm_le (s : List R)
    (hs : forall a, List.Mem a s -> 0 <= a) (r : Nat) (hr : 1 <= r) :
    (s.sum - largestWeightSum s (r - 1)) * (s : Multiset R).esymm (r - 1) <=
      (r : R) * (s : Multiset R).esymm r := by
  have hp := descendingWeightList_perm s
  have hm : ((descendingWeightList s : List R) : Multiset R) = (s : Multiset R) :=
    Multiset.coe_eq_coe.mpr hp
  have hsorted : forall a, List.Mem a (descendingWeightList s) -> 0 <= a :=
    fun a ha => hs a (hp.mem_iff.mp ha)
  have h := sum_sub_take_sum_mul_esymm_le_ordered (descendingWeightList s)
    hsorted (descendingWeightList_pairwise s) r hr
  rw [hp.sum_eq, hm] at h
  exact h

/-- Both finite ratio bounds on their full positive-denominator domain.
All ordering dependence is contained in the explicit largest-weight sum. -/
theorem esymm_ratio_bounds_largest (s : List R)
    (hs : forall a, List.Mem a s -> 0 < a)
    (r : Nat) (hrPos : 1 <= r) (hr : r <= s.length)
    (hComplement : 0 < s.sum - largestWeightSum s (r - 1)) :
    (r : R) / s.sum <= (s : Multiset R).esymm (r - 1) / (s : Multiset R).esymm r /\
      (s : Multiset R).esymm (r - 1) / (s : Multiset R).esymm r <=
        (r : R) / (s.sum - largestWeightSum s (r - 1)) := by
  have hsm : forall a, Membership.mem (s : Multiset R) a -> 0 < a := fun a ha => hs a ha
  have hE : 0 < (s : Multiset R).esymm r :=
    Multiset.esymm_pos_ordered _ hsm r (by simpa using hr)
  have hS : 0 < s.sum := by
    change 0 < (s : Multiset R).sum
    rw [<- Multiset.esymm_one_ordered]
    exact Multiset.esymm_pos_ordered _ hsm 1 (by simpa using hrPos.trans hr)
  constructor
  next =>
    have h := Multiset.degree_mul_esymm_le_sum_mul_ordered (s : Multiset R)
      (fun a ha => (hsm a ha).le) r
    change (r : R) * (s : Multiset R).esymm r <=
      s.sum * (s : Multiset R).esymm (r - 1) at h
    have hd := div_le_div_of_nonneg_right h (mul_pos hS hE).le
    simpa only [mul_div_mul_right _ _ (ne_of_gt hE),
      mul_div_mul_left _ _ (ne_of_gt hS)] using hd
  next =>
    have h := sum_sub_largest_mul_esymm_le s (fun a ha => (hs a ha).le) r hrPos
    have hd := div_le_div_of_nonneg_right h (mul_pos hComplement hE).le
    simpa only [mul_div_mul_left _ _ (ne_of_gt hComplement),
      mul_div_mul_right _ _ (ne_of_gt hE)] using hd

/-- A threshold bounds the largest-weight sum by a linear cap and the total
positive excess. This needs no monotonicity or nonnegativity of the input. -/
theorem largestWeightSum_le_threshold_excess (s : List R) (r : Nat)
    (t : R) (ht : 0 <= t) :
    largestWeightSum s r <= (r : R) * t +
      (s.map (fun a => max (a - t) 0)).sum := by
  let f := fun a : R => max (a - t) 0
  have hnonneg : forall l : List R, 0 <= (l.map f).sum := by
    intro l
    induction l with
    | nil => simp
    | cons a l ih =>
        have hf : 0 <= f a := le_max_right _ _
        simp only [List.map_cons, List.sum_cons]
        exact add_nonneg hf ih
  have hprefix : forall l : List R, forall n : Nat,
      ((l.take n).map f).sum <= (l.map f).sum := by
    intro l
    induction l with
    | nil => intro n; simp
    | cons a l ih =>
        intro n
        cases n with
        | zero => simpa using hnonneg (a :: l)
        | succ n =>
            simp only [List.take_succ_cons, List.map_cons, List.sum_cons]
            linarith only [ih n]
  have hlinear : forall l : List R,
      l.sum <= (l.length : R) * t + (l.map f).sum := by
    intro l
    induction l with
    | nil => simp
    | cons a l ih =>
        have hf : a - t <= f a := le_max_left _ _
        simp only [List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one, List.map_cons]
        nlinarith only [hf, ih]
  have hlen : ((descendingWeightList s).take r).length <= r := by
    simpa only [List.length_take] using (min_le_left r (descendingWeightList s).length)
  have hlenR : (((descendingWeightList s).take r).length : R) <= r := by exact_mod_cast hlen
  have hmul := mul_le_mul_of_nonneg_right hlenR ht
  have htake := hlinear ((descendingWeightList s).take r)
  have hrest := hprefix (descendingWeightList s) r
  have hsum := ((descendingWeightList_perm s).map f).sum_eq
  change ((descendingWeightList s).take r).sum <= (r : R) * t + (s.map f).sum
  linarith only [hmul, htake, hrest, hsum]

end List

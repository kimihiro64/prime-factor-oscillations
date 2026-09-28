/-
Copyright (c) 2026 Prime Factor Oscillations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Elementary-symmetric inequalities for nonnegative rational weights

The induction generalizes the finite-weight argument in
`PrimeFactorUnimodality.Helpers.SymmetricBounds.Lower` and `Upper`, from
https://github.com/kimihiro64/erdos-690-prime-factor-unimodality at
commit ef3c9311d42b61db59f81d99741b5819d1986436 (Apache-2.0).
This module has no project or third-party imports. Weights may be zero.
-/

set_option autoImplicit false

namespace Multiset

/-- Successor recursion for rational elementary symmetric sums. -/
theorem esymm_cons_succ_rat (a : Rat) (s : Multiset Rat) (r : Nat) :
    (Multiset.cons a s).esymm (r + 1) = s.esymm (r + 1) + a * s.esymm r := by
  simp [Multiset.esymm, Multiset.powersetCard_cons, Multiset.sum_map_mul_left]

/-- Nonnegative rational weights have nonnegative elementary symmetric sums. -/
theorem esymm_nonneg_rat (s : Multiset Rat)
    (hs : forall a, Membership.mem s a -> 0 <= a) (r : Nat) :
    0 <= s.esymm r := by
  induction s using Multiset.induction_on generalizing r with
  | empty =>
      cases r with
      | zero => simp
      | succ r => rw [Multiset.esymm_of_card_lt (by simp)]
  | @cons a s ih =>
      have ha : 0 <= a := hs a (by simp)
      have ht : forall b, Membership.mem s b -> 0 <= b := by
        intro b hb
        exact hs b (by simp [hb])
      cases r with
      | zero => simp
      | succ r =>
          rw [esymm_cons_succ_rat]
          exact add_nonneg (ih ht (r + 1)) (mul_nonneg ha (ih ht r))

/-- The degree-one elementary symmetric sum is the total weight. -/
theorem esymm_one_rat (s : Multiset Rat) : s.esymm 1 = s.sum := by
  induction s using Multiset.induction_on with
  | empty => rw [Multiset.esymm_of_card_lt (by simp)]; rfl
  | @cons a s ih =>
      rw [show 1 = 0 + 1 by rfl, esymm_cons_succ_rat]
      simp [ih, add_comm]

/-- The universal polynomial lower ratio bound, including degrees beyond the support. -/
theorem degree_mul_esymm_le_sum_mul (s : Multiset Rat)
    (hs : forall a, Membership.mem s a -> 0 <= a) (r : Nat) :
    (r : Rat) * s.esymm r <= s.sum * s.esymm (r - 1) := by
  induction s using Multiset.induction_on generalizing r with
  | empty =>
      cases r with
      | zero => simp
      | succ r => rw [Multiset.esymm_of_card_lt (by simp)]; simp
  | @cons a s ih =>
      have ha : 0 <= a := hs a (by simp)
      have ht : forall b, Membership.mem s b -> 0 <= b := by
        intro b hb
        exact hs b (by simp [hb])
      cases r with
      | zero =>
          simp only [Nat.cast_zero, Nat.zero_sub, Multiset.esymm_zero, mul_one]
          exact Multiset.sum_nonneg hs
      | succ r =>
          cases r with
          | zero => simp [esymm_one_rat]
          | succ r =>
              have hhi := ih ht (r + 2)
              have hlo := ih ht (r + 1)
              have hnonneg := esymm_nonneg_rat s ht r
              have hscaled := mul_nonneg ha (sub_nonneg.mpr hlo)
              have hsquare := mul_nonneg (sq_nonneg a) hnonneg
              have hsub : r + 2 - 1 = r + 1 := by omega
              rw [hsub] at hhi
              simp only [Nat.add_sub_cancel] at hlo hscaled
              simp only [Nat.succ_sub_one, Multiset.sum_cons]
              rw [esymm_cons_succ_rat, esymm_cons_succ_rat]
              norm_num at hhi hlo hscaled
              norm_num
              nlinarith

/-- Strictly positive rational weights give positivity in every supported degree. -/
theorem esymm_pos_rat (s : Multiset Rat)
    (hs : forall a, Membership.mem s a -> 0 < a)
    (r : Nat) (hr : r <= s.card) : 0 < s.esymm r := by
  induction s using Multiset.induction_on generalizing r with
  | empty =>
      have hz : r = 0 := by simpa using hr
      subst r
      simp
  | @cons a s ih =>
      have ha : 0 < a := hs a (by simp)
      have ht : forall b, Membership.mem s b -> 0 < b := by
        intro b hb
        exact hs b (by simp [hb])
      cases r with
      | zero => simp
      | succ r =>
          rw [esymm_cons_succ_rat]
          apply add_pos_of_nonneg_of_pos
          next => exact esymm_nonneg_rat s (fun b hb => le_of_lt (ht b hb)) (r + 1)
          next => exact mul_pos ha (ih ht r (by simpa using hr))

end Multiset

namespace List

/-- Increasing the prefix length cannot reduce the sum of nonnegative weights. -/
theorem sum_take_succ_sub_nonneg_rat (s : List Rat)
    (hs : forall a, List.Mem a s -> 0 <= a) (n : Nat) :
    0 <= (s.take (n + 1)).sum - (s.take n).sum := by
  induction s generalizing n with
  | nil => simp
  | cons a s ih =>
      cases n with
      | zero => simpa using hs a (List.Mem.head _)
      | succ n =>
          simpa using ih (fun b hb => hs b (List.Mem.tail _ hb)) n

/-- Every prefix increment is bounded by a common upper bound on the weights. -/
theorem sum_take_succ_sub_le_rat (s : List Rat) (cap : Rat)
    (hcap0 : 0 <= cap) (hcap : forall a, List.Mem a s -> a <= cap) (n : Nat) :
    (s.take (n + 1)).sum - (s.take n).sum <= cap := by
  induction s generalizing n with
  | nil => simpa using hcap0
  | cons a s ih =>
      cases n with
      | zero => simpa using hcap a (List.Mem.head _)
      | succ n =>
          simpa using ih (fun b hb => hcap b (List.Mem.tail _ hb)) n

/-- Removing the largest `r-1` weights gives the complementary polynomial
upper ratio bound. No division or positive-denominator assumption is hidden. -/
theorem sum_sub_take_sum_mul_esymm_le_rat (s : List Rat)
    (hs : forall a, List.Mem a s -> 0 <= a)
    (hdescending : s.Pairwise (fun a b => b <= a))
    (r : Nat) (hr : 1 <= r) :
    (s.sum - (s.take (r - 1)).sum) * (s : Multiset Rat).esymm (r - 1) <=
      (r : Rat) * (s : Multiset Rat).esymm r := by
  induction s generalizing r with
  | nil =>
      cases r with
      | zero => omega
      | succ r =>
          have hn : (([] : List Rat) : Multiset Rat) = 0 := rfl
          have hempty : (0 : Multiset Rat).esymm (r + 1) = 0 :=
            Multiset.esymm_of_card_lt (by simp)
          rw [hn, hempty]
          simp
  | cons a s ih =>
      have ha : 0 <= a := hs a (List.Mem.head _)
      have ht : forall b, List.Mem b s -> 0 <= b :=
        fun b hb => hs b (List.Mem.tail _ hb)
      have htm : forall b, Membership.mem (s : Multiset Rat) b -> 0 <= b := by
        intro b hb
        exact ht b hb
      have hpair := List.pairwise_cons.mp hdescending
      cases r with
      | zero => omega
      | succ r =>
          cases r with
          | zero => simp [Multiset.esymm_one_rat]
          | succ n =>
              have hhi := ih ht hpair.2 (n + 2) (by omega)
              have hlo := ih ht hpair.2 (n + 1) (by omega)
              have hstep := sum_take_succ_sub_le_rat s a ha hpair.1 n
              have hEn1 := Multiset.esymm_nonneg_rat (s : Multiset Rat) htm (n + 1)
              have hscaled := mul_nonneg ha (sub_nonneg.mpr hlo)
              have hscaledStep := mul_nonneg (sub_nonneg.mpr hstep) hEn1
              simp only [List.sum_cons, List.take_succ_cons, Nat.succ_sub_one]
              have hc : ((a :: s : List Rat) : Multiset Rat) =
                  Multiset.cons a (s : Multiset Rat) := rfl
              rw [hc, Multiset.esymm_cons_succ_rat, Multiset.esymm_cons_succ_rat]
              norm_num at hhi hlo hscaled
              norm_num
              nlinarith

end List

/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Interval
import Mathlib.Tactic.Linarith

/-!
# Signed cost of displacing a finite prefix

Common coordinates are cancelled before the entering and leaving weights
are compared. The quantitative boundary cost is the arithmetic consumer
needed for universal finite-cutoff probability-profile rigidity.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace Finset

/-- Equal-size sets pay the full boundary difference on every displaced entry. -/
theorem card_sdiff_mul_sub_le_sum_sub_sum {I : Type*} [DecidableEq I]
    (s u : Finset I) (f : I -> Real) (a b : Real) (hc : s.card = u.card)
    (hs : forall i, Membership.mem (s \ u) i -> b <= f i)
    (hu : forall i, Membership.mem (u \ s) i -> f i <= a) :
    ((s \ u).card : Real) * (b - a) <= s.sum f - u.sum f := by
  have hcard : (s \ u).card = (u \ s).card := card_sdiff_comm hc
  have hlow := sum_le_sum (s := s \ u) (fun i hi => hs i hi)
  have hupp := sum_le_sum (s := u \ s) (fun i hi => hu i hi)
  simp only [sum_const, nsmul_eq_mul] at hlow hupp
  rw [<- hcard] at hupp
  have hid := @sum_sdiff_sub_sum_sdiff I Real u s inferInstance inferInstance f
  rw [<- hid]
  nlinarith only [hlow, hupp]

/-- The entire signed finite-prefix defect of a coordinate permutation. -/
def prefixDefect (w : Nat -> Real) (e : Equiv.Perm Nat) (k : Nat) : Real :=
  (range k).sum (fun i => w (e i)) - (range k).sum w

/-- Number of coordinates entering the first `k` positions from outside. -/
def prefixDisplacement (e : Equiv.Perm Nat) (k : Nat) : Nat :=
  ((range k).image e \ range k).card

/-- Every entering coordinate pays at least the adjacent boundary cost. -/
theorem prefixDisplacement_mul_gap_le_prefixDefect
    (w : Nat -> Real) (hw : Monotone w) (e : Equiv.Perm Nat) (k : Nat) :
    (prefixDisplacement e (k + 1) : Real) * (w (k + 1) - w k) <=
      prefixDefect w e (k + 1) := by
  have hc : ((range (k + 1)).image e).card = (range (k + 1)).card :=
    card_image_iff.mpr (fun _ _ _ _ h => e.injective h)
  have hb := card_sdiff_mul_sub_le_sum_sub_sum
    ((range (k + 1)).image e) (range (k + 1)) w (w k) (w (k + 1)) hc
    (fun i hi => hw (by
      have hn := (mem_sdiff.mp hi).2
      rw [mem_range] at hn
      omega))
    (fun i hi => hw (by
      have hn := (mem_sdiff.mp hi).1
      rw [mem_range] at hn
      omega))
  rw [sum_image (fun _ _ _ _ h => e.injective h)] at hb
  exact hb

/-- Zero displaced mass is exactly invariance of the entire prefix. -/
theorem prefixDisplacement_eq_zero_iff (e : Equiv.Perm Nat) (k : Nat) :
    prefixDisplacement e k = 0 <-> (range k).image e = range k := by
  unfold prefixDisplacement
  rw [card_eq_zero, sdiff_eq_empty_iff_subset]
  constructor
  . intro h
    exact eq_of_subset_of_card_le h (by
      rw [card_image_iff.mpr (fun _ _ _ _ he => e.injective he)])
  . intro h
    exact h.le

/-- A defect smaller than one boundary crossing certifies the whole prefix. -/
theorem image_range_eq_of_prefixDefect_lt_gap
    (w : Nat -> Real) (hw : StrictMono w) (e : Equiv.Perm Nat) (k : Nat)
    (h : prefixDefect w e (k + 1) < w (k + 1) - w k) :
    (range (k + 1)).image e = range (k + 1) := by
  apply (prefixDisplacement_eq_zero_iff e (k + 1)).mp
  by_contra hn
  have hc : (1 : Real) <= prefixDisplacement e (k + 1) := by
    exact_mod_cast (show 1 <= prefixDisplacement e (k + 1) by omega)
  have hg : 0 < w (k + 1) - w k := sub_pos.mpr (hw (Nat.lt_succ_self k))
  have hb := prefixDisplacement_mul_gap_le_prefixDefect w hw.monotone e k
  have hm := mul_le_mul_of_nonneg_right hc hg.le
  linarith only [h, hb, hm]

/-- Two invariant successive prefixes recover the coordinate between them. -/
theorem perm_apply_eq_of_image_range_eq (e : Equiv.Perm Nat) (k : Nat)
    (h0 : (range k).image e = range k)
    (h1 : (range (k + 1)).image e = range (k + 1)) : e k = k := by
  have hi : Membership.mem (range (k + 1)) (e k) := by
    rw [<- h1]
    exact mem_image_of_mem e (mem_range.mpr (Nat.lt_succ_self k))
  have hle : e k <= k := by
    have := mem_range.mp hi
    omega
  have hn : Not (e k < k) := by
    intro he
    have hm : Membership.mem ((range k).image e) (e k) := by
      rw [h0]
      exact mem_range.mpr he
    let j := Classical.choose (mem_image.mp hm)
    have hj : Membership.mem (range k) j /\ e j = e k :=
      Classical.choose_spec (mem_image.mp hm)
    have hjk : j = k := e.injective hj.2
    have := mem_range.mp hj.1
    omega
  omega

/-- A permutation fixed beyond a cutoff preserves every later prefix. -/
theorem image_range_eq_of_fixed_tail (e : Equiv.Perm Nat) (N k : Nat)
    (hfix : forall n, N <= n -> e n = n) (hNk : N <= k) :
    (range k).image e = range k := by
  apply eq_of_subset_of_card_le
  . intro j hj
    let i := Classical.choose (mem_image.mp hj)
    have hi : Membership.mem (range k) i /\ e i = j :=
      Classical.choose_spec (mem_image.mp hj)
    apply mem_range.mpr
    by_contra hn
    have hkj : k <= j := by omega
    have hjfix := hfix j (hNk.trans hkj)
    have hij : i = j := e.injective (hi.2.trans hjfix.symm)
    have := mem_range.mp hi.1
    omega
  . rw [card_image_iff.mpr (fun _ _ _ _ he => e.injective he)]

/-- Prefix invariance cancels the entire finite signed defect exactly. -/
theorem prefixDefect_eq_zero_of_image_range_eq
    (w : Nat -> Real) (e : Equiv.Perm Nat) (k : Nat)
    (h : (range k).image e = range k) : prefixDefect w e k = 0 := by
  unfold prefixDefect
  have hs : ((range k).image e).sum w = (range k).sum (fun i => w (e i)) :=
    sum_image (fun _ _ _ _ he => e.injective he)
  rw [<- hs, h, sub_self]

/-- A missing entry has a signed cost even when the two cardinalities differ. -/
theorem neg_boundary_le_sum_sub_sum_of_card_lt {I : Type*} [DecidableEq I]
    (s u : Finset I) (f : I -> Real) (a : Real) (ha : a <= 0)
    (hc : s.card < u.card)
    (hs : forall i, Membership.mem (s \ u) i -> a <= f i)
    (hu : forall i, Membership.mem (u \ s) i -> f i <= a) :
    -a <= s.sum f - u.sum f := by
  have hcs := card_sdiff_add_card_inter s u
  have hcu := card_sdiff_add_card_inter u s
  have hci : (s \ u).card < (u \ s).card := by
    rw [inter_comm u s] at hcu
    omega
  have hcr : ((s \ u).card : Real) + 1 <= (u \ s).card := by
    exact_mod_cast (Nat.succ_le_of_lt hci)
  have hm := mul_le_mul_of_nonpos_right hcr ha
  have hlo := sum_le_sum (s := s \ u) (fun i hi => hs i hi)
  have hup := sum_le_sum (s := u \ s) (fun i hi => hu i hi)
  simp only [sum_const, nsmul_eq_mul] at hlo hup
  have hid := @sum_sdiff_sub_sum_sdiff I Real u s inferInstance inferInstance f
  rw [<- hid]
  nlinarith only [hm, hlo, hup]

/-- Insert a common reference only after the common coordinates cancel. -/
theorem sum_sub_sum_eq_reference_transport {I : Type*} [DecidableEq I]
    (s u : Finset I) (f : I -> Real) (a : Real) (hc : s.card = u.card) :
    s.sum f - u.sum f =
      (s \ u).sum (fun i => f i - a) + (u \ s).sum (fun i => a - f i) := by
  have hcard : (s \ u).card = (u \ s).card := card_sdiff_comm hc
  have hid := @sum_sdiff_sub_sum_sdiff I Real u s inferInstance inferInstance f
  rw [<- hid, sum_sub_distrib, sum_sub_distrib, sum_const, sum_const,
    nsmul_eq_mul, nsmul_eq_mul, hcard]
  linarith

/-- Each entering reference cost is bounded by the complete signed defect. -/
theorem incoming_reference_le_sum_sub_sum {I : Type*} [DecidableEq I]
    (s u : Finset I) (f : I -> Real) (a : Real) (hc : s.card = u.card)
    (hs : forall i, Membership.mem (s \ u) i -> a <= f i)
    (hu : forall i, Membership.mem (u \ s) i -> f i <= a)
    (j : I) (hj : Membership.mem (s \ u) j) :
    f j - a <= s.sum f - u.sum f := by
  rw [sum_sub_sum_eq_reference_transport s u f a hc]
  have hsingle := single_le_sum
    (fun i hi => sub_nonneg.mpr (hs i hi)) hj
  have hrest := sum_nonneg (s := u \ s)
    (fun i hi => sub_nonneg.mpr (hu i hi))
  linarith only [hsingle, hrest]

/-- Each leaving reference cost is bounded by the complete signed defect. -/
theorem outgoing_reference_le_sum_sub_sum {I : Type*} [DecidableEq I]
    (s u : Finset I) (f : I -> Real) (a : Real) (hc : s.card = u.card)
    (hs : forall i, Membership.mem (s \ u) i -> a <= f i)
    (hu : forall i, Membership.mem (u \ s) i -> f i <= a)
    (j : I) (hj : Membership.mem (u \ s) j) :
    a - f j <= s.sum f - u.sum f := by
  rw [sum_sub_sum_eq_reference_transport s u f a hc]
  have hsingle := single_le_sum
    (fun i hi => sub_nonneg.mpr (hu i hi)) hj
  have hrest := sum_nonneg (s := s \ u)
    (fun i hi => sub_nonneg.mpr (hs i hi))
  linarith only [hsingle, hrest]

/-- Compare the full signed transport after the same reference decomposition. -/
theorem reference_transport_comparison {I : Type*} [DecidableEq I]
    (s u : Finset I) (f g : I -> Real) (a b L U : Real) (hc : s.card = u.card)
    (hin : forall i, Membership.mem (s \ u) i ->
      L * (f i - a) <= g i - b /\ g i - b <= U * (f i - a))
    (hout : forall i, Membership.mem (u \ s) i ->
      L * (a - f i) <= b - g i /\ b - g i <= U * (a - f i)) :
    L * (s.sum f - u.sum f) <= s.sum g - u.sum g /\
      s.sum g - u.sum g <= U * (s.sum f - u.sum f) := by
  constructor
  . rw [sum_sub_sum_eq_reference_transport s u f a hc,
      sum_sub_sum_eq_reference_transport s u g b hc, mul_add, mul_sum, mul_sum]
    exact add_le_add (sum_le_sum (fun i hi => (hin i hi).1))
      (sum_le_sum (fun i hi => (hout i hi).1))
  . rw [sum_sub_sum_eq_reference_transport s u f a hc,
      sum_sub_sum_eq_reference_transport s u g b hc, mul_add, mul_sum, mul_sum]
    exact add_le_add (sum_le_sum (fun i hi => (hin i hi).2))
      (sum_le_sum (fun i hi => (hout i hi).2))

/-- Equal-cardinality odd-coordinate sums have an even natural difference. -/
theorem exists_nat_sum_sub_sum_eq_twice {I : Type*}
    (s u : Finset I) (f : I -> Nat) (hc : s.card = u.card)
    (hs : forall i, Membership.mem s i -> f i % 2 = 1)
    (hu : forall i, Membership.mem u i -> f i % 2 = 1) :
    exists k : Nat, s.sum f - u.sum f = 2 * k := by
  have hsone : s.sum (fun i => f i % 2) = s.card := by
    calc
      _ = s.sum (fun _ => 1) := sum_congr rfl hs
      _ = _ := by simp
  have huone : u.sum (fun i => f i % 2) = u.card := by
    calc
      _ = u.sum (fun _ => 1) := sum_congr rfl hu
      _ = _ := by simp
  have hsmod : s.sum f % 2 = s.card % 2 := by rw [sum_nat_mod s 2 f, hsone]
  have humod : u.sum f % 2 = u.card % 2 := by rw [sum_nat_mod u 2 f, huone]
  let d := s.sum f - u.sum f
  have hd : d % 2 = 0 := by dsimp only [d]; omega
  have he := Nat.mod_add_div d 2
  exact Exists.intro (d / 2) (by dsimp only [d] at hd he; omega)

end Finset

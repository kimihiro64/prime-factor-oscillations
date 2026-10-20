/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import Mathlib.Tactic.Ring
import PrimeFactorOscillations.Mathlib.Combinatorics.FinitePrefixDisplacement

/-!
# Exact signed prefixes of disjoint adjacent swaps

Every completed pair cancels exactly. The unique crossing pair is the
consumer for optimal adaptive prime-profile distortion.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

attribute [local instance] Classical.propDecidable

namespace Finset

def adjacentSwapPartner (A : Set Nat) (n : Nat) : Nat := by
  classical
  exact if Membership.mem A n then n + 1 else
    if 0 < n then (if Membership.mem A (n - 1) then n - 1 else n) else n

theorem adjacentSwapPartner_involutive (A : Set Nat)
    (hA : forall n, Membership.mem A n -> Not (Membership.mem A (n + 1))) :
    Function.Involutive (adjacentSwapPartner A) := by
  classical
  intro n
  by_cases hn : Membership.mem A n
  . have hnext := hA n hn
    have he : adjacentSwapPartner A n = n + 1 := by simp [adjacentSwapPartner, hn]
    rw [he]
    have hprev : n + 1 - 1 = n := by omega
    simp [adjacentSwapPartner, hnext, hprev, hn]
  . by_cases hpos : 0 < n
    . by_cases hprev : Membership.mem A (n - 1)
      . have he : adjacentSwapPartner A n = n - 1 := by
          simp [adjacentSwapPartner, hn, hpos, hprev]
        rw [he]
        have hp : adjacentSwapPartner A (n - 1) = n - 1 + 1 := by
          simp [adjacentSwapPartner, hprev]
        rw [hp]
        omega
      . have he : adjacentSwapPartner A n = n := by
          simp [adjacentSwapPartner, hn, hpos, hprev]
        rw [he]
        exact he
    . have he : adjacentSwapPartner A n = n := by
        simp [adjacentSwapPartner, hn, hpos]
      rw [he]
      exact he

def adjacentSwapPerm (A : Set Nat)
    (hA : forall n, Membership.mem A n -> Not (Membership.mem A (n + 1))) :
    Equiv.Perm Nat where
  toFun := adjacentSwapPartner A
  invFun := adjacentSwapPartner A
  left_inv := adjacentSwapPartner_involutive A hA
  right_inv := adjacentSwapPartner_involutive A hA

theorem adjacentSwapPartner_weight_diff (w : Nat -> Real) (A : Set Nat)
    (hA : forall n, Membership.mem A n -> Not (Membership.mem A (n + 1))) (n : Nat) :
    w (adjacentSwapPartner A (n + 1)) - w (n + 1) =
      (if Membership.mem A (n + 1) then w (n + 2) - w (n + 1) else 0) -
      (if Membership.mem A n then w (n + 1) - w n else 0) := by
  classical
  by_cases hnext : Membership.mem A (n + 1)
  . have hn : Not (Membership.mem A n) := fun h => hA n h hnext
    simp [adjacentSwapPartner, hnext, hn, Nat.add_assoc]
  . by_cases hn : Membership.mem A n
    . simp [adjacentSwapPartner, hnext, hn]
    . simp [adjacentSwapPartner, hnext, hn]

/-- Every completed pair cancels; only the pair crossing the boundary survives. -/
theorem prefixDefect_adjacentSwapPerm (w : Nat -> Real) (A : Set Nat)
    (hA : forall n, Membership.mem A n -> Not (Membership.mem A (n + 1))) (n : Nat) :
    prefixDefect w (adjacentSwapPerm A hA) (n + 1) =
      if Membership.mem A n then w (n + 1) - w n else 0 := by
  classical
  induction n with
  | zero =>
    simp only [prefixDefect, sum_range_succ, sum_range_zero, zero_add]
    change w (adjacentSwapPartner A 0) - w 0 =
      if Membership.mem A 0 then w 1 - w 0 else 0
    by_cases h0 : Membership.mem A 0
    . simp [adjacentSwapPartner, h0]
    . simp [adjacentSwapPartner, h0]
  | succ n ih =>
    have hstep : prefixDefect w (adjacentSwapPerm A hA) (n + 2) =
        prefixDefect w (adjacentSwapPerm A hA) (n + 1) +
        (w (adjacentSwapPartner A (n + 1)) - w (n + 1)) := by
      unfold prefixDefect
      simp only [sum_range_succ]
      change _ = _ + (w ((adjacentSwapPerm A hA) (n + 1)) - w (n + 1))
      ring
    change prefixDefect w (adjacentSwapPerm A hA) (n + 2) = _
    rw [hstep, ih, adjacentSwapPartner_weight_diff w A hA n]
    ring

end Finset

namespace Set

/-- An unbounded natural set contains an unbounded subset with no neighbors. -/
theorem exists_unbounded_nonadjacent_subset (S : Set Nat)
    (hS : forall N : Nat, exists n : Nat, N <= n /\ Membership.mem S n) :
    exists A : Set Nat,
      (forall n, Membership.mem A n -> Membership.mem S n) /\
      (forall n, Membership.mem A n -> Not (Membership.mem A (n + 1))) /\
      (forall N : Nat, exists n : Nat, N <= n /\ Membership.mem A n) := by
  classical
  let next : Nat -> Nat := fun N => Classical.choose (hS N)
  have hnext : forall N : Nat, N <= next N /\ Membership.mem S (next N) :=
    fun N => Classical.choose_spec (hS N)
  let f : Nat -> Nat := Nat.rec (next 0) (fun _ v => next (v + 2))
  have hstep : forall k : Nat, f k + 2 <= f (k + 1) := by
    intro k
    change f k + 2 <= next (f k + 2)
    exact (hnext (f k + 2)).1
  have hmono : StrictMono f := strictMono_nat_of_lt_succ (fun k => by
    have hs := hstep k
    omega)
  have hfS : forall k : Nat, Membership.mem S (f k) := by
    intro k
    cases k with
    | zero => exact (hnext 0).2
    | succ k => exact (hnext (f k + 2)).2
  let A : Set Nat := Set.range f
  refine Exists.intro A (And.intro ?_ (And.intro ?_ ?_))
  . intro n hn
    have hex : exists k : Nat, f k = n := hn
    let k := Classical.choose hex
    have hk : f k = n := Classical.choose_spec hex
    rw [<- hk]
    exact hfS k
  . intro n hn hn1
    have hiEx : exists i : Nat, f i = n := hn
    have hjEx : exists j : Nat, f j = n + 1 := hn1
    let i := Classical.choose hiEx
    let j := Classical.choose hjEx
    have hi : f i = n := Classical.choose_spec hiEx
    have hj : f j = n + 1 := Classical.choose_spec hjEx
    by_cases hij : i < j
    . have hindex : i + 1 <= j := by omega
      have hle : f (i + 1) <= f j := hmono.monotone hindex
      have hgap := hstep i
      omega
    . have hindex : j <= i := by omega
      have hle : f j <= f i := hmono.monotone hindex
      omega
  . intro N
    exact Exists.intro (f N) (And.intro (hmono.id_le N) (Exists.intro N rfl))

/-- Unbounded supports admit arbitrarily prescribed positive index separation. -/
theorem exists_unbounded_separated_subset (S : Set Nat)
    (hS : forall N : Nat, exists n : Nat, N <= n /\ Membership.mem S n)
    (L : Nat) (hL : 0 < L) :
    exists A : Set Nat,
      (forall n, Membership.mem A n -> Membership.mem S n) /\
      (forall a, Membership.mem A a -> forall b, Membership.mem A b ->
        a < b -> a + L <= b) /\
      (forall N : Nat, exists n : Nat, N <= n /\ Membership.mem A n) := by
  classical
  let next : Nat -> Nat := fun N => Classical.choose (hS N)
  have hnext : forall N : Nat, N <= next N /\ Membership.mem S (next N) :=
    fun N => Classical.choose_spec (hS N)
  let f : Nat -> Nat := Nat.rec (next 0) (fun _ v => next (v + L))
  have hstep : forall k : Nat, f k + L <= f (k + 1) := by
    intro k
    change f k + L <= next (f k + L)
    exact (hnext (f k + L)).1
  have hmono : StrictMono f := strictMono_nat_of_lt_succ (fun k => by
    have hs := hstep k
    omega)
  have hfS : forall k : Nat, Membership.mem S (f k) := by
    intro k
    cases k with
    | zero => exact And.right (hnext 0)
    | succ k => exact And.right (hnext (f k + L))
  let A : Set Nat := Set.range f
  refine Exists.intro A (And.intro ?_ (And.intro ?_ ?_))
  . intro n hn
    have hex : exists k : Nat, f k = n := hn
    let k := Classical.choose hex
    have hk : f k = n := Classical.choose_spec hex
    rw [<- hk]
    exact hfS k
  . intro a ha b hb hab
    have hiEx : exists i : Nat, f i = a := ha
    have hjEx : exists j : Nat, f j = b := hb
    let i := Classical.choose hiEx
    let j := Classical.choose hjEx
    have hi : f i = a := Classical.choose_spec hiEx
    have hj : f j = b := Classical.choose_spec hjEx
    have hij : i < j := by
      by_contra hn
      have hindex : j <= i := by omega
      have hle : f j <= f i := hmono.monotone hindex
      omega
    have hindex : i + 1 <= j := by omega
    have hle : f (i + 1) <= f j := hmono.monotone hindex
    have hgap := hstep i
    omega
  . intro N
    exact Exists.intro (f N) (And.intro (hmono.id_le N) (Exists.intro N rfl))

end Set

/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Mathlib.Combinatorics.AdjacentSwapPrefix

/-!
# Exact signed prefixes of disjoint distance-two swaps

Selected starts may be adjacent, but starts two apart are forbidden.
Completed pairs cancel exactly. The two possible crossing edges are
retained separately, with their full signed weights.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

attribute [local instance] Classical.propDecidable

namespace Finset

def twoStepSwapPartner (B : Set Nat) (n : Nat) : Nat := by
  classical
  exact if Membership.mem B n then n + 2 else
    if 2 <= n then (if Membership.mem B (n - 2) then n - 2 else n) else n

theorem twoStepSwapPartner_involutive (B : Set Nat)
    (hB : forall n, Membership.mem B n -> Not (Membership.mem B (n + 2))) :
    Function.Involutive (twoStepSwapPartner B) := by
  classical
  intro n
  by_cases hn : Membership.mem B n
  . have hnext := hB n hn
    have he : twoStepSwapPartner B n = n + 2 := by simp [twoStepSwapPartner, hn]
    rw [he]
    have hprev : n + 2 - 2 = n := by omega
    have hpos : 2 <= n + 2 := by omega
    simp [twoStepSwapPartner, hnext, hprev, hn, hpos]
  . by_cases hpos : 2 <= n
    . by_cases hprev : Membership.mem B (n - 2)
      . have he : twoStepSwapPartner B n = n - 2 := by
          simp [twoStepSwapPartner, hn, hpos, hprev]
        rw [he]
        have hp : twoStepSwapPartner B (n - 2) = n - 2 + 2 := by
          simp [twoStepSwapPartner, hprev]
        rw [hp]
        omega
      . have he : twoStepSwapPartner B n = n := by
          simp [twoStepSwapPartner, hn, hpos, hprev]
        rw [he]
        exact he
    . have he : twoStepSwapPartner B n = n := by
        simp [twoStepSwapPartner, hn, hpos]
      rw [he]
      exact he

def twoStepSwapPerm (B : Set Nat)
    (hB : forall n, Membership.mem B n -> Not (Membership.mem B (n + 2))) :
    Equiv.Perm Nat where
  toFun := twoStepSwapPartner B
  invFun := twoStepSwapPartner B
  left_inv := twoStepSwapPartner_involutive B hB
  right_inv := twoStepSwapPartner_involutive B hB

theorem twoStepSwapPartner_weight_diff (w : Nat -> Real) (B : Set Nat)
    (hB : forall n, Membership.mem B n -> Not (Membership.mem B (n + 2))) (n : Nat) :
    w (twoStepSwapPartner B (n + 2)) - w (n + 2) =
      (if Membership.mem B (n + 2) then w (n + 4) - w (n + 2) else 0) -
      (if Membership.mem B n then w (n + 2) - w n else 0) := by
  classical
  have hpos : 2 <= n + 2 := by omega
  have hprev : n + 2 - 2 = n := by omega
  by_cases hnext : Membership.mem B (n + 2)
  . have hn : Not (Membership.mem B n) := fun h => hB n h hnext
    simp [twoStepSwapPartner, hnext, hn, Nat.add_assoc]
  . by_cases hn : Membership.mem B n
    . simp [twoStepSwapPartner, hnext, hn, hpos, hprev]
    . simp [twoStepSwapPartner, hnext, hn, hpos, hprev]

theorem prefixDefect_twoStepSwapPerm (w : Nat -> Real) (B : Set Nat)
    (hB : forall n, Membership.mem B n -> Not (Membership.mem B (n + 2))) (n : Nat) :
    prefixDefect w (twoStepSwapPerm B hB) (n + 2) =
      (if Membership.mem B (n + 1) then w (n + 3) - w (n + 1) else 0) +
      (if Membership.mem B n then w (n + 2) - w n else 0) := by
  classical
  induction n with
  | zero =>
    simp only [prefixDefect, sum_range_succ, sum_range_zero, zero_add]
    change w (twoStepSwapPartner B 0) + w (twoStepSwapPartner B 1) -
      (w 0 + w 1) =
      (if Membership.mem B 1 then w 3 - w 1 else 0) +
      (if Membership.mem B 0 then w 2 - w 0 else 0)
    by_cases h0 : Membership.mem B 0
    . by_cases h1 : Membership.mem B 1
      . simp [twoStepSwapPartner, h0, h1]
        ring
      . simp [twoStepSwapPartner, h0, h1]
    . by_cases h1 : Membership.mem B 1
      . simp [twoStepSwapPartner, h0, h1]
      . simp [twoStepSwapPartner, h0, h1]
  | succ n ih =>
    have hstep : prefixDefect w (twoStepSwapPerm B hB) (n + 3) =
        prefixDefect w (twoStepSwapPerm B hB) (n + 2) +
        (w (twoStepSwapPartner B (n + 2)) - w (n + 2)) := by
      unfold prefixDefect
      simp only [sum_range_succ]
      change _ = _ + (w ((twoStepSwapPerm B hB) (n + 2)) - w (n + 2))
      ring
    change prefixDefect w (twoStepSwapPerm B hB) (n + 3) = _
    rw [hstep, ih, twoStepSwapPartner_weight_diff w B hB n]
    ring

/-- Adjacent selected starts force two distinct coordinates across the cutoff. -/
theorem two_le_prefixDisplacement_twoStepSwapPerm (B : Set Nat)
    (hB : forall n, Membership.mem B n -> Not (Membership.mem B (n + 2)))
    (n : Nat) (hn : Membership.mem B n) (hn1 : Membership.mem B (n + 1)) :
    2 <= prefixDisplacement (twoStepSwapPerm B hB) (n + 2) := by
  have he0 : (twoStepSwapPerm B hB) n = n + 2 := by
    change twoStepSwapPartner B n = n + 2
    simp [twoStepSwapPartner, hn]
  have he1 : (twoStepSwapPerm B hB) (n + 1) = n + 3 := by
    change twoStepSwapPartner B (n + 1) = n + 3
    simp [twoStepSwapPartner, hn1, Nat.add_assoc]
  have hsub : forall j, Membership.mem ({n + 2, n + 3} : Finset Nat) j ->
      Membership.mem ((range (n + 2)).image (twoStepSwapPerm B hB) \
        range (n + 2)) j := by
    intro j hj
    simp only [mem_insert, mem_singleton] at hj
    apply mem_sdiff.mpr
    cases hj with
    | inl hj =>
      subst j
      exact And.intro (mem_image.mpr (Exists.intro n
        (And.intro (mem_range.mpr (by omega)) he0))) (by simp)
    | inr hj =>
      subst j
      exact And.intro (mem_image.mpr (Exists.intro (n + 1)
        (And.intro (mem_range.mpr (by omega)) he1))) (by simp)
  have hcard := card_le_card hsub
  have he : ({n + 2, n + 3} : Finset Nat).card = 2 := by simp
  rw [he] at hcard
  exact hcard

end Finset

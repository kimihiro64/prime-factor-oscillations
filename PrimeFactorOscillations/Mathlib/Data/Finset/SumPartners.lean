/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Lean.Elab.Tactic.Omega
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Union

/-!
# Robust representations of a sum after deleting inputs

Each first summand records one ordered representation. Removing E elements
loses at most 2E representations of a fixed sum; at most one is diagonal.
The two deletion contributions remain together in the complete bound.
-/

set_option autoImplicit false
set_option Elab.async false

namespace Finset

def sumPartners (P : Finset Nat) (n : Nat) : Finset Nat :=
  P.filter (fun p => Membership.mem P (n - p) /\ p <= n)

theorem exists_distinct_sum_of_card_sumPartners_gt (P S : Finset Nat) (n : Nat)
    (hCount : 2 * (SDiff.sdiff P S).card + 1 < (sumPartners P n).card) :
    exists p, exists q, And (Membership.mem S p)
      (And (Membership.mem S q) (And (Not (p = q)) (p + q = n))) := by
  classical
  by_contra h
  have hCover : sumPartners P n <=
      Union.union (Union.union (SDiff.sdiff P S) ((SDiff.sdiff P S).image (fun p => n - p))) {n / 2} := by
    intro p hp
    have hpData := Finset.mem_filter.mp hp
    by_cases hpS : Membership.mem S p
    next =>
      by_cases hqS : Membership.mem S (n - p)
      next =>
        have heq : p = n - p := by
          by_contra hne
          exact h (Exists.intro p (Exists.intro (n - p)
            (And.intro hpS (And.intro hqS (And.intro hne (by omega))))))
        have hpHalf : p = n / 2 := by omega
        exact Finset.mem_union_right _ (Finset.mem_singleton.mpr hpHalf)
      next =>
        have hq : Membership.mem (SDiff.sdiff P S) (n - p) :=
          Finset.mem_sdiff.mpr (And.intro hpData.2.1 hqS)
        have hi : Membership.mem ((SDiff.sdiff P S).image (fun q => n - q)) p := by
          apply Finset.mem_image.mpr
          exact Exists.intro (n - p) (And.intro hq (by omega))
        exact Finset.mem_union_left _ (Finset.mem_union_right _ hi)
    next =>
      exact Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_sdiff.mpr (And.intro hpData.1 hpS)))
  have hCard := Finset.card_le_card hCover
  have hUnion := Finset.card_union_le
    (Union.union (SDiff.sdiff P S) ((SDiff.sdiff P S).image (fun p => n - p))) {n / 2}
  have hInner := Finset.card_union_le (SDiff.sdiff P S) ((SDiff.sdiff P S).image (fun p => n - p))
  have hImage := Finset.card_image_le (s := SDiff.sdiff P S) (f := fun p => n - p)
  have hSingle : ({n / 2} : Finset Nat).card = 1 := Finset.card_singleton _
  omega

end Finset

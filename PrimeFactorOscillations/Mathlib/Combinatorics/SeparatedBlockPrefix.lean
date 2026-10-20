/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import Mathlib.Logic.Equiv.Basic
import PrimeFactorOscillations.Mathlib.Combinatorics.FinitePrefixDisplacement

/-!
# Exact finite-prefix transport by separated block exchanges

Two disjoint intervals of equal finite length are exchanged pointwise. The
prefix defect retains the complete entering and leaving sums, and the far
block contributes its full cardinality outside every earlier cutoff.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace Equiv

/-- The underlying map exchanging the two half-open natural intervals. -/
def separatedBlockSwapFun (a b k x : Nat) : Nat :=
  if a <= x /\ x < a + k then b + (x - a)
  else if b <= x /\ x < b + k then a + (x - b)
  else x

/-- Separation makes the two explicit branches a genuine involution. -/
theorem separatedBlockSwapFun_involutive (a b k : Nat) (hsep : a + k <= b) :
    Function.Involutive (separatedBlockSwapFun a b k) := by
  intro x
  by_cases ha : a <= x /\ x < a + k
  . have hna : Not (a <= b + (x - a) /\ b + (x - a) < a + k) := by omega
    have hbin : b <= b + (x - a) /\ b + (x - a) < b + k := by omega
    simp only [separatedBlockSwapFun, ite_eq_left ha, ite_eq_right hna, ite_eq_left hbin]
    omega
  . by_cases hb : b <= x /\ x < b + k
    . have hain : a <= a + (x - b) /\ a + (x - b) < a + k := by omega
      simp only [separatedBlockSwapFun, ite_eq_right ha, ite_eq_left hb, ite_eq_left hain]
      omega
    . simp only [separatedBlockSwapFun, ite_eq_right ha, ite_eq_right hb]

/-- A finite permutation exchanging the two separated blocks. -/
def separatedBlockSwap (a b k : Nat) (hsep : a + k <= b) : Equiv.Perm Nat where
  toFun := separatedBlockSwapFun a b k
  invFun := separatedBlockSwapFun a b k
  left_inv := separatedBlockSwapFun_involutive a b k hsep
  right_inv := separatedBlockSwapFun_involutive a b k hsep

/-- The first block is translated exactly onto the second block. -/
theorem separatedBlockSwap_apply_left (a b k : Nat) (hsep : a + k <= b)
    (i : Nat) (hi : i < k) : separatedBlockSwap a b k hsep (a + i) = b + i := by
  have ha : a <= a + i /\ a + i < a + k := by omega
  change separatedBlockSwapFun a b k (a + i) = b + i
  simp only [separatedBlockSwapFun, ite_eq_left ha]
  omega

/-- Every coordinate below the first block is fixed. -/
theorem separatedBlockSwap_apply_below (a b k : Nat) (hsep : a + k <= b)
    (i : Nat) (hi : i < a) : separatedBlockSwap a b k hsep i = i := by
  have ha : Not (a <= i /\ i < a + k) := by omega
  have hb : Not (b <= i /\ i < b + k) := by omega
  change separatedBlockSwapFun a b k i = i
  simp only [separatedBlockSwapFun, ite_eq_right ha, ite_eq_right hb]

/-- All coordinates beyond the end of the far block are fixed. -/
theorem separatedBlockSwap_apply_tail (a b k : Nat) (hsep : a + k <= b)
    (i : Nat) (hi : b + k <= i) : separatedBlockSwap a b k hsep i = i := by
  have ha : Not (a <= i /\ i < a + k) := by omega
  have hb : Not (b <= i /\ i < b + k) := by omega
  change separatedBlockSwapFun a b k i = i
  simp only [separatedBlockSwapFun, ite_eq_right ha, ite_eq_right hb]

end Equiv

namespace Finset

/-- The complete signed prefix defect of an entire crossing block. -/
theorem prefixDefect_separatedBlockSwap (w : Nat -> Real) (a b k : Nat)
    (hsep : a + k <= b) :
    prefixDefect w (Equiv.separatedBlockSwap a b k hsep) (a + k) =
      (range k).sum (fun i => w (b + i)) -
        (range k).sum (fun i => w (a + i)) := by
  unfold prefixDefect
  rw [sum_range_add, sum_range_add]
  have hfirst : (range a).sum (fun i => w (Equiv.separatedBlockSwap a b k hsep i)) =
      (range a).sum w := by
    apply sum_congr rfl
    intro i hi
    rw [Equiv.separatedBlockSwap_apply_below a b k hsep i (mem_range.mp hi)]
  have hlast : (range k).sum
      (fun i => w (Equiv.separatedBlockSwap a b k hsep (a + i))) =
        (range k).sum (fun i => w (b + i)) := by
    apply sum_congr rfl
    intro i hi
    rw [Equiv.separatedBlockSwap_apply_left a b k hsep i (mem_range.mp hi)]
  rw [hfirst, hlast]
  linarith

/-- Every index of the far block appears outside an arbitrary earlier cutoff. -/
theorem card_le_prefixTail_separatedBlockSwap (a b k M : Nat)
    (hsep : a + k <= b) (hM : M <= b) :
    k <= (((range (a + k)).image (Equiv.separatedBlockSwap a b k hsep)) \ range M).card := by
  let T := (range k).image (fun i => b + i)
  have hsub : forall j, Membership.mem T j -> Membership.mem
      (((range (a + k)).image (Equiv.separatedBlockSwap a b k hsep)) \ range M) j := by
    intro j hj
    have hex := mem_image.mp hj
    let i := Classical.choose hex
    have hi := Classical.choose_spec hex
    have hik : i < k := mem_range.mp hi.1
    apply mem_sdiff.mpr
    constructor
    . apply mem_image.mpr
      refine Exists.intro (a + i) (And.intro (mem_range.mpr (by omega)) ?_)
      exact (Equiv.separatedBlockSwap_apply_left a b k hsep i hik).trans hi.2
    . intro hjM
      have hjlt : j < M := mem_range.mp hjM
      omega
  have hcard : T.card = k := by
    dsimp only [T]
    rw [card_image_iff.mpr (fun _ _ _ _ h => by omega), card_range]
  have h := card_le_card hsub
  rwa [hcard] at h

end Finset

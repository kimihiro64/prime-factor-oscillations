/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import Mathlib.Logic.Equiv.Basic
import PrimeFactorOscillations.Mathlib.Combinatorics.FinitePrefixDisplacement

/-!
# Exact signed prefix defect of a transposition across the cutoff

A single crossing swap has exactly one retained incoming and outgoing weight.
This identity keeps the finite prefix length and both swap endpoints explicit.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace Finset

/-- A crossing transposition has exactly the signed difference of its endpoint weights. -/
theorem prefixDefect_swap_of_crossing (w : Nat -> Real) (i j k : Nat)
    (hi : i < k) (hkj : k <= j) :
    prefixDefect w (Equiv.swap i j) k = w j - w i := by
  unfold prefixDefect
  rw [<- Finset.sum_sub_distrib]
  calc
    _ = w (Equiv.swap i j i) - w i := by
      apply Finset.sum_eq_single i
      . intro a ha hai
        have hak := Finset.mem_range.mp ha
        have haj : Not (a = j) := by omega
        rw [Equiv.swap_apply_of_ne_of_ne hai haj, sub_self]
      . intro hnot
        exact False.elim (hnot (Finset.mem_range.mpr hi))
    _ = w j - w i := by rw [Equiv.swap_apply_left]

end Finset

/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.ZMod.Basic

/-!
# Uniform counts in shifted residue sets

The quotient and residue identify an integer uniquely. This gives an
interval-count bound uniform in the selected residue set and its shift,
including modulus one and the single-point interval.
-/

set_option autoImplicit false
set_option Elab.async false

namespace ZMod

/-- Count a shifted residue event in the inclusive interval from zero to N. -/
theorem card_filter_range_succ_add_mem_le
    (q N : Nat) [NeZero q] (z : ZMod q) (R : Finset (ZMod q)) :
    ((Finset.range (N + 1)).filter fun n : Nat => Membership.mem R ((n : ZMod q) + z)).card <=
      (N / q + 1) * R.card := by
  classical
  let f : Nat -> Prod Nat (ZMod q) := fun n => (n / q, (n : ZMod q) + z)
  have hf : Function.Injective f := by
    intro n k hnk
    have hdiv : n / q = k / q := congrArg Prod.fst hnk
    have hcast : (n : ZMod q) = (k : ZMod q) :=
      add_right_cancel (congrArg Prod.snd hnk)
    have hmod : n % q = k % q := by
      simpa only [ZMod.val_natCast] using congrArg ZMod.val hcast
    have hn := Nat.mod_add_div n q
    have hk := Nat.mod_add_div k q
    rw [hmod, hdiv] at hn
    exact hn.symm.trans hk
  have hsub :
      (((Finset.range (N + 1)).filter fun n : Nat => Membership.mem R ((n : ZMod q) + z)).image f) <=
      (Finset.range (N / q + 1)).product R := by
    intro x hx
    cases Finset.mem_image.mp hx with
    | intro n hn =>
        cases hn with
        | intro hn he =>
            subst x
            have hmem := Finset.mem_filter.mp hn
            have hnle : n <= N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hmem.1)
            apply Finset.mem_product.mpr
            exact And.intro (Finset.mem_range.mpr
              (Nat.lt_succ_of_le (Nat.div_le_div_right hnle))) hmem.2
  calc
    _ = (((Finset.range (N + 1)).filter
        fun n : Nat => Membership.mem R ((n : ZMod q) + z)).image f).card :=
      (Finset.card_image_of_injective _ hf).symm
    _ <= ((Finset.range (N / q + 1)).product R).card := Finset.card_le_card hsub
    _ = (Finset.range (N / q + 1)).card * R.card := Finset.card_product _ _
    _ = (N / q + 1) * R.card := by rw [Finset.card_range]

end ZMod

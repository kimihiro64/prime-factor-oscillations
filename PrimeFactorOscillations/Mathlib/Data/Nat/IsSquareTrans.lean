/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.Ring

/-!
# Transitivity of positive natural square classes

A positive middle factor can be cancelled from two square products.
Positivity is essential: a zero middle factor gives no such conclusion.
-/

set_option autoImplicit false
set_option Elab.async false

namespace Nat

theorem isSquare_mul_trans_of_pos {a b c : Nat} (hb : 0 < b)
    (hab : IsSquare (a * b)) (hbc : IsSquare (b * c)) : IsSquare (a * c) := by
  have hsq : IsSquare ((b * b) * (a * c)) := by
    convert hab.mul hbc using 1
    ring
  let r := Classical.choose hsq
  have hr : (b * b) * (a * c) = r * r := Classical.choose_spec hsq
  have hdiv : Dvd.dvd (b ^ 2) (r ^ 2) := by
    refine Exists.intro (a * c) ?_
    simpa only [pow_two] using hr.symm
  have hbr : Dvd.dvd b r :=
    (Nat.pow_dvd_pow_iff (by decide : Not ((2 : Nat) = 0))).mp hdiv
  let t := Classical.choose hbr
  have ht : r = b * t := Classical.choose_spec hbr
  refine Exists.intro t ?_
  have hmul : (b * b) * (a * c) = (b * b) * (t * t) := by
    rw [hr, ht]
    ring
  exact Nat.eq_of_mul_eq_mul_left (Nat.mul_pos hb hb) hmul

end Nat

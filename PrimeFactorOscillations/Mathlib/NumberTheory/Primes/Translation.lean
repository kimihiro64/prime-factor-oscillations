/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# No eventual positive prime translation

A positive additive period cannot preserve all sufficiently large primes.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace Nat

/-- An eventual positive translation cannot preserve all primes. -/
theorem no_eventual_positive_prime_period (N c : Nat) (hc : 0 < c)
    (hperiod : forall p : Nat, N <= p -> Nat.Prime p -> Nat.Prime (p + c)) :
    False := by
  let hex := Nat.exists_infinite_primes (max N 2)
  let p := Classical.choose hex
  have hpN : N <= p := (le_max_left N 2).trans (Classical.choose_spec hex).1
  have hp : Nat.Prime p := (Classical.choose_spec hex).2
  have hiter : forall k : Nat, Nat.Prime (p + k * c) := by
    intro k
    induction k with
    | zero => simpa using hp
    | succ k hk =>
      have h := hperiod (p + k * c) (by omega) hk
      convert h using 1 <;> ring
  have hlarge := hiter p
  have hd : Dvd.dvd p (p + p * c) := by
    exact Exists.intro (1 + c) (by ring)
  have he := (hlarge.dvd_iff_eq hp.ne_one).mp hd
  nlinarith [hp.pos]

end Nat

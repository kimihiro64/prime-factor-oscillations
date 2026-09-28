/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Prime.Defs

/-!
# Periodic blocks of composite integers

The offsets from 2 through L after every positive multiple of L! are
composite. Such a multiple occurs within L! integers of every starting point.
-/

namespace Nat

/-- An offset from 2 through L after a positive multiple of L! is composite. -/
theorem not_prime_mul_factorial_add {L n j : Nat}
    (hn : 0 < n) (hj : 2 <= j) (hjL : j <= L) :
    Not (Nat.Prime (n * Nat.factorial L + j)) := by
  intro hp
  have hfac : Dvd.dvd j (Nat.factorial L) := Nat.dvd_factorial (by omega) hjL
  have hdiv : Dvd.dvd j (n * Nat.factorial L + j) :=
    Nat.dvd_add (dvd_mul_of_dvd_right hfac n) (dvd_refl j)
  have hpos : 0 < n * Nat.factorial L := Nat.mul_pos hn (Nat.factorial_pos L)
  rcases hp.eq_one_or_self_of_dvd j hdiv with h | h <;> omega

/-- Every starting point has a nearby block of L-1 consecutive composites. -/
theorem exists_nearby_composite_block (x L : Nat) :
    exists a : Nat, x < a /\ a <= x + Nat.factorial L /\
      forall j : Nat, 2 <= j -> j <= L -> Not (Nat.Prime (a + j)) := by
  let W := Nat.factorial L
  have hW : 0 < W := Nat.factorial_pos L
  have hmod := Nat.mod_lt x hW
  have hdecomp : x % W + (x / W) * W = x := by
    simpa only [Nat.mul_comm] using Nat.mod_add_div x W
  refine Exists.intro ((x / W + 1) * W) (And.intro ?_ (And.intro ?_ ?_))
  next =>
    rw [Nat.add_mul, Nat.one_mul]
    omega
  next =>
    rw [Nat.add_mul, Nat.one_mul]
    change x / W * W + W <= x + W
    omega
  next =>
    intro j hj hjL
    exact not_prime_mul_factorial_add (n := x / W + 1)
      (Nat.succ_pos (x / W)) hj hjL

end Nat

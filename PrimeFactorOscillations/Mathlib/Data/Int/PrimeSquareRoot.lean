/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Algebra.Prime.Lemmas
import Mathlib.Data.Nat.Prime.Int
import Mathlib.Tactic.Ring.Basic

/-!
# Regular square roots modulo a prime square

If a prime does not divide twice a root, equality of squares modulo its square
forces equality up to sign. The unit hypothesis is essential: singular roots
must be counted separately in squarefree sieving.
-/

set_option autoImplicit false

namespace Int

/-- A regular root modulo an odd prime square has only the two signs. -/
theorem prime_sq_dvd_sq_sub_sq_iff {p x a : Int} (hp : _root_.Prime p)
    (hregular : Not (Dvd.dvd p (2 * a))) :
    Iff (Dvd.dvd (p ^ 2) (x ^ 2 - a ^ 2))
      (Or (Dvd.dvd (p ^ 2) (x - a)) (Dvd.dvd (p ^ 2) (x + a))) := by
  have hfactor : x ^ 2 - a ^ 2 = (x - a) * (x + a) := by ring1
  constructor
  case mp =>
    intro h
    rw [hfactor] at h
    by_cases hminus : Dvd.dvd p (x - a)
    case pos =>
      have hplus : Not (Dvd.dvd p (x + a)) := by
        intro hplus
        apply hregular
        have hid : 2 * a = (x + a) - (x - a) := by ring1
        rw [hid]
        cases hplus with
        | intro u hu =>
            cases hminus with
            | intro v hv =>
                refine Exists.intro (u - v) ?_
                rw [mul_sub, <- hu, <- hv]
      exact Or.inl (hp.pow_dvd_of_dvd_mul_right 2 hplus h)
    case neg =>
      exact Or.inr (hp.pow_dvd_of_dvd_mul_left 2 hminus h)
  case mpr =>
    intro h
    rw [hfactor]
    cases h with
    | inl h => exact dvd_mul_of_dvd_left h
    | inr h => exact dvd_mul_of_dvd_right h

/-- The regularity condition follows from an odd natural prime and a unit root. -/
theorem nat_prime_sq_dvd_sq_sub_sq_iff {p : Nat} {x a : Int} (hp : Nat.Prime p)
    (htwo : Not (p = 2)) (hunit : Not (Dvd.dvd (p : Int) a)) :
    Iff (Dvd.dvd ((p : Int) ^ 2) (x ^ 2 - a ^ 2))
      (Or (Dvd.dvd ((p : Int) ^ 2) (x - a))
        (Dvd.dvd ((p : Int) ^ 2) (x + a))) := by
  have hpint : _root_.Prime (p : Int) := Nat.prime_iff_prime_int.mp hp
  apply prime_sq_dvd_sq_sub_sq_iff hpint
  intro h
  cases hpint.dvd_or_dvd h with
  | inl h =>
      have hn : Dvd.dvd p 2 := Int.natCast_dvd_natCast.mp h
      exact htwo ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hn)
  | inr h => exact hunit h

end Int

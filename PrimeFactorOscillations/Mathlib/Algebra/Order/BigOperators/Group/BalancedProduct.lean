/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Card

/-!
# A large subset with a small product

Partition a finite set into two halves by cardinality and choose the half with
the smaller product. Applied to distinct prime factors, this gives a divisor
below the square root that retains at least half the prime factors. It is the
finite compression step in divisor-moment bounds.
-/

set_option autoImplicit false

namespace Finset

/-- A subset retains at least half the factors while its product is at most
the square root of the full product. Natural weights may include zero. -/
theorem exists_subset_sq_prod_le_and_card {I : Type*}
    (s : Finset I) (w : I -> Nat) :
    Exists (fun t : Finset I => And (t <= s)
      (And ((t.prod w) ^ 2 <= s.prod w) (s.card <= 2 * t.card + 1))) := by
  classical
  have hn : s.card / 2 <= s.card := Nat.div_le_self s.card 2
  cases exists_subset_card_eq hn with
  | intro t ht =>
    cases ht with
    | intro hts hcard =>
      have hprod : (s \ t).prod w * t.prod w = s.prod w := prod_sdiff hts
      have hcardc : (s \ t).card = s.card - t.card := card_sdiff_of_subset hts
      by_cases hle : t.prod w <= (s \ t).prod w
      case pos =>
        refine Exists.intro t (And.intro hts (And.intro ?_ ?_))
        case refine_1 =>
          rw [pow_two]
          exact (Nat.mul_le_mul_right (t.prod w) hle).trans_eq hprod
        case refine_2 => omega
      case neg =>
        refine Exists.intro (s \ t) (And.intro sdiff_subset (And.intro ?_ ?_))
        case refine_1 =>
          have hrev : (s \ t).prod w <= t.prod w := Nat.le_of_lt (Nat.lt_of_not_ge hle)
          rw [pow_two]
          exact (Nat.mul_le_mul_left ((s \ t).prod w) hrev).trans_eq hprod
        case refine_2 => omega

end Finset

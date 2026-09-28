import Mathlib.Data.Fintype.Card
import PrimeFactorOscillations.Definitions.Reversals

set_option autoImplicit false

/-!
# Finite reversal counts from tail decrease

An eventual nonincreasing tail rules out every later ascent. Strictly separated
witnesses have distinct ascent indices, so an injection into the initial
segment bounds their number. This discharges the combinatorial finiteness step
in the upper-bound branch without assuming a maximum exists.
-/

namespace PrimeFactorOscillations

variable {R : Type*} [Preorder R]

/-- An empty family always supplies zero reversal witnesses. -/
theorem hasAtLeastReversals_zero (f : Nat -> R) : HasAtLeastReversals f 0 := by
  refine Exists.intro Fin.elim0 (Exists.intro Fin.elim0 ?_)
  constructor
  all_goals intro i; exact Fin.elim0 i

/-- A nonincreasing tail starting at T bounds every separated family by T. -/
theorem reversal_count_le_of_nonincreasing_tail (f : Nat -> R) (T m : Nat)
    (htail : forall i, T <= i -> f (i + 1) <= f i)
    (hm : HasAtLeastReversals f m) : m <= T := by
  choose descent ascent h using hm
  have hlt : forall j, ascent j < T := by
    intro j
    exact lt_of_not_ge (fun hge => not_lt_of_ge (htail _ hge) (h.1 j).2.2)
  have hmono : StrictMono ascent := by
    intro i j hij
    exact lt_trans (Nat.lt_succ_self _) (lt_trans (h.2 i j hij) (h.1 j).1)
  let into : Fin m -> Fin T := fun j => Fin.mk (ascent j) (hlt j)
  have hinj : Function.Injective into := by
    intro i j heq
    exact hmono.injective (congrArg Fin.val heq)
  simpa only [Fintype.card_fin] using Fintype.card_le_of_injective into hinj

end PrimeFactorOscillations

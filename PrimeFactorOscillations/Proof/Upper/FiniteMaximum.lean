import Mathlib.Data.Nat.Find
import PrimeFactorOscillations.Definitions.Targets
import PrimeFactorOscillations.Helpers.ReversalCount

set_option autoImplicit false

/-!
# Existence of the reversal number

This proves the finite-maximum obligation in the headline statement from an
eventually nonincreasing tail. The remaining upper-bound input is an actual
uniform tail estimate for the named density families, not a counting convention.
-/

namespace PrimeFactorOscillations

variable {R : Type*} [Preorder R]

/-- Every eventually nonincreasing sequence has an attained finite reversal count. -/
theorem exists_reversalNumber_of_tail (f : Nat -> R) (T : Nat)
    (htail : forall i, T <= i -> f (i + 1) <= f i) :
    exists N : Nat, HasReversalNumber f N /\ N <= T := by
  classical
  let P : Nat -> Prop := HasAtLeastReversals f
  let N := Nat.findGreatest P T
  have hN : P N := Nat.findGreatest_spec (Nat.zero_le T) (hasAtLeastReversals_zero f)
  refine Exists.intro N (And.intro ?_ (Nat.findGreatest_le T))
  refine And.intro hN ?_
  intro m hm
  exact Nat.le_findGreatest (reversal_count_le_of_nonincreasing_tail f T m htail hm) hm

/-- The attained maximal count is unique, so it defines N(k) without ambiguity. -/
theorem reversalNumber_unique (f : Nat -> R) (N M : Nat)
    (hN : HasReversalNumber f N) (hM : HasReversalNumber f M) : N = M := by
  exact Nat.le_antisymm (hM.2 N hN.1) (hN.2 M hM.1)

end PrimeFactorOscillations

import Mathlib.Tactic.Ring
import PrimeFactorOscillations.Definitions.Reversals

set_option autoImplicit false

/-!
# Permutation invariance of the exact local mass

The Bernoulli recursion is symmetric for arbitrary rational local laws,
including probabilities zero or one. This transports a sorted next-prime
prefix to the cons list used by the exact first-difference criterion.
-/

namespace PrimeFactorOscillations

/-- Reordering the finite prime events leaves every mass coefficient unchanged. -/
theorem finiteLocalMass_perm (eta : Nat -> Rat) (xs ys : List Nat)
    (h : xs.Perm ys) (r : Nat) :
    finiteLocalMass eta xs r = finiteLocalMass eta ys r := by
  induction h generalizing r with
  | nil => rfl
  | cons a h ih =>
      cases r with
      | zero => simp only [finiteLocalMass, ih 0]
      | succ r => simp only [finiteLocalMass, ih r, ih (r + 1)]
  | swap a b entries =>
      cases r with
      | zero => simp only [finiteLocalMass]; ring
      | succ r =>
          cases r with
          | zero => simp only [finiteLocalMass]; ring
          | succ r => simp only [finiteLocalMass]; ring
  | trans h1 h2 ih1 ih2 => exact (ih1 r).trans (ih2 r)

end PrimeFactorOscillations

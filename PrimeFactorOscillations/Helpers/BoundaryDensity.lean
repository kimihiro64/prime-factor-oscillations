import PrimeFactorOscillations.Helpers.OrdinaryLocalLawBridge

/-! # The public fold formula for finite local masses -/

set_option autoImplicit false

namespace PrimeFactorOscillations

/-- The recursive mass equals a fold written entirely with Mathlib primitives. -/
theorem finiteLocalMass_eq_foldr (eta : Nat -> Rat) (xs : List Nat) (r : Nat) :
    finiteLocalMass eta xs r =
      xs.foldr
        (fun ell (f : Nat -> Rat) => Nat.rec ((1 - eta ell) * f 0)
          (fun j _ => (1 - eta ell) * f (j + 1) + eta ell * f j))
        (Nat.rec (1 : Rat) (fun _ _ => 0)) r := by
  induction xs generalizing r with
  | nil => cases r <;> rfl
  | cons p xs ih =>
      cases r with
      | zero =>
          simp only [finiteLocalMass, List.foldr_cons]
          rw [ih]
          rfl
      | succ r =>
          simp only [finiteLocalMass, List.foldr_cons]
          rw [ih, ih]

/-- The canonical rank density in the exact public primitive vocabulary. -/
theorem localRankDensity_eq_public (eta : Nat -> Rat) (k i : Nat) :
    localRankDensity eta k i =
      eta (Nat.nth Nat.Prime i) *
        ((Finset.filter Nat.Prime (Finset.range (Nat.nth Nat.Prime i))).sort
          (fun a b => a <= b)).foldr
            (fun ell (f : Nat -> Rat) => Nat.rec ((1 - eta ell) * f 0)
              (fun j _ => (1 - eta ell) * f (j + 1) + eta ell * f j))
            (Nat.rec (1 : Rat) (fun _ _ => 0)) (k - 1) := by
  rw [localRankDensity, finiteLocalMass_eq_foldr]
  rfl

end PrimeFactorOscillations

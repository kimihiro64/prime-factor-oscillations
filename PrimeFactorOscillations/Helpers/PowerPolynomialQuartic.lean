/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.PowerPolynomialLaw

/-!
# Quartic probability comparisons and exact forced-prime classification

For prime inputs x^4+1 forces p=2, while x^4-1 forces p=2,3,5.
Every other local event remains in the nonconstant arithmetic clock.
-/


set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.PowerPolynomialLaw

def primeTwo : Nat.Primes := Subtype.mk 2 (by decide)
def primeThree : Nat.Primes := Subtype.mk 3 (by decide)
def primeFive : Nat.Primes := Subtype.mk 5 (by decide)

theorem quartic_unitRootCounts_small :
    unitRootCount 4 (-1) primeTwo = 1 /\
    unitRootCount 4 (-1) primeThree = 0 /\
    unitRootCount 4 (-1) primeFive = 0 /\
    unitRootCount 4 1 primeTwo = 1 /\
    unitRootCount 4 1 primeThree = 2 /\
    unitRootCount 4 1 primeFive = 4 := by
  decide

theorem quartic_not_forced_of_seven_le (a : Int) (p : Nat.Primes)
    (hp : 7 <= (p : Nat)) :
    unitRootCount 4 a p < (p : Nat) - 1 := by
  have h := unitRootCount_le_degree 4 a (by decide) p
  omega

theorem prime_lt_seven_cases (p : Nat.Primes) (hp : (p : Nat) < 7) :
    p = primeTwo \/ p = primeThree \/ p = primeFive := by
  have h2 := p.property.two_le
  have h4 : Not ((p : Nat) = 4) := by
    intro h
    have hPrime := p.property
    rw [h] at hPrime
    exact (by decide : Not (Nat.Prime 4)) hPrime
  have h6 : Not ((p : Nat) = 6) := by
    intro h
    have hPrime := p.property
    rw [h] at hPrime
    exact (by decide : Not (Nat.Prime 6)) hPrime
  have hCases : (p : Nat) = 2 \/ (p : Nat) = 3 \/ (p : Nat) = 5 := by omega
  rcases hCases with h | h | h
  . exact Or.inl (Subtype.ext h)
  . exact Or.inr (Or.inl (Subtype.ext h))
  . exact Or.inr (Or.inr (Subtype.ext h))

theorem quartic_plus_forced_iff (p : Nat.Primes) :
    unitRootCount 4 (-1) p = (p : Nat) - 1 <-> p = primeTwo := by
  by_cases hp : 7 <= (p : Nat)
  . have hlt := quartic_not_forced_of_seven_le (-1) p hp
    have hne : Not (p = primeTwo) := by
      intro h
      subst p
      norm_num [primeTwo] at hp
    exact iff_of_false (Nat.ne_of_lt hlt) hne
  . have hsmall := prime_lt_seven_cases p (by omega)
    rcases hsmall with h | h | h
    . subst p
      refine iff_of_true ?_ rfl
      change unitRootCount 4 (-1) primeTwo = 1
      exact quartic_unitRootCounts_small.1
    . subst p
      have hFalse : Not (unitRootCount 4 (-1) primeThree = (primeThree : Nat) - 1) := by
        rw [quartic_unitRootCounts_small.2.1]
        decide
      have hNe : Not (primeThree = primeTwo) := by
        intro h
        have hv := congrArg (fun p : Nat.Primes => (p : Nat)) h
        change (3 : Nat) = 2 at hv
        omega
      exact iff_of_false hFalse hNe
    . subst p
      have hFalse : Not (unitRootCount 4 (-1) primeFive = (primeFive : Nat) - 1) := by
        rw [quartic_unitRootCounts_small.2.2.1]
        decide
      have hNe : Not (primeFive = primeTwo) := by
        intro h
        have hv := congrArg (fun p : Nat.Primes => (p : Nat)) h
        change (5 : Nat) = 2 at hv
        omega
      exact iff_of_false hFalse hNe

theorem quartic_minus_forced_iff (p : Nat.Primes) :
    unitRootCount 4 1 p = (p : Nat) - 1 <->
      p = primeTwo \/ p = primeThree \/ p = primeFive := by
  by_cases hp : 7 <= (p : Nat)
  . have hlt := quartic_not_forced_of_seven_le 1 p hp
    have hne : Not (p = primeTwo \/ p = primeThree \/ p = primeFive) := by
      intro h
      rcases h with h | h | h
      all_goals subst p
      all_goals norm_num [primeTwo, primeThree, primeFive] at hp
    exact iff_of_false (Nat.ne_of_lt hlt) hne
  . have hsmall := prime_lt_seven_cases p (by omega)
    refine iff_of_true ?_ hsmall
    rcases hsmall with h | h | h
    . subst p
      rw [quartic_unitRootCounts_small.2.2.2.1]
      rfl
    . subst p
      rw [quartic_unitRootCounts_small.2.2.2.2.1]
      rfl
    . subst p
      rw [quartic_unitRootCounts_small.2.2.2.2.2]
      rfl

theorem quartic_plus_comparison (b : Real) (hb : 0 < b) :
    ComparisonClaim (primeLaw 4 (-1) (by decide)) b :=
  primeLaw_comparison 4 (-1) (by decide) b hb

theorem quartic_minus_comparison (b : Real) (hb : 0 < b) :
    ComparisonClaim (primeLaw 4 1 (by decide)) b :=
  primeLaw_comparison 4 1 (by decide) b hb

end PrimeFactorOscillations.PowerPolynomialLaw

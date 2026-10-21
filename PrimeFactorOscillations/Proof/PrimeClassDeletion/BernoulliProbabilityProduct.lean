/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Mathlib.Probability.Distributions.FiniteBernoulliPatterns
import PrimeFactorOscillations.Proof.PrimeClassDeletion.BernoulliExpectations

/-! # Exact finite independent-Bernoulli generating product

The coefficient law is identified with the literal product of the one-coordinate
generating polynomials. Nonnegativity and normalization include forced and
excluded coordinates.
-/

set_option autoImplicit false
set_option Elab.async false

namespace List

noncomputable def bernoulliProbabilityProduct (s : List Real) : Polynomial Real :=
  (s.map (fun a => Polynomial.C (1 - a) + Polynomial.C a * Polynomial.X)).prod

theorem bernoulliProbabilityProduct_coeff (s : List Real) (r : Nat) :
    (bernoulliProbabilityProduct s).coeff r = bernoulliMass s r := by
  simpa only [bernoulliProbabilityProduct, add_comm] using
    (bernoulliMass_eq_coeff_product s r).symm

theorem bernoulliProbabilityProduct_coeff_nonneg (s : List Real)
    (hs : forall a, List.Mem a s -> And (0 <= a) (a <= 1)) (r : Nat) :
    0 <= (bernoulliProbabilityProduct s).coeff r := by
  rw [bernoulliProbabilityProduct_coeff]
  exact bernoulliMass_nonneg s hs r

theorem bernoulliProbabilityProduct_coeff_sum (s : List Real) :
    (Finset.range (s.length + 1)).sum
      (fun r => (bernoulliProbabilityProduct s).coeff r) = 1 := by
  simp only [bernoulliProbabilityProduct_coeff, sum_bernoulliMass]

theorem bernoulliProbabilityProduct_coeff_eq_zero (s : List Real) (r : Nat)
    (hr : s.length < r) : (bernoulliProbabilityProduct s).coeff r = 0 := by
  rw [bernoulliProbabilityProduct_coeff]
  exact bernoulliMass_eq_zero_of_length_lt s r hr

end List

/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Proof.PrimeClassDeletion.BernoulliFiniteObservables

/-! # The finite tail indicator and the sampling-error consumer

Every sum retains the full finite support. The absolute estimate concerns
only a separate empirical coefficient error, not a signed arithmetic main term.
-/

set_option autoImplicit false
set_option Elab.async false

namespace List

theorem bernoulliExpectation_tailIndicator (s : List Real) (r : Nat) :
    bernoulliExpectation s (fun k => if r <= k then 1 else 0) = bernoulliTail s r := by
  classical
  rw [<- bernoulliOutcomeExpectation_eq, <- bernoulliOutcomeTail_eq]
  unfold bernoulliOutcomeTail
  apply Finset.sum_congr rfl
  intro w hw
  by_cases h : r <= bernoulliOutcomeCount w
  all_goals simp only [h, ite_true, ite_false, one_mul, zero_mul]

theorem bernoulliTail_eq_finite_sum (s : List Real) (r : Nat) :
    bernoulliTail s r = (Finset.range (s.length + 1)).sum
      (fun k => if r <= k then bernoulliMass s k else 0) := by
  rw [<- bernoulliExpectation_tailIndicator, bernoulliExpectation]
  apply Finset.sum_congr rfl
  intro k hk
  by_cases h : r <= k
  all_goals simp only [h, ite_true, ite_false, one_mul, zero_mul]

theorem abs_bernoulliTail_perturbation_le (s : List Real) (f : Nat -> Real) (r : Nat) :
    abs ((Finset.range (s.length + 1)).sum (fun k => if r <= k then f k else 0) -
      bernoulliTail s r) <=
        (Finset.range (s.length + 1)).sum (fun k => abs (f k - bernoulliMass s k)) := by
  classical
  rw [bernoulliTail_eq_finite_sum, <- Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  apply Finset.sum_le_sum
  intro k hk
  by_cases h : r <= k
  case pos => simp only [h, ite_true, le_refl]
  case neg =>
    simp only [h, ite_false, sub_self, abs_zero]
    exact abs_nonneg _

end List

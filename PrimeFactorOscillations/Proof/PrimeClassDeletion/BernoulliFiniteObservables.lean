/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Proof.PrimeClassDeletion.BernoulliFiniteLaw

/-! # Tails and expectations on the finite independent-bit probability space -/

set_option autoImplicit false
set_option Elab.async false

namespace List

theorem bernoulliOutcomeCount_le {n : Nat} (w : BernoulliOutcomes n) :
    bernoulliOutcomeCount w <= n := by
  induction n with
  | zero => exact Nat.le_refl 0
  | succ n ih =>
      have ht := ih w.2
      change (if w.1 then 1 else 0) + bernoulliOutcomeCount w.2 <= n + 1
      split_ifs <;> omega

theorem bernoulliOutcomeExpectation_eq (s : List Real) (phi : Nat -> Real) :
    (Finset.univ.sum (fun w : BernoulliOutcomes s.length =>
      phi (bernoulliOutcomeCount w) * bernoulliOutcomeWeight s w)) =
        bernoulliExpectation s phi := by
  classical
  rw [bernoulliExpectation]
  simp_rw [<- bernoulliOutcomeMass_eq]
  simp only [bernoulliOutcomeMass, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro w hw
  rw [Finset.sum_eq_single (bernoulliOutcomeCount w)]
  next => simp
  next =>
    intro k hk hne
    simp only [Ne.symm hne, ite_false, mul_zero]
  next =>
    intro hnot
    exact False.elim (hnot (Finset.mem_range.mpr
      (Nat.lt_succ_of_le (bernoulliOutcomeCount_le w))))

noncomputable def bernoulliOutcomeTail (s : List Real) (r : Nat) : Real :=
  Finset.univ.sum (fun w : BernoulliOutcomes s.length =>
    if r <= bernoulliOutcomeCount w then bernoulliOutcomeWeight s w else 0)

theorem bernoulliOutcomeTail_eq (s : List Real) (r : Nat) :
    bernoulliOutcomeTail s r = bernoulliTail s r := by
  classical
  induction s generalizing r with
  | nil =>
      change ((Finset.univ : Finset Unit).sum
        (fun _ => if r <= 0 then (1 : Real) else 0)) = bernoulliTail [] r
      cases r <;> simp [bernoulliTail]
  | cons a s ih =>
      cases r with
      | zero =>
          change (Finset.univ.sum (fun w : BernoulliOutcomes (a :: s).length =>
            if 0 <= bernoulliOutcomeCount w then bernoulliOutcomeWeight (a :: s) w
              else 0)) = 1
          simp only [Nat.zero_le, ite_true]
          exact bernoulliOutcomeWeight_sum (a :: s)
      | succ r =>
          have hscale (c : Real) (k : Nat) :
              (Finset.univ.sum (fun w : BernoulliOutcomes s.length =>
                if k <= bernoulliOutcomeCount w then c * bernoulliOutcomeWeight s w
                  else 0)) = c * bernoulliOutcomeTail s k := by
            rw [bernoulliOutcomeTail, Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro w hw
            by_cases h : k <= bernoulliOutcomeCount w
            all_goals simp only [h, ite_true, ite_false, mul_zero]
          change (Finset.univ.sum (fun w : Prod Bool (BernoulliOutcomes s.length) =>
            if r + 1 <= bernoulliOutcomeCount (n := s.length + 1) w then
              bernoulliOutcomeWeight (a :: s) w else 0)) = _
          simp only [Fintype.sum_prod_type, Fintype.sum_bool, bernoulliOutcomeCount,
            bernoulliOutcomeWeight, Bool.false_eq_true, ite_false, zero_add,
            ite_true, Nat.one_add, Nat.succ_le_succ_iff]
          rw [hscale, hscale, ih, ih, bernoulliTail]
          ring

end List

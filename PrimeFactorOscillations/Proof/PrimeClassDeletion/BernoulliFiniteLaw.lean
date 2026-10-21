/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Proof.PrimeClassDeletion.BernoulliExpectations

/-! # The actual finite product probability space

An outcome is a tuple of independent bits. Its weight is the product of the
chosen success or failure weights. The success-count law is exactly the
existing Bernoulli coefficient law, including zero and one coordinates.
-/

set_option autoImplicit false
set_option Elab.async false

namespace List

def BernoulliOutcomes : Nat -> Type
  | 0 => Unit
  | n + 1 => Prod Bool (BernoulliOutcomes n)

instance bernoulliOutcomesFintype (n : Nat) : Fintype (BernoulliOutcomes n) := by
  induction n with
  | zero => exact inferInstanceAs (Fintype Unit)
  | succ n ih =>
      letI := ih
      exact inferInstanceAs (Fintype (Prod Bool (BernoulliOutcomes n)))

def bernoulliOutcomeCount : {n : Nat} -> BernoulliOutcomes n -> Nat
  | 0, _ => 0
  | _ + 1, w => (if w.1 then 1 else 0) + bernoulliOutcomeCount w.2

noncomputable def bernoulliOutcomeWeight :
    (s : List Real) -> BernoulliOutcomes s.length -> Real
  | [], _ => 1
  | a :: s, w => (if w.1 then a else 1 - a) * bernoulliOutcomeWeight s w.2

noncomputable def bernoulliOutcomeMass (s : List Real) (r : Nat) : Real :=
  Finset.univ.sum (fun w : BernoulliOutcomes s.length =>
    if bernoulliOutcomeCount w = r then bernoulliOutcomeWeight s w else 0)

theorem bernoulliOutcomeMass_eq (s : List Real) (r : Nat) :
    bernoulliOutcomeMass s r = bernoulliMass s r := by
  classical
  induction s generalizing r with
  | nil =>
      change ((Finset.univ : Finset Unit).sum
        (fun _ => if 0 = r then (1 : Real) else 0)) = bernoulliMass [] r
      cases r <;> simp [bernoulliMass]
  | cons a s ih =>
      have hscale (c : Real) (k : Nat) :
          (Finset.univ.sum (fun w : BernoulliOutcomes s.length =>
            if bernoulliOutcomeCount w = k then c * bernoulliOutcomeWeight s w else 0)) =
              c * bernoulliOutcomeMass s k := by
        rw [bernoulliOutcomeMass, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro w hw
        by_cases h : bernoulliOutcomeCount w = k
        all_goals simp only [h, ite_true, ite_false, mul_zero]
      cases r with
      | zero =>
          change (Finset.univ.sum (fun w : Prod Bool (BernoulliOutcomes s.length) =>
            if bernoulliOutcomeCount (n := s.length + 1) w = 0 then
              bernoulliOutcomeWeight (a :: s) w else 0)) = _
          simp only [Fintype.sum_prod_type, Fintype.sum_bool, bernoulliOutcomeCount,
            bernoulliOutcomeWeight, Bool.false_eq_true, ite_false, zero_add,
            ite_true, Nat.one_add, Nat.succ_ne_zero]
          simp only [Finset.sum_const_zero, zero_add, hscale, bernoulliMass, ih]
      | succ r =>
          change (Finset.univ.sum (fun w : Prod Bool (BernoulliOutcomes s.length) =>
            if bernoulliOutcomeCount (n := s.length + 1) w = r + 1 then
              bernoulliOutcomeWeight (a :: s) w
              else 0)) = _
          simp only [Fintype.sum_prod_type, Fintype.sum_bool, bernoulliOutcomeCount,
            bernoulliOutcomeWeight, Bool.false_eq_true, ite_false, zero_add,
            ite_true, Nat.one_add, Nat.succ.injEq]
          rw [hscale, hscale, bernoulliMass, ih, ih]
          ring

theorem bernoulliOutcomeWeight_nonneg (s : List Real)
    (hs : forall a, List.Mem a s -> And (0 <= a) (a <= 1))
    (w : BernoulliOutcomes s.length) : 0 <= bernoulliOutcomeWeight s w := by
  induction s with
  | nil => exact zero_le_one
  | cons a s ih =>
      have ha := hs a (List.Mem.head _)
      have ht : forall b, List.Mem b s -> And (0 <= b) (b <= 1) :=
        fun b hb => hs b (List.Mem.tail _ hb)
      change 0 <= (if w.1 then a else 1 - a) * bernoulliOutcomeWeight s w.2
      apply mul_nonneg
      next => exact ite_nonneg ha.1 (sub_nonneg.mpr ha.2)
      next => exact ih ht w.2

theorem bernoulliOutcomeWeight_sum (s : List Real) :
    (Finset.univ.sum (fun w : BernoulliOutcomes s.length => bernoulliOutcomeWeight s w)) =
      1 := by
  induction s with
  | nil =>
      change ((Finset.univ : Finset Unit).sum (fun _ => (1 : Real))) = 1
      simp
  | cons a s ih =>
      change (Finset.univ.sum (fun w : Prod Bool (BernoulliOutcomes s.length) =>
        bernoulliOutcomeWeight (a :: s) w)) = 1
      simp only [Fintype.sum_prod_type, Fintype.sum_bool, bernoulliOutcomeWeight,
        Bool.false_eq_true, ite_false, ite_true, <- Finset.mul_sum, ih]
      ring

end List

/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Mathlib.Probability.Distributions.FiniteBernoulliComparison

/-! # Exact finite Bernoulli stochastic order

The tail recurrence is identified with the complement of the existing
coefficient cumulative sum. Coordinate replacement preserves its exact
signed increment, and zero padding permits comparison of different lengths.
-/

set_option autoImplicit false
set_option Elab.async false

namespace List

/-- Coordinatewise order on equally long probability arrays. -/
inductive BernoulliCoordinateLE : List Real -> List Real -> Prop
  | nil : BernoulliCoordinateLE [] []
  | cons {a b : Real} {s t : List Real} (hab : a <= b)
      (hst : BernoulliCoordinateLE s t) :
      BernoulliCoordinateLE (a :: s) (b :: t)

noncomputable def bernoulliTail : List Real -> Nat -> Real
  | _, 0 => 1
  | [], _ + 1 => 0
  | a :: s, r + 1 =>
      (1 - a) * bernoulliTail s (r + 1) + a * bernoulliTail s r

theorem bernoulliTail_sub_succ (s : List Real) (r : Nat) :
    bernoulliTail s r - bernoulliTail s (r + 1) = bernoulliMass s r := by
  induction s generalizing r with
  | nil => cases r <;> simp [bernoulliTail, bernoulliMass]
  | cons a s ih =>
      cases r with
      | zero =>
          change 1 - ((1 - a) * bernoulliTail s 1 + a * bernoulliTail s 0) =
            (1 - a) * bernoulliMass s 0
          rw [<- ih 0]
          simp only [bernoulliTail]
          ring
      | succ r =>
          change
            ((1 - a) * bernoulliTail s (r + 1) + a * bernoulliTail s r) -
              ((1 - a) * bernoulliTail s (r + 2) +
                a * bernoulliTail s (r + 1)) =
            (1 - a) * bernoulliMass s (r + 1) + a * bernoulliMass s r
          rw [<- ih (r + 1), <- ih r]
          ring

/-- This identifies the tail with the established finite coefficients,
rather than introducing an unrelated probability model. -/
theorem bernoulliTail_eq_one_sub_sum_range (s : List Real) (r : Nat) :
    bernoulliTail s r =
      1 - (Finset.range r).sum (fun k => bernoulliMass s k) := by
  induction r with
  | zero => simp [bernoulliTail]
  | succ r ih =>
      rw [Finset.sum_range_succ]
      have hd := bernoulliTail_sub_succ s r
      linarith only [ih, hd]

/-- The exact signed tail response to one coordinate change. -/
theorem bernoulliTail_cons_difference (s : List Real) (a b : Real) (r : Nat) :
    bernoulliTail (b :: s) (r + 1) - bernoulliTail (a :: s) (r + 1) =
      (b - a) * bernoulliMass s r := by
  change
    ((1 - b) * bernoulliTail s (r + 1) + b * bernoulliTail s r) -
      ((1 - a) * bernoulliTail s (r + 1) + a * bernoulliTail s r) =
        (b - a) * bernoulliMass s r
  rw [<- bernoulliTail_sub_succ s r]
  ring

theorem bernoulliTail_mono (s t : List Real)
    (hst : BernoulliCoordinateLE s t)
    (hsunit : forall a, List.Mem a s -> 0 <= a /\ a <= 1)
    (htunit : forall b, List.Mem b t -> 0 <= b /\ b <= 1)
    (r : Nat) :
    bernoulliTail s r <= bernoulliTail t r := by
  revert hsunit htunit
  induction hst generalizing r with
  | nil =>
      intro hsunit htunit
      exact le_rfl
  | @cons a b s t hab hst ih =>
      intro hsunit htunit
      have ha := hsunit a (List.Mem.head _)
      have hs : forall c, List.Mem c s -> 0 <= c /\ c <= 1 :=
        fun c hc => hsunit c (List.Mem.tail _ hc)
      have ht : forall c, List.Mem c t -> 0 <= c /\ c <= 1 :=
        fun c hc => htunit c (List.Mem.tail _ hc)
      cases r with
      | zero => simp [bernoulliTail]
      | succ r =>
          have hlo := ih r hs ht
          have hhi := ih (r + 1) hs ht
          have hfirst :
              bernoulliTail (a :: s) (r + 1) <=
                bernoulliTail (a :: t) (r + 1) := by
            exact add_le_add
              (mul_le_mul_of_nonneg_left hhi (sub_nonneg.mpr ha.2))
              (mul_le_mul_of_nonneg_left hlo ha.1)
          have hmass := bernoulliMass_nonneg t ht r
          have hresponse := bernoulliTail_cons_difference t a b r
          have hnonneg := mul_nonneg (sub_nonneg.mpr hab) hmass
          exact hfirst.trans (by linarith only [hresponse, hnonneg])

theorem bernoulliTail_replicate_zero (n r : Nat) :
    bernoulliTail (List.replicate n (0 : Real)) r =
      bernoulliTail ([] : List Real) r := by
  induction n generalizing r with
  | zero => rfl
  | succ n ih =>
      cases r with
      | zero => simp [bernoulliTail]
      | succ r => simp [List.replicate_succ, bernoulliTail, ih]

theorem bernoulliTail_append_zeros (s : List Real) (n r : Nat) :
    bernoulliTail (s ++ List.replicate n (0 : Real)) r = bernoulliTail s r := by
  induction s generalizing r with
  | nil => simpa using bernoulliTail_replicate_zero n r
  | cons a s ih =>
      cases r with
      | zero => simp [bernoulliTail]
      | succ r => simp [bernoulliTail, ih]

/-- Coordinate order after zero padding implies stochastic dominance,
including all deterministic endpoint coordinates and all ranks. -/
theorem bernoulliTail_mono_padded (s t : List Real) (n r : Nat)
    (hst : BernoulliCoordinateLE (s ++ List.replicate n (0 : Real)) t)
    (hsunit : forall a, List.Mem a s -> 0 <= a /\ a <= 1)
    (htunit : forall b, List.Mem b t -> 0 <= b /\ b <= 1) :
    bernoulliTail s r <= bernoulliTail t r := by
  have hp : forall a, List.Mem a (s ++ List.replicate n (0 : Real)) ->
      0 <= a /\ a <= 1 := by
    intro a ha
    cases List.mem_append.mp ha with
    | inl hs => exact hsunit a hs
    | inr hz =>
        have hzero : a = 0 := (List.mem_replicate.mp hz).2
        subst a
        exact And.intro (le_refl _) zero_le_one
  have h := bernoulliTail_mono _ _ hst hp htunit r
  simpa only [bernoulliTail_append_zeros] using h

end List

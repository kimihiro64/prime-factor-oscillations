/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import Mathlib.Algebra.Order.Field.Basic
import PrimeFactorOscillations.Mathlib.Probability.Distributions.FiniteBernoulliMass

/-! # Exact removal of excluded and forced Bernoulli coordinates -/

set_option autoImplicit false
set_option Elab.async false

namespace List

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]

/-- Retain exactly the genuinely random coordinates of a finite probability list. -/
def bernoulliInterior (s : List R) : List R :=
  s.filter (fun a => decide (0 < a /\ a < 1))

private theorem erased_eq_interior (s : List R)
    (hs : forall a, List.Mem a s -> 0 <= a /\ a <= 1) :
    (s.filter (fun a => decide (Not (a = 1)))).filter (fun a => decide (Not (a = 0))) =
      bernoulliInterior s := by
  induction s with
  | nil => rfl
  | cons a s ih =>
      have ha := hs a (List.Mem.head _)
      have ht : forall b, List.Mem b s -> 0 <= b /\ b <= 1 :=
        fun b hb => hs b (List.Mem.tail _ hb)
      by_cases hz : a = 0
      next =>
        subst a
        simpa [bernoulliInterior] using ih ht
      next =>
        by_cases ho : a = 1
        next =>
          subst a
          simpa [bernoulliInterior] using ih ht
        next =>
          have hpos : 0 < a := by
            by_contra hn
            exact hz (le_antisymm (le_of_not_gt hn) ha.1)
          have hlt : a < 1 := by
            by_contra hn
            exact ho (le_antisymm ha.2 (le_of_not_gt hn))
          simpa [bernoulliInterior, hz, ho, hpos, hlt] using
            congrArg (List.cons a) (ih ht)

omit [IsStrictOrderedRing R] in
/-- Every retained probability is interior; this fact comes from the exact
filter, with no monotonicity assumption on the original list. -/
theorem bernoulliInterior_mem (s : List R) :
    forall a, List.Mem a (bernoulliInterior s) -> 0 < a /\ a < 1 := by
  intro a ha
  have h := (List.mem_filter.mp ha).2
  simpa only [decide_eq_true_eq] using h

/-- The original finite mass is exactly the interior mass after subtracting
the number of forced coordinates; excluded coordinates cause no rank shift. -/
theorem bernoulliMass_interior_count_one_add (s : List R)
    (hs : forall a, List.Mem a s -> 0 <= a /\ a <= 1) (r : Nat) :
    bernoulliMass s (s.count 1 + r) = bernoulliMass (bernoulliInterior s) r := by
  calc
    bernoulliMass s (s.count 1 + r) =
        bernoulliMass (s.filter (fun a => decide (Not (a = 1)))) r :=
      bernoulliMass_count_one_add s r
    _ = bernoulliMass
        ((s.filter (fun a => decide (Not (a = 1)))).filter
          (fun a => decide (Not (a = 0)))) r :=
      (bernoulliMass_filter_nonzero _ r).symm
    _ = bernoulliMass (bernoulliInterior s) r := by rw [erased_eq_interior s hs]

/-- Both ranks in the probability ratio undergo the same exact forced shift.
The lower shifted rank is guarded explicitly. -/
theorem bernoulliMass_ratio_interior (s : List R)
    (hs : forall a, List.Mem a s -> 0 <= a /\ a <= 1)
    (r : Nat) (hr : 1 <= r) :
    bernoulliMass s (s.count 1 + r - 1) / bernoulliMass s (s.count 1 + r) =
      bernoulliMass (bernoulliInterior s) (r - 1) /
        bernoulliMass (bernoulliInterior s) r := by
  rw [show s.count 1 + r - 1 = s.count 1 + (r - 1) by omega,
    bernoulliMass_interior_count_one_add s hs (r - 1),
    bernoulliMass_interior_count_one_add s hs r]

/-- An observable vanishing on the two deterministic probabilities has the
same finite sum before and after removing those coordinates. -/
theorem sum_map_bernoulliInterior {M : Type*} [AddCommMonoid M]
    (s : List R) (hs : forall a, List.Mem a s -> 0 <= a /\ a <= 1)
    (f : R -> M) (hf0 : f 0 = 0) (hf1 : f 1 = 0) :
    ((bernoulliInterior s).map f).sum = (s.map f).sum := by
  induction s with
  | nil => simp [bernoulliInterior]
  | cons a s ih =>
      have ha := hs a (List.Mem.head _)
      have ht : forall b, List.Mem b s -> 0 <= b /\ b <= 1 :=
        fun b hb => hs b (List.Mem.tail _ hb)
      by_cases hz : a = 0
      next =>
        subst a
        simpa [bernoulliInterior, hf0] using ih ht
      next =>
        by_cases ho : a = 1
        next =>
          subst a
          simpa [bernoulliInterior, hf1] using ih ht
        next =>
          have hpos : 0 < a := by
            by_contra hn
            exact hz (le_antisymm (le_of_not_gt hn) ha.1)
          have hlt : a < 1 := by
            by_contra hn
            exact ho (le_antisymm ha.2 (le_of_not_gt hn))
          simpa [bernoulliInterior, hpos, hlt] using
            congrArg (fun b : M => f a + b) (ih ht)

end List

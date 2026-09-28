/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Mathlib.Probability.Distributions.FiniteBernoulliInterior
import PrimeFactorOscillations.Mathlib.Probability.Distributions.FiniteBernoulliOdds
import PrimeFactorOscillations.Mathlib.RingTheory.MvPolynomial.Symmetric.LargestWeightBounds

/-! # Actual finite Bernoulli ratio bounds with supported positive denominators -/

set_option autoImplicit false
set_option Elab.async false

namespace List

variable {R : Type*} [Field R] [LinearOrder R]

/-- A positive complementary weight sum forces the requested degree into
the finite support. No separate prime-count or enumeration estimate is needed. -/
theorem degree_supported_of_largest_complement_pos (s : List R) (r : Nat)
    (hc : 0 < s.sum - largestWeightSum s (r - 1)) : r <= s.length := by
  by_contra hn
  have hlen : (descendingWeightList s).length <= r - 1 := by
    rw [(descendingWeightList_perm s).length_eq]
    omega
  unfold largestWeightSum at hc
  rw [List.take_of_length_le hlen, (descendingWeightList_perm s).sum_eq, sub_self] at hc
  exact (lt_irrefl (0 : R)) hc

variable [IsStrictOrderedRing R]

private theorem survival_pos (s : List R)
    (hs : forall a, List.Mem a s -> a < 1) :
    0 < (s.map (fun a => 1 - a)).prod := by
  induction s with
  | nil => simp
  | cons a s ih =>
      simp only [List.map_cons, List.prod_cons]
      exact mul_pos (sub_pos.mpr (hs a (List.Mem.head _)))
        (ih (fun b hb => hs b (List.Mem.tail _ hb)))

private theorem interior_odds_pos (s : List R)
    (hs : forall a, List.Mem a s -> 0 < a /\ a < 1) :
    forall b, List.Mem b (s.map (fun a => a / (1 - a))) -> 0 < b := by
  intro b hb
  have ha := Classical.choose_spec (List.mem_map.mp hb)
  rw [<- ha.2]
  exact div_pos (hs _ ha.1).1 (sub_pos.mpr (hs _ ha.1).2)

/-- All supported finite Bernoulli coefficients are strictly positive when
each retained coordinate lies in the open probability interval. -/
theorem bernoulliMass_pos_of_interior (s : List R)
    (hs : forall a, List.Mem a s -> 0 < a /\ a < 1)
    (r : Nat) (hr : r <= s.length) : 0 < bernoulliMass s r := by
  have hne : forall a, List.Mem a s -> Not (a = 1) :=
    fun a ha => ne_of_lt (hs a ha).2
  rw [bernoulliMass_eq_survival_mul_esymm s hne r]
  apply mul_pos (survival_pos s (fun a ha => (hs a ha).2))
  apply Multiset.esymm_pos_ordered
  next =>
    intro b hb
    exact interior_odds_pos s hs b hb
  next => simpa using hr

/-- The exact ratio cancels the positive survival product; this theorem
keeps the probability and nonvanishing hypotheses explicit. -/
theorem bernoulliMass_ratio_eq_esymm (s : List R)
    (hs : forall a, List.Mem a s -> 0 < a /\ a < 1) (r : Nat) :
    bernoulliMass s (r - 1) / bernoulliMass s r =
      ((s.map (fun a => a / (1 - a)) : List R) : Multiset R).esymm (r - 1) /
        ((s.map (fun a => a / (1 - a)) : List R) : Multiset R).esymm r := by
  have hne : forall a, List.Mem a s -> Not (a = 1) :=
    fun a ha => ne_of_lt (hs a ha).2
  have hp := survival_pos s (fun a ha => (hs a ha).2)
  rw [bernoulliMass_eq_survival_mul_esymm s hne (r - 1),
    bernoulliMass_eq_survival_mul_esymm s hne r]
  exact mul_div_mul_left _ _ (ne_of_gt hp)

/-- Both bounds concern the actual probability coefficients. Positive
complement implies supported degree and a strictly positive denominator. -/
theorem bernoulliMass_ratio_bounds_largest (s : List R)
    (hs : forall a, List.Mem a s -> 0 < a /\ a < 1)
    (r : Nat) (hr : 1 <= r)
    (hc : 0 < (s.map (fun a => a / (1 - a))).sum -
      largestWeightSum (s.map (fun a => a / (1 - a))) (r - 1)) :
    r <= s.length /\ 0 < bernoulliMass s r /\
      (r : R) / (s.map (fun a => a / (1 - a))).sum <=
        bernoulliMass s (r - 1) / bernoulliMass s r /\
      bernoulliMass s (r - 1) / bernoulliMass s r <=
        (r : R) / ((s.map (fun a => a / (1 - a))).sum -
          largestWeightSum (s.map (fun a => a / (1 - a))) (r - 1)) := by
  have hsupport := degree_supported_of_largest_complement_pos
    (s.map (fun a => a / (1 - a))) r hc
  have hlen : r <= s.length := by simpa using hsupport
  have hbounds := esymm_ratio_bounds_largest (s.map (fun a => a / (1 - a)))
    (interior_odds_pos s hs) r hr hsupport hc
  have heq := bernoulliMass_ratio_eq_esymm s hs r
  rw [<- heq] at hbounds
  exact And.intro hlen (And.intro (bernoulliMass_pos_of_interior s hs r hlen) hbounds)

/-- Finite ratio bounds for the original probability list. Every forced
coordinate contributes exactly one to both ranks, every excluded coordinate
is removed without changing rank, and the denominator is proved positive. -/
theorem bernoulliMass_forced_ratio_bounds (s : List R)
    (hs : forall a, List.Mem a s -> 0 <= a /\ a <= 1)
    (r : Nat) (hr : 1 <= r)
    (hc : 0 < ((bernoulliInterior s).map (fun a => a / (1 - a))).sum -
      largestWeightSum ((bernoulliInterior s).map (fun a => a / (1 - a))) (r - 1)) :
    r <= (bernoulliInterior s).length /\
      0 < bernoulliMass s (s.count 1 + r) /\
      (r : R) / ((bernoulliInterior s).map (fun a => a / (1 - a))).sum <=
        bernoulliMass s (s.count 1 + r - 1) / bernoulliMass s (s.count 1 + r) /\
      bernoulliMass s (s.count 1 + r - 1) / bernoulliMass s (s.count 1 + r) <=
        (r : R) / (((bernoulliInterior s).map (fun a => a / (1 - a))).sum -
          largestWeightSum ((bernoulliInterior s).map (fun a => a / (1 - a))) (r - 1)) := by
  have hb := bernoulliMass_ratio_bounds_largest (bernoulliInterior s)
    (bernoulliInterior_mem s) r hr hc
  have hpos : 0 < bernoulliMass s (s.count 1 + r) := by
    rw [bernoulliMass_interior_count_one_add s hs r]
    exact hb.2.1
  refine And.intro hb.1 (And.intro hpos ?_)
  rw [bernoulliMass_ratio_interior s hs r hr]
  exact hb.2.2

end List

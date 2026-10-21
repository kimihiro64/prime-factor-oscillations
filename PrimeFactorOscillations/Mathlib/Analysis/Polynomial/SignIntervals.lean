/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Topology.Order.IntermediateValue

/-!
# Polynomial degree bounds from disjoint sign intervals

Strict sign changes produce distinct real roots by continuity. Finite collections
of pairwise disjoint open sign intervals therefore have cardinality at most the
polynomial's natural degree. Shared interval endpoints cause no exception.
-/

set_option autoImplicit false
set_option Elab.async false

namespace Polynomial

/-- Opposite endpoint signs force a root strictly inside the interval. -/
theorem exists_root_mem_Ioo_of_eval_mul_neg
    (p : Polynomial Real) {a b : Real} (hab : a < b)
    (hsign : p.eval a * p.eval b < 0) :
    Exists (fun r : Real =>
      And (Membership.mem (Set.Ioo a b) r) (p.eval r = 0)) := by
  have hclosed : Exists (fun r : Real =>
      And (Membership.mem (Set.Icc a b) r) (p.eval r = 0)) := by
    rcases mul_neg_iff.mp hsign with h | h
    case inl =>
      exact intermediate_value_Icc' hab.le p.continuous.continuousOn
        (And.intro h.2.le h.1.le)
    case inr =>
      exact intermediate_value_Icc hab.le p.continuous.continuousOn
        (And.intro h.1.le h.2.le)
  let r := Classical.choose hclosed
  have hr := Classical.choose_spec hclosed
  have ha : a < r := by
    by_contra h
    have heq : r = a := le_antisymm (le_of_not_gt h) hr.1.1
    have hz : p.eval a = 0 := by
      rw [<- heq]
      exact hr.2
    rw [hz, zero_mul] at hsign
    exact (lt_irrefl 0) hsign
  have hb : r < b := by
    by_contra h
    have heq : r = b := le_antisymm hr.1.2 (le_of_not_gt h)
    have hz : p.eval b = 0 := by
      rw [<- heq]
      exact hr.2
    rw [hz, mul_zero] at hsign
    exact (lt_irrefl 0) hsign
  exact Exists.intro r (And.intro (And.intro ha hb) hr.2)

universe u

/-- Pairwise disjoint intervals with opposite endpoint signs consume distinct roots. -/
theorem card_le_natDegree_of_disjoint_sign_intervals
    {I : Type u} (p : Polynomial Real) (hp : Not (p = 0))
    (s : Finset I) (a b : I -> Real)
    (hab : forall i, Membership.mem s i -> a i < b i)
    (hdis : (s : Set I).Pairwise (fun i j =>
      Disjoint (Set.Ioo (a i) (b i)) (Set.Ioo (a j) (b j))))
    (hsign : forall i, Membership.mem s i ->
      p.eval (a i) * p.eval (b i) < 0) :
    s.card <= p.natDegree := by
  classical
  have hroots : forall i, Membership.mem s i ->
      Exists (fun r : Real =>
        And (Membership.mem (Set.Ioo (a i) (b i)) r) (p.eval r = 0)) :=
    fun i hi => p.exists_root_mem_Ioo_of_eval_mul_neg (hab i hi) (hsign i hi)
  let r : I -> Real := fun i =>
    if hi : Membership.mem s i then Classical.choose (hroots i hi) else 0
  have hr (i : I) (hi : Membership.mem s i) :
      And (Membership.mem (Set.Ioo (a i) (b i)) (r i)) (p.eval (r i) = 0) := by
    dsimp only [r]
    rw [dite_eq_left hi]
    exact Classical.choose_spec (hroots i hi)
  have hmaps : Set.MapsTo r (s : Set I) (p.roots.toFinset : Set Real) := by
    intro i hi
    exact Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hp).mpr (hr i hi).2)
  have hinj : Set.InjOn r (s : Set I) := by
    intro i hi j hj hij
    by_contra hne
    have hd := hdis hi hj hne
    apply Set.disjoint_left.mp hd (hr i hi).1
    rw [hij]
    exact (hr j hj).1
  exact (Finset.card_le_card_of_injOn r hmaps hinj).trans
    ((Multiset.toFinset_card_le p.roots).trans p.card_roots')

end Polynomial

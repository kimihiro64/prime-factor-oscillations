/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianCycleOrientation
import PrimeFactorOscillations.Helpers.HamiltonianRegularFactorKernels

/-! # Actual simple cycle edges and the exclusion of a local double return -/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

variable {Iota : Type*} [Fintype Iota] [DecidableEq Iota]

theorem hamiltonian_single_orbit_no_two_step_return (f : Equiv.Perm Iota)
    (hCard : 3 <= Fintype.card Iota)
    (hOne : (hamiltonianPermutationOrbits f).card = 1) (x : Iota) :
    Not (f (f x) = x) := by
  classical
  intro hTwice
  have hPowers : forall k : Nat, Or ((f ^ k) x = x) ((f ^ k) x = f x) := by
    intro k
    induction k with
    | zero => exact Or.inl rfl
    | succ k ih =>
      rw [pow_succ', Equiv.Perm.mul_apply]
      cases ih with
      | inl h => rw [h]; exact Or.inr rfl
      | inr h => rw [h, hTwice]; exact Or.inl rfl
  have hAll : forall y : Iota, Membership.mem ({x, f x} : Finset Iota) y := by
    intro y
    choose k hk using (hamiltonian_single_orbit_same_cycle f hOne x y).exists_nat_pow_eq
    have h := hPowers k
    rw [hk] at h
    simp only [Finset.mem_insert, Finset.mem_singleton]
    exact h
  have hSub : forall y, Membership.mem (Finset.univ : Finset Iota) y ->
      Membership.mem ({x, f x} : Finset Iota) y := fun y _ => hAll y
  have hBound := Finset.card_le_card hSub
  have hPair : ({x, f x} : Finset Iota).card <= 2 := by
    simpa only [Finset.card_singleton] using Finset.card_insert_le x ({f x} : Finset Iota)
  rw [Finset.card_univ] at hBound
  omega

def hamiltonianBipartiteCycleEdges {m : Nat}
    (f : Equiv.Perm (Sum (Fin m) (Fin m))) : Finset (Prod (Fin m) (Fin m)) :=
  Finset.univ.filter (fun e =>
    f (Sum.inl e.1) = Sum.inr e.2 \/ f (Sum.inr e.2) = Sum.inl e.1)

theorem hamiltonian_bipartite_cycle_edges_mem {m : Nat}
    (f : Equiv.Perm (Sum (Fin m) (Fin m))) (a b : Fin m) :
    Membership.mem (hamiltonianBipartiteCycleEdges f) (a, b) <->
      f (Sum.inl a) = Sum.inr b \/ f (Sum.inr b) = Sum.inl a := by
  simp only [hamiltonianBipartiteCycleEdges, Finset.mem_filter, Finset.mem_univ, true_and]

theorem hamiltonian_bipartite_cycle_edges_subset {m : Nat}
    (f : Equiv.Perm (Sum (Fin m) (Fin m)))
    (F : Finset (Prod (Fin m) (Fin m)))
    (hSupport : forall i, Not (hamiltonianFactorAdjacency F (f i) i = 0)) :
    hamiltonianBipartiteCycleEdges f <= F := by
  intro e he
  have hEdge := (hamiltonian_bipartite_cycle_edges_mem f e.1 e.2).mp he
  by_contra hNot
  cases hEdge with
  | inl h =>
    have hBad := hSupport (Sum.inl e.1)
    rw [h] at hBad
    apply hBad
    change (if Membership.mem F e then (1 : Real) else 0) = 0
    simp only [hNot, ite_false]
  | inr h =>
    have hBad := hSupport (Sum.inr e.2)
    rw [h] at hBad
    apply hBad
    change (if Membership.mem F e then (1 : Real) else 0) = 0
    simp only [hNot, ite_false]

theorem hamiltonian_bipartite_cycle_left_neighbors {m : Nat}
    (f : Equiv.Perm (Sum (Fin m) (Fin m))) (hm : 2 <= m)
    (F : Finset (Prod (Fin m) (Fin m)))
    (hOne : (hamiltonianPermutationOrbits f).card = 1)
    (hSupport : forall i, Not (hamiltonianFactorAdjacency F (f i) i = 0)) (a : Fin m) :
    exists b c : Fin m, f (Sum.inl a) = Sum.inr b /\
      f (Sum.inr c) = Sum.inl a /\ Not (b = c) := by
  have hOut : exists b : Fin m, f (Sum.inl a) = Sum.inr b := by
    cases h : f (Sum.inl a) with
    | inl x =>
      have hBad := hSupport (Sum.inl a)
      rw [h] at hBad
      exact False.elim (hBad rfl)
    | inr b => exact Exists.intro b rfl
  have hIn : exists c : Fin m, f (Sum.inr c) = Sum.inl a := by
    have hPre := f.apply_symm_apply (Sum.inl a)
    cases h : f.symm (Sum.inl a) with
    | inl x =>
      rw [h] at hPre
      have hBad := hSupport (Sum.inl x)
      rw [hPre] at hBad
      exact False.elim (hBad rfl)
    | inr c =>
      rw [h] at hPre
      exact Exists.intro c hPre
  choose b hb using hOut
  choose c hc using hIn
  have hCard : 3 <= Fintype.card (Sum (Fin m) (Fin m)) := by
    simp only [Fintype.card_sum, Fintype.card_fin]
    omega
  refine Exists.intro b (Exists.intro c (And.intro hb (And.intro hc ?_)))
  intro hEq
  apply hamiltonian_single_orbit_no_two_step_return f hCard hOne (Sum.inl a)
  rw [hb, hEq, hc]

theorem hamiltonian_bipartite_cycle_right_neighbors {m : Nat}
    (f : Equiv.Perm (Sum (Fin m) (Fin m))) (hm : 2 <= m)
    (F : Finset (Prod (Fin m) (Fin m)))
    (hOne : (hamiltonianPermutationOrbits f).card = 1)
    (hSupport : forall i, Not (hamiltonianFactorAdjacency F (f i) i = 0)) (b : Fin m) :
    exists a c : Fin m, f (Sum.inr b) = Sum.inl a /\
      f (Sum.inl c) = Sum.inr b /\ Not (a = c) := by
  have hOut : exists a : Fin m, f (Sum.inr b) = Sum.inl a := by
    cases h : f (Sum.inr b) with
    | inl a => exact Exists.intro a rfl
    | inr x =>
      have hBad := hSupport (Sum.inr b)
      rw [h] at hBad
      exact False.elim (hBad rfl)
  have hIn : exists c : Fin m, f (Sum.inl c) = Sum.inr b := by
    have hPre := f.apply_symm_apply (Sum.inr b)
    cases h : f.symm (Sum.inr b) with
    | inl c =>
      rw [h] at hPre
      exact Exists.intro c hPre
    | inr x =>
      rw [h] at hPre
      have hBad := hSupport (Sum.inr x)
      rw [hPre] at hBad
      exact False.elim (hBad rfl)
  choose a ha using hOut
  choose c hc using hIn
  have hCard : 3 <= Fintype.card (Sum (Fin m) (Fin m)) := by
    simp only [Fintype.card_sum, Fintype.card_fin]
    omega
  refine Exists.intro a (Exists.intro c (And.intro ha (And.intro hc ?_)))
  intro hEq
  apply hamiltonian_single_orbit_no_two_step_return f hCard hOne (Sum.inr b)
  rw [ha, hEq, hc]


theorem hamiltonian_bipartite_cycle_left_degree {m : Nat}
    (f : Equiv.Perm (Sum (Fin m) (Fin m))) (hm : 2 <= m)
    (F : Finset (Prod (Fin m) (Fin m)))
    (hOne : (hamiltonianPermutationOrbits f).card = 1)
    (hSupport : forall i, Not (hamiltonianFactorAdjacency F (f i) i = 0)) (a : Fin m) :
    ((hamiltonianBipartiteCycleEdges f).filter (fun e => e.1 = a)).card = 2 := by
  choose b c hb hc hNe using hamiltonian_bipartite_cycle_left_neighbors f hm F hOne hSupport a
  have hMem (j : Fin m) :
      Membership.mem (hamiltonianBipartiteCycleEdges f) (a, j) <->
        b = j \/ j = c := by
    rw [hamiltonian_bipartite_cycle_edges_mem, hb, <- hc]
    simp only [Sum.inr.injEq, f.injective.eq_iff]
  have hSet : (hamiltonianBipartiteCycleEdges f).filter (fun e => e.1 = a) =
      {(a, b), (a, c)} := by
    ext e
    cases e with
    | mk x y =>
      by_cases hx : x = a
      case pos =>
        subst x
        simp [Finset.mem_filter, hMem, eq_comm]
      case neg =>
        simp [Finset.mem_filter, hx, Prod.mk.injEq]
  rw [hSet]
  apply Finset.card_pair_eq_two_iff.mpr
  intro h
  exact hNe (congrArg Prod.snd h)

theorem hamiltonian_bipartite_cycle_right_degree {m : Nat}
    (f : Equiv.Perm (Sum (Fin m) (Fin m))) (hm : 2 <= m)
    (F : Finset (Prod (Fin m) (Fin m)))
    (hOne : (hamiltonianPermutationOrbits f).card = 1)
    (hSupport : forall i, Not (hamiltonianFactorAdjacency F (f i) i = 0)) (b : Fin m) :
    ((hamiltonianBipartiteCycleEdges f).filter (fun e => e.2 = b)).card = 2 := by
  choose a c ha hc hNe using hamiltonian_bipartite_cycle_right_neighbors f hm F hOne hSupport b
  have hMem (j : Fin m) :
      Membership.mem (hamiltonianBipartiteCycleEdges f) (j, b) <->
        j = c \/ a = j := by
    rw [hamiltonian_bipartite_cycle_edges_mem, ha, <- hc]
    simp only [Sum.inl.injEq, f.injective.eq_iff]
  have hSet : (hamiltonianBipartiteCycleEdges f).filter (fun e => e.2 = b) =
      {(c, b), (a, b)} := by
    ext e
    cases e with
    | mk x y =>
      by_cases hy : y = b
      case pos =>
        subst y
        simp [Finset.mem_filter, hMem, eq_comm]
      case neg =>
        simp [Finset.mem_filter, hy, Prod.mk.injEq]
  rw [hSet]
  apply Finset.card_pair_eq_two_iff.mpr
  intro h
  exact hNe (congrArg Prod.fst h).symm

end PrimeFactorOscillations

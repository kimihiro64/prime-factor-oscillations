/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianBipartiteCycleEdges
import PrimeFactorOscillations.Helpers.HamiltonianFactorDeletion

/-! # Finite edge-disjoint cycle iteration with exact remaining degrees -/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

theorem hamiltonian_factor_nonzero_mono {m : Nat}
    (H E : Finset (Prod (Fin m) (Fin m))) (hHE : H <= E)
    (s t : Sum (Fin m) (Fin m))
    (h : Not (hamiltonianFactorAdjacency H s t = 0)) :
    Not (hamiltonianFactorAdjacency E s t = 0) := by
  have hIndicator (e : Prod (Fin m) (Fin m))
      (hn : Not ((if Membership.mem H e then (1 : Real) else 0) = 0)) :
      Not ((if Membership.mem E e then (1 : Real) else 0) = 0) := by
    by_cases he : Membership.mem H e
    case pos => simp [hHE he]
    case neg => simp only [he, ite_false, not_true_eq_false] at hn
  cases s with
  | inl a =>
    cases t with
    | inl b => exact False.elim (h rfl)
    | inr b => exact hIndicator (a, b) h
  | inr a =>
    cases t with
    | inl b => exact hIndicator (b, a) h
    | inr b => exact False.elim (h rfl)

structure HamiltonianCyclePackingState {m : Nat}
    (E : Finset (Prod (Fin m) (Fin m))) (r j : Nat) where
  remaining : Finset (Prod (Fin m) (Fin m))
  cycles : Finset (Finset (Prod (Fin m) (Fin m)))
  subset : remaining <= E
  left_degree : forall a, (remaining.filter (fun e => e.1 = a)).card = r - 2 * j
  right_degree : forall b, (remaining.filter (fun e => e.2 = b)).card = r - 2 * j
  card : cycles.card = j
  used : forall C, Membership.mem cycles C -> C <= E \ remaining
  witness : forall C, Membership.mem cycles C ->
    exists f : Equiv.Perm (Sum (Fin m) (Fin m)),
      (hamiltonianPermutationOrbits f).card = 1 /\
      (forall i, Not (hamiltonianFactorAdjacency E (f i) i = 0)) /\
      C = hamiltonianBipartiteCycleEdges f
  pairwise : forall C, Membership.mem cycles C -> forall D, Membership.mem cycles D ->
    Not (C = D) -> Disjoint C D

def hamiltonian_cycle_packing_initial {m : Nat}
    (E : Finset (Prod (Fin m) (Fin m))) (r : Nat)
    (hLeft : forall a, (E.filter (fun e => e.1 = a)).card = r)
    (hRight : forall b, (E.filter (fun e => e.2 = b)).card = r) :
    HamiltonianCyclePackingState E r 0 where
  remaining := E
  cycles := Finset.empty
  subset := le_refl E
  left_degree := by simpa only [Nat.mul_zero, Nat.sub_zero] using hLeft
  right_degree := by simpa only [Nat.mul_zero, Nat.sub_zero] using hRight
  card := Finset.card_empty
  used := by intro C hC; exact False.elim (Finset.notMem_empty C hC)
  witness := by intro C hC; exact False.elim (Finset.notMem_empty C hC)
  pairwise := by intro C hC; exact False.elim (Finset.notMem_empty C hC)

theorem hamiltonian_cycle_packing_step {m r j : Nat} (hm : 2 <= m)
    (E : Finset (Prod (Fin m) (Fin m)))
    (s : HamiltonianCyclePackingState E r j)
    (f : Equiv.Perm (Sum (Fin m) (Fin m)))
    (hOne : (hamiltonianPermutationOrbits f).card = 1)
    (hSupport : forall i, Not (hamiltonianFactorAdjacency s.remaining (f i) i = 0)) :
    Nonempty (HamiltonianCyclePackingState E r (j + 1)) := by
  classical
  let Cnew := hamiltonianBipartiteCycleEdges f
  have hCH : Cnew <= s.remaining :=
    hamiltonian_bipartite_cycle_edges_subset f s.remaining hSupport
  have hCL (a : Fin m) : (Cnew.filter (fun e => e.1 = a)).card = 2 :=
    hamiltonian_bipartite_cycle_left_degree f hm s.remaining hOne hSupport a
  have hCR (b : Fin m) : (Cnew.filter (fun e => e.2 = b)).card = 2 :=
    hamiltonian_bipartite_cycle_right_degree f hm s.remaining hOne hSupport b
  have hCNonempty : Cnew.Nonempty := by
    apply Finset.nonempty_iff_ne_empty.mpr
    intro hEmpty
    have h := hCL (Fin.mk 0 (by omega))
    rw [hEmpty] at h
    simp only [Finset.filter_empty, Finset.card_empty] at h
    omega
  have hDisjoint (D : Finset (Prod (Fin m) (Fin m)))
      (hD : Membership.mem s.cycles D) : Disjoint Cnew D := by
    apply Finset.disjoint_left.mpr
    intro e heC heD
    exact (Finset.mem_sdiff.mp (s.used D hD heD)).2 (hCH heC)
  have hNotMem : Not (Membership.mem s.cycles Cnew) := by
    intro hMem
    choose e he using hCNonempty
    exact (Finset.mem_sdiff.mp (s.used Cnew hMem he)).2 (hCH he)
  let Hnew := s.remaining \ Cnew
  have hNewSubset : Hnew <= E := Finset.sdiff_subset.trans s.subset
  have hNewLeft (a : Fin m) :
      (Hnew.filter (fun e => e.1 = a)).card = r - 2 * (j + 1) := by
    have h := hamiltonian_factor_filtered_deletion s.remaining Cnew hCH (fun e => e.1 = a)
    rw [hCL a, s.left_degree a] at h
    change (Hnew.filter (fun e => e.1 = a)).card + 2 = r - 2 * j at h
    omega
  have hNewRight (b : Fin m) :
      (Hnew.filter (fun e => e.2 = b)).card = r - 2 * (j + 1) := by
    have h := hamiltonian_factor_filtered_deletion s.remaining Cnew hCH (fun e => e.2 = b)
    rw [hCR b, s.right_degree b] at h
    change (Hnew.filter (fun e => e.2 = b)).card + 2 = r - 2 * j at h
    omega
  refine Nonempty.intro {
    remaining := Hnew
    cycles := insert Cnew s.cycles
    subset := hNewSubset
    left_degree := hNewLeft
    right_degree := hNewRight
    card := ?_
    used := ?_
    witness := ?_
    pairwise := ?_ }
  next => rw [Finset.card_insert_of_notMem hNotMem, s.card]
  next =>
    intro C hC e he
    cases Finset.mem_insert.mp hC with
    | inl hEq =>
      subst C
      refine Finset.mem_sdiff.mpr (And.intro (s.subset (hCH he)) ?_)
      intro heH
      exact (Finset.mem_sdiff.mp heH).2 he
    | inr hOld =>
      have hOldData := Finset.mem_sdiff.mp (s.used C hOld he)
      refine Finset.mem_sdiff.mpr (And.intro hOldData.1 ?_)
      intro heH
      exact hOldData.2 (Finset.mem_sdiff.mp heH).1
  next =>
    intro C hC
    cases Finset.mem_insert.mp hC with
    | inl hEq =>
      subst C
      refine Exists.intro f (And.intro hOne (And.intro ?_ rfl))
      intro i
      exact hamiltonian_factor_nonzero_mono s.remaining E s.subset (f i) i (hSupport i)
    | inr hOld => exact s.witness C hOld
  next =>
    intro C hC D hD hNe
    by_cases hCNew : C = Cnew
    case pos =>
      subst C
      have hDOld : Membership.mem s.cycles D := (Finset.mem_insert.mp hD).resolve_left
        (fun hEq => hNe hEq.symm)
      exact hDisjoint D hDOld
    case neg =>
      have hCOld : Membership.mem s.cycles C := (Finset.mem_insert.mp hC).resolve_left hCNew
      by_cases hDNew : D = Cnew
      case pos =>
        subst D
        exact (hDisjoint C hCOld).symm
      case neg =>
        have hDOld : Membership.mem s.cycles D := (Finset.mem_insert.mp hD).resolve_left hDNew
        exact s.pairwise C hCOld D hDOld hNe

theorem hamiltonian_finite_edge_disjoint_cycle_packing
    (m r k : Nat) (hm : 2 <= m) (hSize : 2 * k <= r)
    (E : Finset (Prod (Fin m) (Fin m)))
    (hLeft : forall a, (E.filter (fun e => e.1 = a)).card = r)
    (hRight : forall b, (E.filter (fun e => e.2 = b)).card = r)
    (hCycle : forall H : Finset (Prod (Fin m) (Fin m)), H <= E ->
      forall d : Nat, r - 2 * k + 2 <= d ->
        (forall a, (H.filter (fun e => e.1 = a)).card = d) ->
        (forall b, (H.filter (fun e => e.2 = b)).card = d) ->
        exists f : Equiv.Perm (Sum (Fin m) (Fin m)),
          (hamiltonianPermutationOrbits f).card = 1 /\
            (forall i, Not (hamiltonianFactorAdjacency H (f i) i = 0))) :
    exists Cs : Finset (Finset (Prod (Fin m) (Fin m))), Cs.card = k /\
      (forall C, Membership.mem Cs C -> C <= E) /\
      (forall C, Membership.mem Cs C ->
        exists f : Equiv.Perm (Sum (Fin m) (Fin m)),
          (hamiltonianPermutationOrbits f).card = 1 /\
          (forall i, Not (hamiltonianFactorAdjacency E (f i) i = 0)) /\
          C = hamiltonianBipartiteCycleEdges f) /\
      (forall C, Membership.mem Cs C -> forall D, Membership.mem Cs D ->
        Not (C = D) -> Disjoint C D) := by
  have hBuild : forall j : Nat, j <= k -> Nonempty (HamiltonianCyclePackingState E r j) := by
    intro j
    induction j with
    | zero => exact fun _ => Nonempty.intro (hamiltonian_cycle_packing_initial E r hLeft hRight)
    | succ j ih =>
      intro hj
      cases ih (by omega : j <= k) with
      | intro s =>
        choose f hOne hSupport using
          hCycle s.remaining s.subset (r - 2 * j) (by omega) s.left_degree s.right_degree
        exact hamiltonian_cycle_packing_step hm E s f hOne hSupport
  cases hBuild k (le_refl k) with
  | intro s =>
    refine Exists.intro s.cycles (And.intro s.card (And.intro ?_
      (And.intro s.witness s.pairwise)))
    intro C hC e he
    exact (Finset.mem_sdiff.mp (s.used C hC he)).1

end PrimeFactorOscillations

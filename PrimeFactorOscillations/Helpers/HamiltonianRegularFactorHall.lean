/-
Copyright (c) 2026 Jonas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas
-/
import Mathlib.Data.Finset.Sum
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import PrimeFactorOscillations.Helpers.HamiltonianFiniteHall

/-!
# Edge-capacity-one Hall gadget for regular bipartite factors

The cut condition is kept in addition form, so the zero-rank case and
subsets with negative cardinality difference require no truncated subtraction.
-/

set_option autoImplicit false
set_option Elab.async false

open Finset

universe u v

variable {A : Type u} {B : Type v} [Fintype A] [Fintype B]
variable [DecidableEq A] [DecidableEq B]

abbrev hamiltonianFactorEdge (E : Finset (Prod A B)) :=
  {e : Prod A B // Membership.mem E e}

noncomputable def hamiltonianFactorCross (E : Finset (Prod A B))
    (S : Finset A) (T : Finset B) : Finset (hamiltonianFactorEdge E) := by
  classical
  exact univ.filter (fun e =>
    Membership.mem S e.val.1 /\ Not (Membership.mem T e.val.2))

def hamiltonianFactorGadget (E : Finset (Prod A B)) (r : Nat) :
    Sum (Prod A (Fin r)) (hamiltonianFactorEdge E) ->
    Sum (Prod B (Fin r)) (hamiltonianFactorEdge E) -> Prop
  | Sum.inl _ak, Sum.inl _bk => False
  | Sum.inl ak, Sum.inr e => ak.1 = e.val.1
  | Sum.inr e, Sum.inl bk => e.val.2 = bk.1
  | Sum.inr e, Sum.inr f => e = f

noncomputable def hamiltonianFactorNeighbors (E : Finset (Prod A B)) (r : Nat)
    (x : Sum (Prod A (Fin r)) (hamiltonianFactorEdge E)) :
    Finset (Sum (Prod B (Fin r)) (hamiltonianFactorEdge E)) := by
  classical
  exact univ.filter (hamiltonianFactorGadget E r x)

theorem hamiltonian_factor_gadget_hall
    (E : Finset (Prod A B)) (r : Nat)
    (hcut : forall (S : Finset A) (T : Finset B),
      r * S.card <= (hamiltonianFactorCross E S T).card + r * T.card)
    (Z : Finset (Sum (Prod A (Fin r)) (hamiltonianFactorEdge E))) :
    Z.card <= (Z.biUnion (hamiltonianFactorNeighbors E r)).card := by
  classical
  let slots := Z.toLeft
  let F := Z.toRight
  let S := slots.image Prod.fst
  let T := F.image (fun e => e.val.2)
  let C := hamiltonianFactorCross E S T
  let K := (T.product (univ : Finset (Fin r))).disjSum (Union.union F C)
  have hslots : slots.card <= S.card * r := by
    have hsub : slots <= S.product (univ : Finset (Fin r)) := by
      intro ak hak
      exact mem_product.mpr (And.intro (mem_image.mpr
        (Exists.intro ak (And.intro hak rfl))) (mem_univ ak.2))
    have hp : (S.product (univ : Finset (Fin r))).card = S.card * r := by
      calc
        (S.product (univ : Finset (Fin r))).card =
            S.card * (univ : Finset (Fin r)).card := Finset.card_product S univ
        _ = S.card * r := by rw [card_univ, Fintype.card_fin]
    exact Eq.mp (congrArg (fun n => slots.card <= n) hp) (card_le_card hsub)
  have hdisj : Disjoint F C := by
    apply disjoint_left.mpr
    intro e he hc
    have hnot := (mem_filter.mp hc).2.2
    apply hnot
    exact mem_image.mpr (Exists.intro e (And.intro he rfl))
  have hK : K <= Z.biUnion (hamiltonianFactorNeighbors E r) := by
    intro w hw
    rcases w with bk | e
    . have hbk : Membership.mem (T.product (univ : Finset (Fin r))) bk := by
        simpa only [K, inl_mem_disjSum] using hw
      have hb := (mem_product.mp hbk).1
      choose e he using (mem_image.mp hb)
      apply mem_biUnion.mpr
      refine Exists.intro (Sum.inr e) (And.intro ?_ ?_)
      . exact mem_toRight.mp he.1
      . apply mem_filter.mpr
        exact And.intro (mem_univ _) he.2
    . have he : Membership.mem (Union.union F C) e := by
        simpa only [K, inr_mem_disjSum] using hw
      rcases mem_union.mp he with he | he
      . apply mem_biUnion.mpr
        refine Exists.intro (Sum.inr e) (And.intro ?_ ?_)
        . exact mem_toRight.mp he
        . exact mem_filter.mpr (And.intro (mem_univ _) rfl)
      . have hS := (mem_filter.mp he).2.1
        choose ak hak using (mem_image.mp hS)
        apply mem_biUnion.mpr
        refine Exists.intro (Sum.inl ak) (And.intro ?_ ?_)
        . exact mem_toLeft.mp hak.1
        . exact mem_filter.mpr (And.intro (mem_univ _) hak.2)
  have hcardK : K.card = r * T.card + F.card + C.card := by
    have hp : (T.product (univ : Finset (Fin r))).card = T.card * r := by
      calc
        (T.product (univ : Finset (Fin r))).card =
            T.card * (univ : Finset (Fin r)).card := Finset.card_product T univ
        _ = T.card * r := by rw [card_univ, Fintype.card_fin]
    simp only [K, card_disjSum, card_union_of_disjoint hdisj]
    rw [hp]
    ac_rfl
  calc
    Z.card = slots.card + F.card := (card_toLeft_add_card_toRight (u := Z)).symm
    _ <= S.card * r + F.card := Nat.add_le_add_right hslots _
    _ = r * S.card + F.card := by rw [Nat.mul_comm S.card r]
    _ <= C.card + r * T.card + F.card := Nat.add_le_add_right (hcut S T) _
    _ = K.card := by rw [hcardK]; ac_rfl
    _ <= (Z.biUnion (hamiltonianFactorNeighbors E r)).card := card_le_card hK

theorem hamiltonian_factor_gadget_matching
    (E : Finset (Prod A B)) (r : Nat)
    (hcut : forall (S : Finset A) (T : Finset B),
      r * S.card <= (hamiltonianFactorCross E S T).card + r * T.card) :
    Exists (fun f :
      Sum (Prod A (Fin r)) (hamiltonianFactorEdge E) ->
      Sum (Prod B (Fin r)) (hamiltonianFactorEdge E) =>
      Function.Injective f /\ forall x, hamiltonianFactorGadget E r x (f x)) := by
  classical
  choose f hf using HamiltonianFiniteHall.exists_matching
    (hamiltonian_factor_gadget_hall E r hcut)
  exact Exists.intro f (And.intro hf.1 (fun x => (mem_filter.mp (hf.2 x)).2))

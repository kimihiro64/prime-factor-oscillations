/-
Copyright (c) 2026 Jonas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas
-/
import PrimeFactorOscillations.Helpers.HamiltonianRegularFactorHall

/-!
# Extracting a simple regular factor from the full Hall gadget

Every original edge has one private pair of gadget vertices. The extraction
retains this capacity constraint and proves both degree equalities.
-/

set_option autoImplicit false
set_option Elab.async false

open Finset

universe u v

variable {A : Type u} {B : Type v} [Fintype A] [Fintype B]
variable [DecidableEq A] [DecidableEq B]

theorem hamiltonian_factor_matching_bijective
    (E : Finset (Prod A B)) (r : Nat)
    (hAB : Fintype.card A = Fintype.card B)
    (f : Sum (Prod A (Fin r)) (hamiltonianFactorEdge E) ->
      Sum (Prod B (Fin r)) (hamiltonianFactorEdge E))
    (hf : Function.Injective f) : Function.Bijective f := by
  classical
  have hcard : Fintype.card (Sum (Prod A (Fin r)) (hamiltonianFactorEdge E)) =
      Fintype.card (Sum (Prod B (Fin r)) (hamiltonianFactorEdge E)) := by
    simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, hAB]
  have himg : (univ.image f) = univ := by
    apply eq_of_subset_of_card_le (subset_univ _)
    rw [card_image_of_injective _ hf, card_univ, card_univ, hcard]
  refine And.intro hf ?_
  intro y
  have hy : Membership.mem (univ.image f) y := by rw [himg]; exact mem_univ _
  choose x hx using mem_image.mp hy
  exact Exists.intro x hx.2

theorem hamiltonian_factor_edge_used_iff
    (E : Finset (Prod A B)) (r : Nat)
    (f : Sum (Prod A (Fin r)) (hamiltonianFactorEdge E) ->
      Sum (Prod B (Fin r)) (hamiltonianFactorEdge E))
    (hf : Function.Bijective f)
    (hrel : forall x, hamiltonianFactorGadget E r x (f x))
    (e : hamiltonianFactorEdge E) :
    (Exists (fun ak : Prod A (Fin r) => f (Sum.inl ak) = Sum.inr e)) <->
      Exists (fun bk : Prod B (Fin r) => f (Sum.inr e) = Sum.inl bk) := by
  constructor
  . intro h
    choose ak hak using h
    cases he : f (Sum.inr e) with
    | inl bk => exact Exists.intro bk rfl
    | inr e' =>
      have hee : e = e' := by
        have h := hrel (Sum.inr e)
        simpa only [he, hamiltonianFactorGadget] using h
      subst e'
      have hx := hf.1 (hak.trans he.symm)
      cases hx
  . intro h
    choose bk hbk using h
    choose x hx using hf.2 (Sum.inr e)
    cases x with
    | inl ak => exact Exists.intro ak hx
    | inr e' =>
      have hee : e' = e := by
        have h := hrel (Sum.inr e')
        simpa only [hx, hamiltonianFactorGadget] using h
      subst e'
      have hbad := hx.symm.trans hbk
      cases hbad

theorem hamiltonian_factor_projection_card
    (E : Finset (Prod A B)) (F : Finset (hamiltonianFactorEdge E))
    (P : Prod A B -> Prop) [DecidablePred P] :
    ((F.image Subtype.val).filter P).card =
      (F.filter (fun e => P e.val)).card := by
  classical
  rw [filter_image]
  exact card_image_of_injective _ Subtype.coe_injective

theorem hamiltonian_bipartite_regular_factor
    (E : Finset (Prod A B)) (r : Nat)
    (hAB : Fintype.card A = Fintype.card B)
    (hcut : forall (S : Finset A) (T : Finset B),
      r * S.card <= (hamiltonianFactorCross E S T).card + r * T.card) :
    Exists (fun F : Finset (Prod A B) =>
      F <= E /\
      (forall a, (F.filter (fun e => e.1 = a)).card = r) /\
      (forall b, (F.filter (fun e => e.2 = b)).card = r)) := by
  classical
  choose f hf0 using hamiltonian_factor_gadget_matching E r hcut
  have hf := hamiltonian_factor_matching_bijective E r hAB f hf0.1
  have hrel := hf0.2
  let F : Finset (hamiltonianFactorEdge E) := univ.filter
    (fun e => Exists (fun ak : Prod A (Fin r) => f (Sum.inl ak) = Sum.inr e))
  have hleftSlot : forall ak : Prod A (Fin r),
      Exists (fun e : hamiltonianFactorEdge E =>
        f (Sum.inl ak) = Sum.inr e /\ e.val.1 = ak.1) := by
    intro ak
    cases he : f (Sum.inl ak) with
    | inl bk =>
      have h := hrel (Sum.inl ak)
      exact False.elim (by simpa only [he, hamiltonianFactorGadget] using h)
    | inr e =>
      refine Exists.intro e (And.intro rfl ?_)
      have h := hrel (Sum.inl ak)
      exact (show ak.1 = e.val.1 from
        by simpa only [he, hamiltonianFactorGadget] using h).symm
  choose phi hphi using hleftSlot
  have hrightSlot : forall bk : Prod B (Fin r),
      Exists (fun e : hamiltonianFactorEdge E =>
        f (Sum.inr e) = Sum.inl bk /\ e.val.2 = bk.1) := by
    intro bk
    choose x hx using hf.2 (Sum.inl bk)
    cases x with
    | inl ak =>
      have h := hrel (Sum.inl ak)
      exact False.elim (by simpa only [hx, hamiltonianFactorGadget] using h)
    | inr e =>
      refine Exists.intro e (And.intro hx ?_)
      have h := hrel (Sum.inr e)
      simpa only [hx, hamiltonianFactorGadget] using h
  choose psi hpsi using hrightSlot
  have hleft : forall a, (F.filter (fun e => e.val.1 = a)).card = r := by
    intro a
    have hset : F.filter (fun e => e.val.1 = a) =
        univ.image (fun k : Fin r => phi (a, k)) := by
      ext e
      constructor
      . intro he
        have heF := (mem_filter.mp he).1
        have heA := (mem_filter.mp he).2
        choose ak hak using (mem_filter.mp heF).2
        have hfirst : ak.1 = e.val.1 := by
          have h := hrel (Sum.inl ak)
          simpa only [hak, hamiltonianFactorGadget] using h
        have hakpair : ak = (a, ak.2) := Prod.ext (hfirst.trans heA) rfl
        have hfe : f (Sum.inl (a, ak.2)) = Sum.inr e := by
          calc
            f (Sum.inl (a, ak.2)) = f (Sum.inl ak) :=
              congrArg (fun q => f (Sum.inl q)) hakpair.symm
            _ = Sum.inr e := hak
        have hpe : phi (a, ak.2) = e := Sum.inr.inj ((hphi (a, ak.2)).1.symm.trans hfe)
        exact mem_image.mpr (Exists.intro ak.2 (And.intro (mem_univ _) hpe))
      . intro he
        choose k hk using mem_image.mp he
        rw [<- hk.2]
        apply mem_filter.mpr
        constructor
        . apply mem_filter.mpr
          exact And.intro (mem_univ _)
            (Exists.intro (a, k) (hphi (a, k)).1)
        . exact (hphi (a, k)).2
    have hinj : Function.Injective (fun k : Fin r => phi (a, k)) := by
      intro k l hkl
      change phi (a, k) = phi (a, l) at hkl
      have hfe : f (Sum.inl (a, k)) = f (Sum.inl (a, l)) := by
        rw [(hphi (a, k)).1, (hphi (a, l)).1, hkl]
      exact congrArg Prod.snd (Sum.inl.inj (hf.1 hfe))
    rw [hset, card_image_of_injective _ hinj, card_univ, Fintype.card_fin]
  have hright : forall b, (F.filter (fun e => e.val.2 = b)).card = r := by
    intro b
    have hset : F.filter (fun e => e.val.2 = b) =
        univ.image (fun k : Fin r => psi (b, k)) := by
      ext e
      constructor
      . intro he
        have heF := (mem_filter.mp he).1
        have heB := (mem_filter.mp he).2
        have hused := (mem_filter.mp heF).2
        choose bk hbk using (hamiltonian_factor_edge_used_iff E r f hf hrel e).mp hused
        have hsecond : e.val.2 = bk.1 := by
          have h := hrel (Sum.inr e)
          simpa only [hbk, hamiltonianFactorGadget] using h
        have hbkpair : bk = (b, bk.2) := Prod.ext (hsecond.symm.trans heB) rfl
        have hfe : f (Sum.inr e) = Sum.inl (b, bk.2) := by
          calc
            f (Sum.inr e) = Sum.inl bk := hbk
            _ = Sum.inl (b, bk.2) := congrArg Sum.inl hbkpair
        have hpe : psi (b, bk.2) = e :=
          Sum.inr.inj (hf.1 ((hpsi (b, bk.2)).1.trans hfe.symm))
        exact mem_image.mpr (Exists.intro bk.2 (And.intro (mem_univ _) hpe))
      . intro he
        choose k hk using mem_image.mp he
        rw [<- hk.2]
        apply mem_filter.mpr
        constructor
        . apply mem_filter.mpr
          refine And.intro (mem_univ _) ?_
          exact (hamiltonian_factor_edge_used_iff E r f hf hrel (psi (b, k))).mpr
            (Exists.intro (b, k) (hpsi (b, k)).1)
        . exact (hpsi (b, k)).2
    have hinj : Function.Injective (fun k : Fin r => psi (b, k)) := by
      intro k l hkl
      change psi (b, k) = psi (b, l) at hkl
      have hfe : Sum.inl (b, k) = (Sum.inl (b, l) :
          Sum (Prod B (Fin r)) (hamiltonianFactorEdge E)) := by
        rw [<- (hpsi (b, k)).1, <- (hpsi (b, l)).1, hkl]
      exact congrArg Prod.snd (Sum.inl.inj hfe)
    rw [hset, card_image_of_injective _ hinj, card_univ, Fintype.card_fin]
  refine Exists.intro (F.image Subtype.val) (And.intro ?_ (And.intro ?_ ?_))
  . intro e he
    choose q hq using mem_image.mp he
    rw [<- hq.2]
    exact q.property
  . intro a
    rw [hamiltonian_factor_projection_card]
    exact hleft a
  . intro b
    rw [hamiltonian_factor_projection_card]
    exact hright b

/-
Copyright (c) 2026 Jonas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas
-/
import PrimeFactorOscillations.Helpers.HamiltonianRegularFactorCriterion
import PrimeFactorOscillations.Helpers.HamiltonianSchurBudget

/-! # Actual adjacency loss of an integral regular factor -/

set_option autoImplicit false
set_option Elab.async false

open Finset
open scoped Matrix.Norms.L2Operator

universe u v

variable {A : Type u} {B : Type v} [Fintype A] [Fintype B]
variable [DecidableEq A] [DecidableEq B]

def hamiltonianFactorAdjacency (E : Finset (Prod A B)) :
    Matrix (Sum A B) (Sum A B) Real
  | Sum.inl _, Sum.inl _ => 0
  | Sum.inl a, Sum.inr b => if Membership.mem E (a, b) then 1 else 0
  | Sum.inr b, Sum.inl a => if Membership.mem E (a, b) then 1 else 0
  | Sum.inr _, Sum.inr _ => 0

theorem hamiltonian_factor_left_row_count (E : Finset (Prod A B)) (a : A) :
    univ.sum (fun b : B => if Membership.mem E (a, b) then (1 : Real) else 0) =
      ((E.filter (fun e => e.1 = a)).card : Real) := by
  classical
  have hc : (univ.filter (fun b : B => Membership.mem E (a, b))).card =
      (E.filter (fun e => e.1 = a)).card := by
    refine card_bij (fun b _ => (a, b)) ?_ ?_ ?_
    . intro b hb
      exact mem_filter.mpr (And.intro (mem_filter.mp hb).2 rfl)
    . intro b hb c hc hbc
      exact congrArg Prod.snd hbc
    . intro e he
      have heE := (mem_filter.mp he).1
      have heA := (mem_filter.mp he).2
      have hb : Membership.mem (univ.filter (fun b : B => Membership.mem E (a, b))) e.2 := by
        apply mem_filter.mpr
        constructor
        . exact mem_univ _
        . rw [<- heA]
          exact heE
      refine Exists.intro e.2 (Exists.intro hb ?_)
      exact Prod.ext heA.symm rfl
  calc
    _ = ((univ.filter (fun b : B => Membership.mem E (a, b))).card : Real) := by
      rw [card_eq_sum_ones, Nat.cast_sum]
      simp only [Nat.cast_one, sum_filter]
    _ = ((E.filter (fun e => e.1 = a)).card : Real) :=
      congrArg (fun n : Nat => (n : Real)) hc

theorem hamiltonian_factor_right_row_count (E : Finset (Prod A B)) (b : B) :
    univ.sum (fun a : A => if Membership.mem E (a, b) then (1 : Real) else 0) =
      ((E.filter (fun e => e.2 = b)).card : Real) := by
  classical
  have hc : (univ.filter (fun a : A => Membership.mem E (a, b))).card =
      (E.filter (fun e => e.2 = b)).card := by
    refine card_bij (fun a _ => (a, b)) ?_ ?_ ?_
    . intro a ha
      exact mem_filter.mpr (And.intro (mem_filter.mp ha).2 rfl)
    . intro a ha c hc hac
      exact congrArg Prod.fst hac
    . intro e he
      have heE := (mem_filter.mp he).1
      have heB := (mem_filter.mp he).2
      have ha : Membership.mem (univ.filter (fun a : A => Membership.mem E (a, b))) e.1 := by
        apply mem_filter.mpr
        constructor
        . exact mem_univ _
        . rw [<- heB]
          exact heE
      refine Exists.intro e.1 (Exists.intro ha ?_)
      exact Prod.ext rfl heB.symm
  calc
    _ = ((univ.filter (fun a : A => Membership.mem E (a, b))).card : Real) := by
      rw [card_eq_sum_ones, Nat.cast_sum]
      simp only [Nat.cast_one, sum_filter]
    _ = ((E.filter (fun e => e.2 = b)).card : Real) :=
      congrArg (fun n : Nat => (n : Real)) hc

theorem hamiltonian_factor_adjacency_row
    (E : Finset (Prod A B)) (i : Sum A B) :
    univ.sum (fun j => hamiltonianFactorAdjacency E i j) =
      match i with
      | Sum.inl a => ((E.filter (fun e => e.1 = a)).card : Real)
      | Sum.inr b => ((E.filter (fun e => e.2 = b)).card : Real) := by
  cases i with
  | inl a =>
    rw [Fintype.sum_sum_type]
    simpa only [hamiltonianFactorAdjacency, sum_const_zero, zero_add] using
      hamiltonian_factor_left_row_count E a
  | inr b =>
    rw [Fintype.sum_sum_type]
    simpa only [hamiltonianFactorAdjacency, sum_const_zero, add_zero] using
      hamiltonian_factor_right_row_count E b

theorem hamiltonian_factor_adjacency_symmetric
    (E : Finset (Prod A B)) (i j : Sum A B) :
    hamiltonianFactorAdjacency E i j = hamiltonianFactorAdjacency E j i := by
  cases i <;> cases j <;> rfl

theorem hamiltonian_factor_mass_left_original
    (E : Finset (Prod A B)) (a : A) :
    hamiltonianFactorMass (fun e : hamiltonianFactorEdge E => e.val.1) {a} =
      ((E.filter (fun e => e.1 = a)).card : Real) := by
  classical
  have himg : (univ : Finset (hamiltonianFactorEdge E)).image Subtype.val = E := by
    ext e
    simp
  have hc := hamiltonian_factor_projection_card E univ (fun e => e.1 = a)
  rw [himg] at hc
  unfold hamiltonianFactorMass
  simp only [mem_singleton]
  exact_mod_cast hc.symm

theorem hamiltonian_factor_mass_right_original
    (E : Finset (Prod A B)) (b : B) :
    hamiltonianFactorMass (fun e : hamiltonianFactorEdge E => e.val.2) {b} =
      ((E.filter (fun e => e.2 = b)).card : Real) := by
  classical
  have himg : (univ : Finset (hamiltonianFactorEdge E)).image Subtype.val = E := by
    ext e
    simp
  have hc := hamiltonian_factor_projection_card E univ (fun e => e.2 = b)
  rw [himg] at hc
  unfold hamiltonianFactorMass
  simp only [mem_singleton]
  exact_mod_cast hc.symm

theorem hamiltonian_factor_adjacency_loss
    (E F : Finset (Prod A B)) (r : Nat) (d : Real)
    (hFE : F <= E) (hdelta : 0 <= d - (r : Real))
    (hleft : forall a, ((E.filter (fun e => e.1 = a)).card : Real) <= d)
    (hright : forall b, ((E.filter (fun e => e.2 = b)).card : Real) <= d)
    (hFleft : forall a, (F.filter (fun e => e.1 = a)).card = r)
    (hFright : forall b, (F.filter (fun e => e.2 = b)).card = r) :
    norm (hamiltonianFactorAdjacency E - hamiltonianFactorAdjacency F) <= d - (r : Real) := by
  have hentry : forall e : Prod A B,
      (if Membership.mem F e then (1 : Real) else 0) <=
        (if Membership.mem E e then (1 : Real) else 0) := by
    intro e
    by_cases hF : Membership.mem F e
    . simp [hF, hFE hF]
    . by_cases hE : Membership.mem E e <;> simp [hF, hE]
  have hnonneg : forall i j : Sum A B,
      0 <= hamiltonianFactorAdjacency E i j - hamiltonianFactorAdjacency F i j := by
    intro i j
    cases i with
    | inl a =>
      cases j with
      | inl c => simp [hamiltonianFactorAdjacency]
      | inr b => exact sub_nonneg.mpr (hentry (a, b))
    | inr b =>
      cases j with
      | inl a => exact sub_nonneg.mpr (hentry (a, b))
      | inr c => simp [hamiltonianFactorAdjacency]
  apply PrimeFactorOscillations.hamiltonian_symmetric_row_budget
    (hamiltonianFactorAdjacency E - hamiltonianFactorAdjacency F)
    (fun i j => by
      simp only [Matrix.sub_apply, hamiltonian_factor_adjacency_symmetric E i j,
        hamiltonian_factor_adjacency_symmetric F i j])
    (d - (r : Real)) hdelta
  intro i
  have hnorm :
      univ.sum (fun j => norm
        ((hamiltonianFactorAdjacency E - hamiltonianFactorAdjacency F) i j)) =
      univ.sum (fun j => hamiltonianFactorAdjacency E i j -
        hamiltonianFactorAdjacency F i j) := by
    apply sum_congr rfl
    intro j hj
    exact Real.norm_of_nonneg (hnonneg i j)
  rw [hnorm, sum_sub_distrib, hamiltonian_factor_adjacency_row,
    hamiltonian_factor_adjacency_row]
  cases i with
  | inl a =>
    simp only [hFleft a]
    exact sub_le_sub_right (hleft a) _
  | inr b =>
    simp only [hFright b]
    exact sub_le_sub_right (hright b) _

theorem hamiltonian_regular_factor_and_operator
    (E : Finset (Prod A B)) (r : Nat)
    (hAB : Fintype.card A = Fintype.card B)
    (D g eps : Real) (hD : 0 < D) (hg : 0 < g)
    (heps : 0 <= eps) (hepsg : eps < g / 2)
    (hr : (r : Real) <= (1 - 2 * eps / g) * D)
    (hleft : forall a,
      (1 - eps) * D <= ((E.filter (fun e => e.1 = a)).card : Real) /\
      ((E.filter (fun e => e.1 = a)).card : Real) <= (1 + eps) * D)
    (hright : forall b,
      (1 - eps) * D <= ((E.filter (fun e => e.2 = b)).card : Real) /\
      ((E.filter (fun e => e.2 = b)).card : Real) <= (1 + eps) * D)
    (hcut : forall (S : Finset A) (T : Finset B),
      g * D * min ((S.card : Real) + (T.card : Real))
        (((Compl.compl S).card : Real) + ((Compl.compl T).card : Real)) <=
      ((hamiltonianFactorCross E S T).card : Real) +
        ((hamiltonianFactorCross E (Compl.compl S) (Compl.compl T)).card : Real)) :
    Exists (fun F : Finset (Prod A B) =>
      F <= E /\
      (forall a, (F.filter (fun e => e.1 = a)).card = r) /\
      (forall b, (F.filter (fun e => e.2 = b)).card = r) /\
      norm (hamiltonianFactorAdjacency E - hamiltonianFactorAdjacency F) <=
        (1 + eps) * D - (r : Real)) := by
  have hleftMass : forall a,
      (1 - eps) * D <=
        hamiltonianFactorMass (fun e : hamiltonianFactorEdge E => e.val.1) {a} /\
      hamiltonianFactorMass (fun e : hamiltonianFactorEdge E => e.val.1) {a} <=
        (1 + eps) * D := by
    intro a
    simpa only [hamiltonian_factor_mass_left_original] using hleft a
  have hrightMass : forall b,
      (1 - eps) * D <=
        hamiltonianFactorMass (fun e : hamiltonianFactorEdge E => e.val.2) {b} /\
      hamiltonianFactorMass (fun e : hamiltonianFactorEdge E => e.val.2) {b} <=
        (1 + eps) * D := by
    intro b
    simpa only [hamiltonian_factor_mass_right_original] using hright b
  choose F hF using hamiltonian_regular_factor_from_cuts E r hAB D g eps
    hD hg heps hepsg hr hleftMass hrightMass hcut
  have hq : 0 <= 2 * eps / g :=
    div_nonneg (mul_nonneg (by norm_num) heps) (le_of_lt hg)
  have hcoef : (1 - 2 * eps / g) * D <= (1 + eps) * D :=
    mul_le_mul_of_nonneg_right (by linarith only [heps, hq]) (le_of_lt hD)
  have hdelta : 0 <= (1 + eps) * D - (r : Real) := by linarith only [hr, hcoef]
  refine Exists.intro F
    (And.intro hF.1 (And.intro hF.2.1 (And.intro hF.2.2 ?_)))
  exact hamiltonian_factor_adjacency_loss E F r ((1 + eps) * D)
    hF.1 hdelta (fun a => (hleft a).2) (fun b => (hright b).2)
    hF.2.1 hF.2.2

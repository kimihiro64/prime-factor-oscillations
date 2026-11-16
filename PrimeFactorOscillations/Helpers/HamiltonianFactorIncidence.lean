/-
Copyright (c) 2026 Jonas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas
-/
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import PrimeFactorOscillations.Helpers.HamiltonianRegularFactorMatching

/-!
# Exact incidence balances for the regular-factor cut criterion

The forward and reverse boundary counts stay coupled. Both complementary
degree bounds are available before the minimum-size cut is selected.
-/

set_option autoImplicit false
set_option Elab.async false

open Finset

universe u v w

noncomputable def hamiltonianFactorMass
    {X : Type u} [Fintype X] {Y : Type v} (f : X -> Y)
    (S : Finset Y) : Real := by
  classical
  exact ((univ.filter (fun x => Membership.mem S (f x))).card : Real)

theorem hamiltonian_factor_mass_fibers
    {X : Type u} [Fintype X] {Y : Type v} [DecidableEq Y]
    (f : X -> Y) (S : Finset Y) :
    hamiltonianFactorMass f S =
      S.sum (fun a => hamiltonianFactorMass f {a}) := by
  classical
  unfold hamiltonianFactorMass
  simp only [card_eq_sum_ones, Nat.cast_sum, Nat.cast_one, sum_filter,
    mem_singleton]
  rw [sum_comm]
  apply sum_congr rfl
  intro x hx
  by_cases h : Membership.mem S (f x)
  . simp [h, eq_comm]
  . simp [h, eq_comm]

theorem hamiltonian_factor_mass_bounds
    {X : Type u} [Fintype X] {Y : Type v} [DecidableEq Y]
    (f : X -> Y) (S : Finset Y) (lo hi : Real)
    (hdeg : forall a, lo <= hamiltonianFactorMass f {a} /\
      hamiltonianFactorMass f {a} <= hi) :
    lo * (S.card : Real) <= hamiltonianFactorMass f S /\
      hamiltonianFactorMass f S <= hi * (S.card : Real) := by
  rw [hamiltonian_factor_mass_fibers]
  constructor
  . calc
      lo * (S.card : Real) = S.sum (fun _ => lo) := by simp [mul_comm]
      _ <= S.sum (fun a => hamiltonianFactorMass f {a}) :=
        sum_le_sum (fun a _ => (hdeg a).1)
  . calc
      S.sum (fun a => hamiltonianFactorMass f {a}) <= S.sum (fun _ => hi) :=
        sum_le_sum (fun a _ => (hdeg a).2)
      _ = hi * (S.card : Real) := by simp [mul_comm]

theorem hamiltonian_factor_mass_complement
    {X : Type u} [Fintype X] {Y : Type v} [Fintype Y] [DecidableEq Y]
    (f : X -> Y) (S : Finset Y) :
    hamiltonianFactorMass f S + hamiltonianFactorMass f (Compl.compl S) =
      (Fintype.card X : Real) := by
  classical
  unfold hamiltonianFactorMass
  simp only [card_eq_sum_ones, Nat.cast_sum, Nat.cast_one, sum_filter]
  rw [<- sum_add_distrib]
  calc
    _ = univ.sum (fun _ : X => (1 : Real)) := by
      apply sum_congr rfl
      intro x hx
      by_cases h : Membership.mem S (f x) <;> simp [h]
    _ = (Fintype.card X : Real) := by simp

variable {A : Type u} {B : Type v} [Fintype A] [Fintype B]
variable [DecidableEq A] [DecidableEq B]

theorem hamiltonian_factor_cross_balance
    (E : Finset (Prod A B)) (S : Finset A) (T : Finset B) :
    ((hamiltonianFactorCross E S T).card : Real) -
      ((hamiltonianFactorCross E (Compl.compl S) (Compl.compl T)).card : Real) =
      hamiltonianFactorMass (fun e : hamiltonianFactorEdge E => e.val.1) S -
      hamiltonianFactorMass (fun e : hamiltonianFactorEdge E => e.val.2) T := by
  classical
  unfold hamiltonianFactorCross hamiltonianFactorMass
  simp only [card_eq_sum_ones, Nat.cast_sum, Nat.cast_one, sum_filter]
  rw [<- sum_sub_distrib, <- sum_sub_distrib]
  apply sum_congr rfl
  intro e he
  by_cases hS : Membership.mem S e.val.1 <;>
    by_cases hT : Membership.mem T e.val.2 <;> simp [hS, hT]

theorem hamiltonian_factor_cross_degree_difference
    (E : Finset (Prod A B)) (S : Finset A) (T : Finset B)
    (D eps : Real)
    (hleft : forall a,
      (1 - eps) * D <=
        hamiltonianFactorMass (fun e : hamiltonianFactorEdge E => e.val.1) {a} /\
      hamiltonianFactorMass (fun e : hamiltonianFactorEdge E => e.val.1) {a} <=
        (1 + eps) * D)
    (hright : forall b,
      (1 - eps) * D <=
        hamiltonianFactorMass (fun e : hamiltonianFactorEdge E => e.val.2) {b} /\
      hamiltonianFactorMass (fun e : hamiltonianFactorEdge E => e.val.2) {b} <=
        (1 + eps) * D) :
    D * ((S.card : Real) - (T.card : Real)) -
        eps * D * ((S.card : Real) + (T.card : Real)) <=
      ((hamiltonianFactorCross E S T).card : Real) -
        ((hamiltonianFactorCross E (Compl.compl S) (Compl.compl T)).card : Real) := by
  rw [hamiltonian_factor_cross_balance]
  have hS := hamiltonian_factor_mass_bounds
    (fun e : hamiltonianFactorEdge E => e.val.1) S
    ((1 - eps) * D) ((1 + eps) * D) hleft
  have hT := hamiltonian_factor_mass_bounds
    (fun e : hamiltonianFactorEdge E => e.val.2) T
    ((1 - eps) * D) ((1 + eps) * D) hright
  nlinarith [hS.1, hT.2]

theorem hamiltonian_factor_cross_complement_difference
    (E : Finset (Prod A B)) (S : Finset A) (T : Finset B)
    (hAB : Fintype.card A = Fintype.card B) (D eps : Real)
    (hleft : forall a,
      (1 - eps) * D <=
        hamiltonianFactorMass (fun e : hamiltonianFactorEdge E => e.val.1) {a} /\
      hamiltonianFactorMass (fun e : hamiltonianFactorEdge E => e.val.1) {a} <=
        (1 + eps) * D)
    (hright : forall b,
      (1 - eps) * D <=
        hamiltonianFactorMass (fun e : hamiltonianFactorEdge E => e.val.2) {b} /\
      hamiltonianFactorMass (fun e : hamiltonianFactorEdge E => e.val.2) {b} <=
        (1 + eps) * D) :
    D * ((S.card : Real) - (T.card : Real)) -
        eps * D * (((Compl.compl S).card : Real) + ((Compl.compl T).card : Real)) <=
      ((hamiltonianFactorCross E S T).card : Real) -
        ((hamiltonianFactorCross E (Compl.compl S) (Compl.compl T)).card : Real) := by
  rw [hamiltonian_factor_cross_balance]
  have hS := hamiltonian_factor_mass_bounds
    (fun e : hamiltonianFactorEdge E => e.val.1) (Compl.compl S)
    ((1 - eps) * D) ((1 + eps) * D) hleft
  have hT := hamiltonian_factor_mass_bounds
    (fun e : hamiltonianFactorEdge E => e.val.2) (Compl.compl T)
    ((1 - eps) * D) ((1 + eps) * D) hright
  have hSc := hamiltonian_factor_mass_complement
    (fun e : hamiltonianFactorEdge E => e.val.1) S
  have hTc := hamiltonian_factor_mass_complement
    (fun e : hamiltonianFactorEdge E => e.val.2) T
  have hcS : ((Compl.compl S).card : Real) =
      (Fintype.card A : Real) - (S.card : Real) := by
    rw [card_compl, Nat.cast_sub (card_le_univ S)]
  have hcT : ((Compl.compl T).card : Real) =
      (Fintype.card B : Real) - (T.card : Real) := by
    rw [card_compl, Nat.cast_sub (card_le_univ T)]
  have hABR : (Fintype.card A : Real) = (Fintype.card B : Real) := by
    exact_mod_cast hAB
  rw [hcS] at hS
  rw [hcT] at hT
  rw [hcS, hcT]
  have hbalance :
      hamiltonianFactorMass (fun e : hamiltonianFactorEdge E => e.val.1) S -
        hamiltonianFactorMass (fun e : hamiltonianFactorEdge E => e.val.2) T =
      hamiltonianFactorMass (fun e : hamiltonianFactorEdge E => e.val.2) (Compl.compl T) -
        hamiltonianFactorMass (fun e : hamiltonianFactorEdge E => e.val.1) (Compl.compl S) := by
    linarith only [hSc, hTc]
  rw [hbalance]
  rw [hABR] at hS
  rw [hABR]
  nlinarith only [hS.2, hT.1]

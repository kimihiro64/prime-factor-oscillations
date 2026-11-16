/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianCenteredCuts
import PrimeFactorOscillations.Helpers.HamiltonianMatrixGeometry
import PrimeFactorOscillations.Helpers.HamiltonianRegularFactorOperator

/-! # Exact full-cut geometry for the integral prime-factor consumer -/

set_option autoImplicit false
set_option Elab.async false

open Finset PrimeFactorOscillations

universe u v w

theorem hamiltonian_factor_filter_count
    {A : Type u} {B : Type v} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (E : Finset (Prod A B)) (P : Prod A B -> Prop) [DecidablePred P] :
    ((E.filter P).card : Real) =
      univ.sum (fun a : A => univ.sum (fun b : B =>
        if And (P (a, b)) (Membership.mem E (a, b)) then (1 : Real) else 0)) := by
  classical
  have heq : E.filter P = univ.filter
      (fun e : Prod A B => And (P e) (Membership.mem E e)) := by
    ext e
    simp only [mem_filter, mem_univ, true_and, and_comm]
  rw [heq, card_eq_sum_ones, Nat.cast_sum]
  simp only [Nat.cast_one, sum_filter]
  exact Fintype.sum_prod_type _

theorem hamiltonian_factor_cross_sum
    {A : Type u} {B : Type v} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (E : Finset (Prod A B)) (S : Finset A) (T : Finset B) :
    ((hamiltonianFactorCross E S T).card : Real) =
      univ.sum (fun a : A => univ.sum (fun b : B =>
        if And (Membership.mem S a)
          (And (Not (Membership.mem T b)) (Membership.mem E (a, b)))
          then (1 : Real) else 0)) := by
  classical
  have himg : (univ : Finset (hamiltonianFactorEdge E)).image Subtype.val = E := by
    ext e
    simp
  have hc := hamiltonian_factor_projection_card E univ
    (fun e => And (Membership.mem S e.1) (Not (Membership.mem T e.2)))
  rw [himg] at hc
  calc
    _ = ((E.filter
        (fun e => And (Membership.mem S e.1) (Not (Membership.mem T e.2)))).card : Real) :=
      congrArg (fun n : Nat => (n : Real)) hc.symm
    _ = _ := by
      simpa only [and_assoc] using hamiltonian_factor_filter_count E
        (fun e => And (Membership.mem S e.1) (Not (Membership.mem T e.2)))

theorem hamiltonian_cut_full_sum
    {Iota : Type u} [Fintype Iota] [DecidableEq Iota]
    (M : Matrix Iota Iota Real) (W : Finset Iota) :
    hamiltonianCutBoundary M W = univ.sum (fun i => univ.sum (fun j =>
      if Membership.mem W i then
        if Not (Membership.mem W j) then M i j else 0 else 0)) := by
  have houter :
      hamiltonianCutBoundary M W = univ.sum (fun i =>
        if Membership.mem W i then (univ \ W).sum (fun j => M i j) else 0) := by
    rw [<- sum_filter, hamiltonian_cut_filter]
    rfl
  have hinner (i : Iota) :
      (univ \ W).sum (fun j => M i j) =
        univ.sum (fun j => if Not (Membership.mem W j) then M i j else 0) := by
    rw [<- sum_filter, hamiltonian_cut_complement_filter]
  rw [houter]
  simp_rw [hinner]
  apply sum_congr rfl
  intro i hi
  by_cases h : Membership.mem W i <;> simp only [h, ite_true, ite_false, sum_const_zero]

theorem hamiltonian_factor_full_boundary
    {A : Type u} {B : Type v} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (E : Finset (Prod A B)) (S : Finset A) (T : Finset B) :
    hamiltonianCutBoundary (hamiltonianFactorAdjacency E) (S.disjSum T) =
      ((hamiltonianFactorCross E S T).card : Real) +
        ((hamiltonianFactorCross E (Compl.compl S) (Compl.compl T)).card : Real) := by
  classical
  rw [hamiltonian_cut_full_sum, hamiltonian_factor_cross_sum,
    hamiltonian_factor_cross_sum]
  simp only [Fintype.sum_sum_type, hamiltonianFactorAdjacency,
    inl_mem_disjSum, inr_mem_disjSum, ite_self, sum_const_zero, zero_add, add_zero,
    mem_compl, not_not]
  congr 1
  . apply sum_congr rfl
    intro a ha
    apply sum_congr rfl
    intro b hb
    by_cases hS : Membership.mem S a <;>
      by_cases hT : Membership.mem T b <;>
      by_cases hE : Membership.mem E (a, b) <;> simp [hS, hT, hE]
  . calc
      _ = univ.sum (fun a : A => univ.sum (fun b : B =>
          if Membership.mem T b then if Not (Membership.mem S a) then
            if Membership.mem E (a, b) then (1 : Real) else 0 else 0 else 0)) :=
        sum_comm
      _ = _ := by
        apply sum_congr rfl
        intro a ha
        apply sum_congr rfl
        intro b hb
        by_cases hS : Membership.mem S a <;>
          by_cases hT : Membership.mem T b <;>
          by_cases hE : Membership.mem E (a, b) <;> simp [hS, hT, hE]

theorem hamiltonian_cut_reindex
    {Iota : Type u} {Kappa : Type v}
    [Fintype Iota] [Fintype Kappa] [DecidableEq Iota] [DecidableEq Kappa]
    (e : Equiv Kappa Iota) (M : Matrix Iota Iota Real) (W : Finset Kappa) :
    hamiltonianCutBoundary M (W.image e) =
      hamiltonianCutBoundary (M.submatrix e e) W := by
  classical
  have hm (i : Kappa) :
      Membership.mem (W.image e) (e i) <-> Membership.mem W i := by
    constructor
    . intro h
      choose j hj using mem_image.mp h
      have hji := e.injective hj.2
      rw [<- hji]
      exact hj.1
    . intro h
      exact mem_image.mpr (Exists.intro i (And.intro h rfl))
  rw [hamiltonian_cut_full_sum, hamiltonian_cut_full_sum]
  calc
    _ = univ.sum (fun i : Kappa => univ.sum (fun j : Iota =>
        if Membership.mem (W.image e) (e i) then
          if Not (Membership.mem (W.image e) j) then M (e i) j else 0 else 0)) :=
      (hamiltonian_sum_reindex e _).symm
    _ = univ.sum (fun i : Kappa => univ.sum (fun j : Kappa =>
        if Membership.mem (W.image e) (e i) then
          if Not (Membership.mem (W.image e) (e j)) then M (e i) (e j) else 0 else 0)) := by
      apply sum_congr rfl
      intro i hi
      exact (hamiltonian_sum_reindex e _).symm
    _ = _ := by simp only [hm, Matrix.submatrix_apply]

theorem hamiltonian_cut_scalar
    {Iota : Type u} [Fintype Iota] [DecidableEq Iota]
    (c : Real) (M : Matrix Iota Iota Real) (W : Finset Iota) :
    hamiltonianCutBoundary (SMul.smul c M) W = c * hamiltonianCutBoundary M W := by
  unfold hamiltonianCutBoundary
  have hpoint (i j : Iota) : SMul.smul c M i j = c * M i j := rfl
  simp_rw [hpoint]
  simp only [mul_sum]

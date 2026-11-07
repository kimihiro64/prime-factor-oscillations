/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Finset.Lattice.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Exact finite residual budgets after retaining every known contribution -/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace PrimeFactorOscillations

theorem finite_trace_residual_card {Iota : Type*} (S P : Finset Iota)
    (f ell : Iota -> Real) (q U : Real)
    (hMass : forall W : Finset Iota, Finset.sum W f <= U)
    (hKnown : forall i, Membership.mem S i -> ell i <= f i)
    (hNew : forall i, Membership.mem P i -> q <= f i)
    (hApart : forall i, Membership.mem P i -> Not (Membership.mem S i)) :
    q * (P.card : Real) <= U - Finset.sum S ell := by
  classical
  have hDisjoint : Disjoint S P := Finset.disjoint_left.mpr
    (fun i hiS hiP => hApart i hiP hiS)
  have hUpper := hMass (Union.union S P)
  rw [Finset.sum_union hDisjoint] at hUpper
  have hS := Finset.sum_le_sum hKnown
  have hP := Finset.sum_le_sum hNew
  have hCard : Finset.sum P (fun _ => q) = q * (P.card : Real) := by
    rw [Finset.sum_const, nsmul_eq_mul]
    ring
  rw [hCard] at hP
  linarith only [hUpper, hS, hP]

theorem finite_trace_residual_contains {Iota : Type*} (S : Finset Iota)
    (f ell : Iota -> Real) (q U : Real) (B : Iota -> Prop)
    (hMass : forall W : Finset Iota, Finset.sum W f <= U)
    (hKnown : forall i, Membership.mem S i -> ell i <= f i)
    (hBlock : forall i, B i -> q <= f i)
    (hBudget : U - Finset.sum S ell < q) :
    forall i, B i -> Membership.mem S i := by
  classical
  intro i hi
  by_contra hn
  have hS := Finset.sum_le_sum hKnown
  have hUpper := hMass (Insert.insert i S)
  rw [Finset.sum_insert hn] at hUpper
  have hLower := hBlock i hi
  linarith only [hS, hUpper, hLower, hBudget]

end PrimeFactorOscillations

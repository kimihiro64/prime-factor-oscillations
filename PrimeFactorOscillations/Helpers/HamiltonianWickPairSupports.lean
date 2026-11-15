/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Data.Finset.Powerset
import PrimeFactorOscillations.Helpers.HamiltonianGaussianWickReadout

/-! # Signed conversion between two-element supports and ordered pairs

The finite identity holds for arbitrary complex weights. No sign or phase
is discarded, and diagonal pairs are explicitly excluded.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

theorem wick_two_support_sum_insert {J : Type*} [DecidableEq J]
    (U : Finset J) (g : Finset J -> Complex) (a : J)
    (ha : Not (Membership.mem U a)) :
    Finset.sum ((insert a U).powersetCard 2) g =
      Finset.sum (U.powersetCard 2) g + Finset.sum U (fun i => g {a, i}) := by
  have hDisjoint : Disjoint (U.powersetCard 2)
      ((U.powersetCard 1).image (fun S : Finset J => insert a S)) := by
    apply Finset.disjoint_left.mpr
    intro S hS hImage
    have hWitness := Finset.mem_image.mp hImage
    let B := hWitness.choose
    have hEq : insert a B = S := hWitness.choose_spec.2
    have haS : Membership.mem S a := by rw [<- hEq]; exact Finset.mem_insert_self a B
    exact ha ((Finset.mem_powersetCard.mp hS).1 haS)
  have hInj : Set.InjOn (fun S : Finset J => insert a S) (U.powersetCard 1) := by
    intro S hS T hT hEq
    have haS : Not (Membership.mem S a) := by
      intro h
      exact ha ((Finset.mem_powersetCard.mp hS).1 h)
    have haT : Not (Membership.mem T a) := by
      intro h
      exact ha ((Finset.mem_powersetCard.mp hT).1 h)
    have hErase := congrArg (fun B : Finset J => B.erase a) hEq
    simpa [haS, haT] using hErase
  rw [Finset.powersetCard_succ_insert ha 1, Finset.sum_union hDisjoint,
    Finset.sum_image hInj, Finset.powersetCard_one, Finset.sum_map]
  rfl

theorem wick_two_support_sum_eq_ordered {J : Type*} [DecidableEq J]
    (U : Finset J) (g : Finset J -> Complex) :
    2 * Finset.sum (U.powersetCard 2) g =
      Finset.sum U (fun i => Finset.sum U
        (fun j => if i = j then 0 else g {i, j})) := by
  induction U using Finset.induction_on with
  | empty =>
    have hEmpty : (EmptyCollection.emptyCollection : Finset J).powersetCard 2 =
        EmptyCollection.emptyCollection := Finset.powersetCard_eq_empty.mpr (by simp)
    rw [hEmpty]
    simp
  | @insert a U ha ih =>
    have haNe : forall i, Membership.mem U i -> Not (a = i) := by
      intro i hi hEq
      exact ha (hEq.symm.rec hi)
    have hRow :
        Finset.sum (insert a U) (fun j => if a = j then 0 else g {a, j}) =
          Finset.sum U (fun j => g {a, j}) := by
      rw [Finset.sum_insert ha, if_pos rfl, zero_add]
      apply Finset.sum_congr rfl
      intro j hj
      rw [if_neg (haNe j hj)]
    have hOld :
        Finset.sum U (fun i => Finset.sum (insert a U)
          (fun j => if i = j then 0 else g {i, j})) =
          Finset.sum U (fun i => g {a, i}) +
            Finset.sum U (fun i => Finset.sum U (fun j => if i = j then 0 else g {i, j})) := by
      calc
        _ = Finset.sum U (fun i => g {a, i} +
            Finset.sum U (fun j => if i = j then 0 else g {i, j})) := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [Finset.sum_insert ha, if_neg (Ne.symm (haNe i hi)), Finset.pair_comm i a]
        _ = _ := Finset.sum_add_distrib
    calc
      _ = 2 * (Finset.sum (U.powersetCard 2) g + Finset.sum U (fun i => g {a, i})) :=
        congrArg (fun c : Complex => 2 * c) (wick_two_support_sum_insert U g a ha)
      _ = Finset.sum U (fun j => g {a, j}) +
          (Finset.sum U (fun i => g {a, i}) +
            Finset.sum U (fun i => Finset.sum U (fun j => if i = j then 0 else g {i, j}))) := by
        rw [mul_add, ih]
        ring
      _ = _ := by rw [Finset.sum_insert ha, hRow, hOld]

theorem gaussianLinearWickValue_two_triples_comm
    {Iota : Type*} [Fintype Iota] [DecidableEq Iota]
    (z a b : Iota -> Complex) :
    gaussianLinearWickValue z [a, a, a, b, b, b] =
      gaussianLinearWickValue z [b, b, b, a, a, a] := by
  unfold gaussianLinearWickValue
  apply congrArg (gaussianPolynomialState z)
  simp only [gaussianLinearProduct]
  ring

end PrimeFactorOscillations

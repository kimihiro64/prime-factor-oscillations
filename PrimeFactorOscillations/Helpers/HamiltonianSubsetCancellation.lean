/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring

/-! # Complete cycle-subset cancellation

The weighted powerset identity is the finite cancellation used in Liu's
Hamiltonian determinant-permanent formula. All subsets are retained. A cycle
family contributes exactly its total length when it consists of one cycle,
and zero otherwise. This module does not assert the later analytic estimates.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

variable {Iota R : Type*} [DecidableEq Iota] [CommRing R]

def signedSubsetMass (S : Finset Iota) : R :=
  Finset.sum S.powerset (fun T => (-1 : R) ^ T.card)

def signedSubsetLength (S : Finset Iota) (ell : Iota -> R) : R :=
  Finset.sum S.powerset
    (fun T => (-1 : R) ^ T.card * Finset.sum T ell)

theorem signedSubsetMass_insert (a : Iota) (S : Finset Iota)
    (ha : Not (Membership.mem S a)) :
    signedSubsetMass (R := R) (insert a S) = 0 := by
  classical
  unfold signedSubsetMass
  rw [Finset.sum_powerset_insert ha]
  have hNeg :
      Finset.sum S.powerset (fun T => (-1 : R) ^ (insert a T).card) =
        -Finset.sum S.powerset (fun T => (-1 : R) ^ T.card) := by
    calc
      _ = Finset.sum S.powerset (fun T => -((-1 : R) ^ T.card)) := by
        apply Finset.sum_congr rfl
        intro T hT
        have haT : Not (Membership.mem T a) := by
          intro h
          exact ha ((Finset.mem_powerset.mp hT) h)
        rw [Finset.card_insert_of_notMem haT, pow_succ]
        ring
      _ = _ := by rw [Finset.sum_neg_distrib]
  rw [hNeg]
  ring

theorem signedSubsetMass_eq (S : Finset Iota) :
    signedSubsetMass (R := R) S = if S.card = 0 then 1 else 0 := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [signedSubsetMass]
  | @insert a S ha ih =>
      rw [signedSubsetMass_insert (R := R) a S ha]
      simp [Finset.card_insert_of_notMem ha]

theorem signedSubsetLength_insert (a : Iota) (S : Finset Iota)
    (ell : Iota -> R) (ha : Not (Membership.mem S a)) :
    signedSubsetLength (insert a S) ell =
      -ell a * signedSubsetMass (R := R) S := by
  classical
  unfold signedSubsetLength signedSubsetMass
  rw [Finset.sum_powerset_insert ha]
  have hInsert :
      Finset.sum S.powerset
        (fun T => (-1 : R) ^ (insert a T).card *
          Finset.sum (insert a T) ell) =
        -ell a * Finset.sum S.powerset (fun T => (-1 : R) ^ T.card) -
          Finset.sum S.powerset
            (fun T => (-1 : R) ^ T.card * Finset.sum T ell) := by
    calc
      _ = Finset.sum S.powerset
          (fun T => -ell a * (-1 : R) ^ T.card -
            (-1 : R) ^ T.card * Finset.sum T ell) := by
        apply Finset.sum_congr rfl
        intro T hT
        have haT : Not (Membership.mem T a) := by
          intro h
          exact ha ((Finset.mem_powerset.mp hT) h)
        rw [Finset.card_insert_of_notMem haT, Finset.sum_insert haT, pow_succ]
        ring
      _ = _ := by rw [Finset.sum_sub_distrib, <- Finset.mul_sum]
  rw [hInsert]
  ring

theorem signedSubsetLength_eq (S : Finset Iota) (ell : Iota -> R) :
    signedSubsetLength S ell =
      if S.card = 1 then -Finset.sum S ell else 0 := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [signedSubsetLength]
  | @insert a S ha ih =>
      rw [signedSubsetLength_insert a S ell ha, signedSubsetMass_eq (R := R)]
      by_cases hS : S.card = 0
      case pos =>
        have hEmpty := Finset.card_eq_zero.mp hS
        simp [hEmpty]
      case neg =>
        simp [hS, Finset.card_insert_of_notMem ha]

theorem cycleSubsetIsolation (S : Finset Iota) (ell : Iota -> R) :
    -Finset.sum S.powerset
        (fun T => (-1 : R) ^ T.card * Finset.sum T ell) =
      if S.card = 1 then Finset.sum S ell else 0 := by
  change -signedSubsetLength S ell = _
  rw [signedSubsetLength_eq (R := R)]
  split_ifs <;> simp

end PrimeFactorOscillations

/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import PrimeFactorOscillations.Helpers.HamiltonianFiniteHall

/-! # Exact finite Hall matching on every stochastic support -/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

variable {Iota : Type*} [Fintype Iota] [DecidableEq Iota]

def hamiltonianStochasticNeighbors (P : Matrix Iota Iota Real) (i : Iota) :
    Finset Iota :=
  Finset.univ.filter (fun j => 0 < P i j)

theorem hamiltonian_stochastic_support_hall
    (P : Matrix Iota Iota Real) (hP : forall i j, 0 <= P i j)
    (hRows : forall i, Finset.univ.sum (fun j => P i j) = 1)
    (hCols : forall j, Finset.univ.sum (fun i => P i j) = 1)
    (S : Finset Iota) :
    S.card <= (S.biUnion (hamiltonianStochasticNeighbors P)).card := by
  classical
  let N := S.biUnion (hamiltonianStochasticNeighbors P)
  have hZero (j : Iota) (hj : Not (Membership.mem N j)) :
      S.sum (fun i => P i j) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    have hNo : Not (0 < P i j) := by
      intro hp
      apply hj
      exact Finset.mem_biUnion.mpr (Exists.intro i (And.intro hi
        (Finset.mem_filter.mpr (And.intro (Finset.mem_univ j) hp))))
    exact le_antisymm (le_of_not_gt hNo) (hP i j)
  have hCol (j : Iota) : S.sum (fun i => P i j) <= 1 := by
    calc
      _ <= Finset.univ.sum (fun i => P i j) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
          (fun i _ _ => hP i j)
      _ = 1 := hCols j
  have hSize : (S.card : Real) <= (N.card : Real) := by
    calc
      _ = S.sum (fun i => Finset.univ.sum (fun j => P i j)) := by simp [hRows]
      _ = Finset.univ.sum (fun j => S.sum (fun i => P i j)) := Finset.sum_comm
      _ = N.sum (fun j => S.sum (fun i => P i j)) := by
        symm
        exact Finset.sum_subset (Finset.subset_univ N) (fun j _ hj => hZero j hj)
      _ <= N.sum (fun _ => (1 : Real)) := Finset.sum_le_sum (fun j _ => hCol j)
      _ = _ := by simp
  exact_mod_cast hSize

theorem hamiltonian_stochastic_support_injective_matching
    (P : Matrix Iota Iota Real) (hP : forall i j, 0 <= P i j)
    (hRows : forall i, Finset.univ.sum (fun j => P i j) = 1)
    (hCols : forall j, Finset.univ.sum (fun i => P i j) = 1) :
    exists f : Iota -> Iota, Function.Injective f /\ forall i, 0 < P i (f i) := by
  choose f hf using HamiltonianFiniteHall.exists_matching
    (t := hamiltonianStochasticNeighbors P)
    (hamiltonian_stochastic_support_hall P hP hRows hCols)
  exact Exists.intro f (And.intro hf.1
    (fun i => (Finset.mem_filter.mp (hf.2 i)).2))

theorem hamiltonian_stochastic_support_permutation
    (P : Matrix Iota Iota Real) (hP : forall i j, 0 <= P i j)
    (hRows : forall i, Finset.univ.sum (fun j => P i j) = 1)
    (hCols : forall j, Finset.univ.sum (fun i => P i j) = 1) :
    exists f : Equiv.Perm Iota, forall i, 0 < P i (f i) := by
  classical
  choose f hf hSupport using
    hamiltonian_stochastic_support_injective_matching P hP hRows hCols
  have hImage : Finset.univ.image f = Finset.univ := by
    apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
    rw [Finset.card_image_of_injective _ hf]
  have hSurj : Function.Surjective f := by
    intro j
    have hj : Membership.mem (Finset.univ.image f) j := by
      rw [hImage]
      exact Finset.mem_univ _
    choose i hi using Finset.mem_image.mp hj
    exact Exists.intro i hi.2
  exact Exists.intro (Equiv.ofBijective f (And.intro hf hSurj)) hSupport

end PrimeFactorOscillations

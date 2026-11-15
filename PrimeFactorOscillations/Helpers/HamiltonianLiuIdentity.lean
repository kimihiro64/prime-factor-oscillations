/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import PrimeFactorOscillations.Helpers.HamiltonianInvariantCoefficient
import PrimeFactorOscillations.Helpers.HamiltonianPermutationSplitting

/-! # The full determinant-permanent cycle identity

Complementary restricted permutations are regrouped into actual full
permutations. Their complete invariant-subset coefficient cancels unless
the full permutation has one orbit. Singleton fixed-point orbits and empty
principal minors are included throughout; no support is discarded.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

variable {Iota R : Type*} [Fintype Iota] [DecidableEq Iota]

abbrev hamiltonianSplitData (Iota : Type*) :=
  Sigma (fun S : Finset Iota =>
    Prod (Equiv.Perm {x : Iota // Membership.mem S x})
      (Equiv.Perm {x : Iota // Not (Membership.mem S x)}))

abbrev hamiltonianInvariantData (Iota : Type*) :=
  Sigma (fun f : Equiv.Perm Iota =>
    {S : Finset Iota // hamiltonianPermutationInvariant f S})

def hamiltonianPermutationPartitionEquiv :
    Equiv (hamiltonianSplitData Iota) (hamiltonianInvariantData Iota) := by
  classical
  let first : Equiv (hamiltonianSplitData Iota)
      (Sigma (fun S : Finset Iota =>
        {f : Equiv.Perm Iota // hamiltonianPermutationInvariant f S})) := {
    toFun := fun p => Sigma.mk p.1 (hamiltonianSplitPermutationEquiv p.1 p.2)
    invFun := fun p => Sigma.mk p.1 ((hamiltonianSplitPermutationEquiv p.1).symm p.2)
    left_inv := by
      intro p
      cases p with
      | mk S p =>
        exact congrArg (Sigma.mk S)
          ((hamiltonianSplitPermutationEquiv S).symm_apply_apply p)
    right_inv := by
      intro p
      cases p with
      | mk S p =>
        exact congrArg (Sigma.mk S)
          ((hamiltonianSplitPermutationEquiv S).apply_symm_apply p) }
  let second : Equiv
      (Sigma (fun S : Finset Iota =>
        {f : Equiv.Perm Iota // hamiltonianPermutationInvariant f S}))
      (hamiltonianInvariantData Iota) := {
    toFun := fun p => Sigma.mk p.2.val (Subtype.mk p.1 p.2.property)
    invFun := fun p => Sigma.mk p.2.val (Subtype.mk p.1 p.2.property)
    left_inv := by intro p; cases p; rfl
    right_inv := by intro p; cases p; rfl }
  exact first.trans second

def hamiltonianLiuSum [CommRing R] (M : Matrix Iota Iota R) : R := by
  classical
  exact -Finset.sum Finset.univ (fun S : Finset Iota =>
    ((S.card : R) * (-1 : R) ^ S.card) *
      (Matrix.det (M.submatrix (fun i : {x : Iota // Membership.mem S x} => i.val)
          (fun i : {x : Iota // Membership.mem S x} => i.val)) *
        finitePermutationSum
          (M.submatrix (fun i : {x : Iota // Not (Membership.mem S x)} => i.val)
            (fun i : {x : Iota // Not (Membership.mem S x)} => i.val))))

def hamiltonianCycleSum [CommSemiring R] (M : Matrix Iota Iota R) : R := by
  classical
  exact Finset.sum Finset.univ (fun f : Equiv.Perm Iota =>
    if (hamiltonianPermutationOrbits f).card = 1 then
      Finset.prod Finset.univ (fun i => M (f i) i) else 0)

theorem hamiltonianLiu_principal_expansion [CommRing R]
    (M : Matrix Iota Iota R) (S : Finset Iota) :
    ((S.card : R) * (-1 : R) ^ S.card) *
        (Matrix.det (M.submatrix (fun i : {x : Iota // Membership.mem S x} => i.val)
            (fun i : {x : Iota // Membership.mem S x} => i.val)) *
          finitePermutationSum
            (M.submatrix (fun i : {x : Iota // Not (Membership.mem S x)} => i.val)
              (fun i : {x : Iota // Not (Membership.mem S x)} => i.val))) =
      Finset.sum Finset.univ
        (fun p : Prod (Equiv.Perm {x : Iota // Membership.mem S x})
            (Equiv.Perm {x : Iota // Not (Membership.mem S x)}) =>
          ((S.card : R) * (-1 : R) ^ S.card) *
            ((Equiv.Perm.sign p.1 : Int) : R) *
              Finset.prod Finset.univ (fun i => M (hamiltonianSplitPermutation S p.1 p.2 i) i)) := by
  classical
  rw [Fintype.sum_prod_type]
  simp only [Matrix.det_apply', finitePermutationSum, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr (by apply Finset.ext; intro i; simp only [Finset.mem_univ])
  intro a ha
  apply Finset.sum_congr (by apply Finset.ext; intro i; simp only [Finset.mem_univ])
  intro b hb
  rw [hamiltonianSplitPermutation_weight]
  simp only [Matrix.submatrix_apply, mul_assoc]

theorem hamiltonianLiuSum_eq_coefficient_sum [CommRing R]
    (M : Matrix Iota Iota R) :
    hamiltonianLiuSum M =
      Finset.sum Finset.univ (fun f : Equiv.Perm Iota =>
        hamiltonianInvariantCoefficient (R := R) f *
          Finset.prod Finset.univ (fun i => M (f i) i)) := by
  classical
  let F : hamiltonianSplitData Iota -> R := fun p =>
    ((p.1.card : R) * (-1 : R) ^ p.1.card) *
      ((Equiv.Perm.sign p.2.1 : Int) : R) *
        Finset.prod Finset.univ (fun i => M (hamiltonianSplitPermutation p.1 p.2.1 p.2.2 i) i)
  let G : hamiltonianInvariantData Iota -> R := fun p =>
    (p.2.val.card : R) *
      ((-1 : R) ^ p.2.val.card *
        ((Equiv.Perm.sign (Equiv.Perm.subtypePerm p.1
          (p := fun x => Membership.mem p.2.val x) p.2.property) : Int) : R)) *
            Finset.prod Finset.univ (fun i => M (p.1 i) i)
  have hLeftUniv : (Finset.univ : Finset (hamiltonianSplitData Iota)) =
      Finset.univ.sigma (fun S : Finset Iota =>
        (Finset.univ : Finset (Prod (Equiv.Perm {x : Iota // Membership.mem S x})
          (Equiv.Perm {x : Iota // Not (Membership.mem S x)})))) := by
    apply Finset.ext
    intro p
    simp
  have hRightUniv : (Finset.univ : Finset (hamiltonianInvariantData Iota)) =
      Finset.univ.sigma (fun f : Equiv.Perm Iota =>
        (Finset.univ : Finset {S : Finset Iota // hamiltonianPermutationInvariant f S})) := by
    apply Finset.ext
    intro p
    simp
  have hLeft :
      Finset.sum Finset.univ (fun S : Finset Iota =>
        ((S.card : R) * (-1 : R) ^ S.card) *
          (Matrix.det (M.submatrix (fun i : {x : Iota // Membership.mem S x} => i.val)
              (fun i : {x : Iota // Membership.mem S x} => i.val)) *
            finitePermutationSum
              (M.submatrix (fun i : {x : Iota // Not (Membership.mem S x)} => i.val)
                (fun i : {x : Iota // Not (Membership.mem S x)} => i.val)))) =
        Finset.sum Finset.univ F := by
    rw [hLeftUniv, Finset.sum_sigma]
    apply Finset.sum_congr (by apply Finset.ext; intro i; simp only [Finset.mem_univ])
    intro S hS
    exact hamiltonianLiu_principal_expansion M S
  have hPoint (p : hamiltonianSplitData Iota) :
      F p = G (hamiltonianPermutationPartitionEquiv p) := by
    change ((p.1.card : R) * (-1 : R) ^ p.1.card) *
        ((Equiv.Perm.sign p.2.1 : Int) : R) *
          Finset.prod Finset.univ (fun i => M (hamiltonianSplitPermutation p.1 p.2.1 p.2.2 i) i) =
      (p.1.card : R) * ((-1 : R) ^ p.1.card *
        ((Equiv.Perm.sign (Equiv.Perm.subtypePerm
          (hamiltonianSplitPermutation p.1 p.2.1 p.2.2)
          (p := fun x => Membership.mem p.1 x)
          (hamiltonianSplitPermutation_invariant p.1 p.2.1 p.2.2)) : Int) : R)) *
          Finset.prod Finset.univ (fun i => M (hamiltonianSplitPermutation p.1 p.2.1 p.2.2 i) i)
    rw [hamiltonianSplitPermutation_restrict_mem]
    simp only [mul_assoc]
  have hRegroup : Finset.sum Finset.univ F = Finset.sum Finset.univ G := by
    calc
      _ = Finset.sum Finset.univ
          (fun p : hamiltonianSplitData Iota => G (hamiltonianPermutationPartitionEquiv p)) := by
        apply Finset.sum_congr rfl
        intro p hp
        exact hPoint p
      _ = _ := Equiv.sum_comp hamiltonianPermutationPartitionEquiv G
  have hRight : Finset.sum Finset.univ G =
      Finset.sum Finset.univ (fun f : Equiv.Perm Iota =>
        Finset.sum Finset.univ
          (fun S : {S : Finset Iota // hamiltonianPermutationInvariant f S} =>
            (S.val.card : R) * ((-1 : R) ^ S.val.card *
              ((Equiv.Perm.sign (Equiv.Perm.subtypePerm f
                (p := fun x => Membership.mem S.val x) S.property) : Int) : R))) *
          Finset.prod Finset.univ (fun i => M (f i) i)) := by
    rw [hRightUniv, Finset.sum_sigma]
    apply Finset.sum_congr (by apply Finset.ext; intro i; simp only [Finset.mem_univ])
    intro f hf
    rw [Finset.sum_mul]
  unfold hamiltonianLiuSum
  rw [hLeft, hRegroup, hRight, <- Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro f hf
  unfold hamiltonianInvariantCoefficient
  exact (neg_mul _ _).symm

theorem hamiltonianLiuIdentity [CommRing R] (M : Matrix Iota Iota R) :
    hamiltonianLiuSum M = (Fintype.card Iota : R) * hamiltonianCycleSum M := by
  classical
  rw [hamiltonianLiuSum_eq_coefficient_sum, hamiltonianCycleSum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro f hf
  rw [hamiltonianInvariantCoefficient_eq]
  by_cases h : (hamiltonianPermutationOrbits f).card = 1
  next => simp only [h, ite_true]
  next => simp only [h, ite_false, zero_mul, mul_zero]

end PrimeFactorOscillations

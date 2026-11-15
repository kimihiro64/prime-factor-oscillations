/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianPermutationSplitting

/-! # Exact permanent transport and complementary zero-pattern splitting

Row permutations, transposition and simultaneous reindexing preserve the
actual permanent. A matrix with no edges between a set and its complement
splits into its two actual principal permanents. The proof reuses the
complete complementary-permutation bijection; outside permutations vanish
by an actual zero factor, with no estimate of a signed term.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

variable {Iota Jota R : Type*}
variable [Fintype Iota] [DecidableEq Iota]
variable [Fintype Jota] [DecidableEq Jota] [CommSemiring R]

theorem finitePermutationSum_rowPerm (M : Matrix Iota Iota R) (f : Equiv.Perm Iota) :
    finitePermutationSum (M.submatrix f id) = finitePermutationSum M := by
  classical
  let e : Equiv (Equiv.Perm Iota) (Equiv.Perm Iota) := {
    toFun := fun sigma => f * sigma
    invFun := fun sigma => (Inv.inv f) * sigma
    left_inv := by intro sigma; simp [mul_assoc]
    right_inv := by intro sigma; simp [mul_assoc] }
  change Finset.sum Finset.univ (fun sigma : Equiv.Perm Iota =>
      Finset.prod Finset.univ (fun i => M (f (sigma i)) i)) =
    Finset.sum Finset.univ (fun sigma : Equiv.Perm Iota =>
      Finset.prod Finset.univ (fun i => M (sigma i) i))
  exact Equiv.sum_comp e (fun sigma => Finset.prod Finset.univ (fun i => M (sigma i) i))

theorem finitePermutationSum_transpose (M : Matrix Iota Iota R) :
    finitePermutationSum M.transpose = finitePermutationSum M := by
  classical
  unfold finitePermutationSum
  calc
    _ = Finset.sum Finset.univ (fun sigma : Equiv.Perm Iota =>
        Finset.prod Finset.univ (fun i => M (sigma.symm i) i)) := by
      apply Finset.sum_congr rfl
      intro sigma hs
      have h := Equiv.prod_comp sigma (fun i => M (sigma.symm i) i)
      simpa only [Equiv.symm_apply_apply, Matrix.transpose_apply] using h
    _ = _ := by
      change Finset.sum Finset.univ (fun sigma : Equiv.Perm Iota =>
          Finset.prod Finset.univ (fun i => M ((Inv.inv sigma) i) i)) = _
      exact Equiv.sum_comp (Equiv.inv (Equiv.Perm Iota))
        (fun sigma => Finset.prod Finset.univ (fun i => M (sigma i) i))

theorem finitePermutationSum_reindex (e : Equiv Jota Iota) (M : Matrix Iota Iota R) :
    finitePermutationSum (M.submatrix e e) = finitePermutationSum M := by
  classical
  let p : Equiv (Equiv.Perm Jota) (Equiv.Perm Iota) := {
    toFun := fun sigma => e.symm.trans (sigma.trans e)
    invFun := fun sigma => e.trans (sigma.trans e.symm)
    left_inv := by
      intro sigma
      apply Equiv.ext
      intro i
      simp only [Equiv.trans_apply, Equiv.apply_symm_apply, Equiv.symm_apply_apply]
    right_inv := by
      intro sigma
      apply Equiv.ext
      intro i
      simp only [Equiv.trans_apply, Equiv.apply_symm_apply, Equiv.symm_apply_apply] }
  unfold finitePermutationSum
  calc
    _ = Finset.sum Finset.univ (fun sigma : Equiv.Perm Jota =>
        Finset.prod Finset.univ (fun i => M (p sigma i) i)) := by
      apply Finset.sum_congr rfl
      intro sigma hs
      have h := Equiv.prod_comp e (fun i => M (p sigma i) i)
      have hPoint (j : Jota) : p sigma (e j) = e (sigma j) := by
        change e (sigma (e.symm (e j))) = e (sigma j)
        rw [Equiv.symm_apply_apply]
      change Finset.prod Finset.univ (fun j => M (e (sigma j)) (e j)) =
        Finset.prod Finset.univ (fun i => M (p sigma i) i)
      calc
        _ = Finset.prod Finset.univ (fun j : Jota => M (p sigma (e j)) (e j)) := by
          apply Finset.prod_congr rfl
          intro j hj
          rw [hPoint]
        _ = _ := h
    _ = _ := Equiv.sum_comp p
      (fun sigma => Finset.prod Finset.univ (fun i => M (sigma i) i))

theorem finitePermutationSum_zeroPattern (M : Matrix Iota Iota R) (S : Finset Iota)
    (hCross : forall i j, Not (Membership.mem S i <-> Membership.mem S j) -> M i j = 0) :
    finitePermutationSum M =
      finitePermutationSum
          (M.submatrix (fun i : {x : Iota // Membership.mem S x} => i.val)
            (fun i : {x : Iota // Membership.mem S x} => i.val)) *
        finitePermutationSum
          (M.submatrix (fun i : {x : Iota // Not (Membership.mem S x)} => i.val)
            (fun i : {x : Iota // Not (Membership.mem S x)} => i.val)) := by
  classical
  let w : Equiv.Perm Iota -> R :=
    fun f => Finset.prod Finset.univ (fun i => M (f i) i)
  let selected : Finset (Equiv.Perm Iota) :=
    Finset.univ.filter (fun f => hamiltonianPermutationInvariant f S)
  have hZero (f : Equiv.Perm Iota) (hInv : Not (hamiltonianPermutationInvariant f S)) :
      w f = 0 := by
    have hNot : Not (forall x, Membership.mem S (f x) <-> Membership.mem S x) := hInv
    let bad := not_forall.mp hNot
    exact Finset.prod_eq_zero (Finset.mem_univ bad.choose)
      (hCross (f bad.choose) bad.choose bad.choose_spec)
  have hSubset : Finset.sum Finset.univ w = Finset.sum selected w := by
    apply Eq.symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro f hf hNot
    apply hZero
    intro hInv
    exact hNot (Finset.mem_filter.mpr (And.intro hf hInv))
  have hSubtype : Finset.sum selected w =
      Finset.sum Finset.univ
        (fun f : {f : Equiv.Perm Iota // hamiltonianPermutationInvariant f S} => w f.val) :=
    Finset.sum_subtype selected
      (fun f => by simp only [selected, Finset.mem_filter, Finset.mem_univ, true_and]) w
  calc
    finitePermutationSum M =
        Finset.sum Finset.univ
          (fun f : {f : Equiv.Perm Iota // hamiltonianPermutationInvariant f S} => w f.val) :=
      hSubset.trans hSubtype
    _ = Finset.sum Finset.univ
        (fun p : Prod (Equiv.Perm {x : Iota // Membership.mem S x})
            (Equiv.Perm {x : Iota // Not (Membership.mem S x)}) =>
          w (hamiltonianSplitPermutation S p.1 p.2)) :=
      (Equiv.sum_comp (hamiltonianSplitPermutationEquiv S) (fun f => w f.val)).symm
    _ = _ := by
      rw [Fintype.sum_prod_type]
      dsimp only [w]
      simp_rw [hamiltonianSplitPermutation_weight]
      simp only [finitePermutationSum, Matrix.submatrix_apply, Finset.sum_mul_sum]

end PrimeFactorOscillations

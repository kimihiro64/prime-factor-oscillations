/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.GroupTheory.Perm.Fin
import PrimeFactorOscillations.Helpers.HamiltonianRookGamma

/-! # Exact Laplace recursion for the maintained permanent

The recursion is used by the Gaussian Euler-to-permanent identification.
The omitted row is represented by the explicit zero-to-row transposition.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

def finitePermutationSum {K J : Type*} [CommSemiring K]
    [Fintype J] [DecidableEq J] (M : Matrix J J K) : K :=
  Finset.sum Finset.univ (fun sigma : Equiv.Perm J =>
    Finset.prod Finset.univ (fun i => M (sigma i) i))

theorem finitePermutationSum_fin_zero {K : Type*} [CommSemiring K]
    (M : Matrix (Fin 0) (Fin 0) K) :
    finitePermutationSum M = 1 := by
  simp [finitePermutationSum]

theorem finitePermutationSum_laplace {K : Type*} [CommSemiring K] {n : Nat}
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) K) :
    finitePermutationSum M =
      Finset.sum Finset.univ (fun j : Fin (n + 1) =>
        M j 0 * finitePermutationSum
          (M.submatrix (fun i : Fin n => Equiv.swap 0 j i.succ) Fin.succ)) := by
  classical
  let e : Equiv (Prod (Fin (n + 1)) (Equiv.Perm (Fin n)))
      (Equiv.Perm (Fin (n + 1))) := Equiv.Perm.decomposeFin.symm
  calc
    finitePermutationSum M =
        Finset.sum Finset.univ
          (fun p : Prod (Fin (n + 1)) (Equiv.Perm (Fin n)) =>
            Finset.prod Finset.univ (fun i => M (e p i) i)) := by
      exact (Equiv.sum_comp e
        (fun sigma => Finset.prod Finset.univ (fun i => M (sigma i) i))).symm
    _ = Finset.sum Finset.univ (fun j : Fin (n + 1) =>
        Finset.sum Finset.univ (fun sigma : Equiv.Perm (Fin n) =>
          M j 0 * Finset.prod Finset.univ (fun i : Fin n =>
            M (Equiv.swap 0 j (sigma i).succ) i.succ))) := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro j hj
      apply Finset.sum_congr rfl
      intro sigma hs
      rw [Fin.prod_univ_succ]
      simp only [e, Equiv.Perm.decomposeFin_symm_apply_zero,
        Equiv.Perm.decomposeFin_symm_apply_succ]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [finitePermutationSum, Finset.mul_sum]
      rfl

theorem finitePermutationSum_real {J : Type*} [Fintype J] [DecidableEq J]
    (M : Matrix J J Real) :
    finitePermutationSum (fun i j => (M i j : Complex)) =
      (weightedPermutationSum M : Complex) := by
  simp only [finitePermutationSum, weightedPermutationSum, Complex.ofReal_sum,
    Complex.ofReal_prod]

theorem weightedPermutationSum_fin_zero (M : Matrix (Fin 0) (Fin 0) Real) :
    weightedPermutationSum M = 1 :=
  finitePermutationSum_fin_zero M

theorem weightedPermutationSum_laplace {n : Nat}
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) Real) :
    weightedPermutationSum M =
      Finset.sum Finset.univ (fun j : Fin (n + 1) =>
        M j 0 * weightedPermutationSum
          (M.submatrix (fun i : Fin n => Equiv.swap 0 j i.succ) Fin.succ)) :=
  finitePermutationSum_laplace M

end PrimeFactorOscillations

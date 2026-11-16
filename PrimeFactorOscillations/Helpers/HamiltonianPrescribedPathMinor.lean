/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianCycleTransport
import PrimeFactorOscillations.Helpers.HamiltonianLiuIdentity
import PrimeFactorOscillations.Helpers.HamiltonianRectangularPermanentUpper

/-! # Prescribed Hamiltonian paths and their actual permanent minors

A unit closing edge from the terminal vertex to the initial vertex
turns a prescribed path into one permutation orbit. The closing edge
has weight one, so every original path edge keeps its original weight.
The exact minor and its row-substochastic upper bound retain both endpoints.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

variable {Iota R : Type*} [Fintype Iota] [DecidableEq Iota]

def hamiltonianPathClosingKernel [Zero R] [One R]
    (M : Matrix Iota Iota R) (a b : Iota) : Matrix Iota Iota R :=
  fun i j => if j = a then if i = b then 1 else 0 else M i j

def hamiltonianPrescribedPathSum [CommSemiring R]
    (M : Matrix Iota Iota R) (a b : Iota) : R :=
  hamiltonianCycleSum (hamiltonianPathClosingKernel M a b)

theorem hamiltonian_path_closing_nonnegative
    (M : Matrix Iota Iota Real) (a b : Iota)
    (hNonneg : forall i j, 0 <= M i j) :
    forall i j, 0 <= hamiltonianPathClosingKernel M a b i j := by
  intro i j
  unfold hamiltonianPathClosingKernel
  split_ifs
  next => exact zero_le_one
  next => exact le_refl 0
  next => exact hNonneg i j

theorem hamiltonian_cycle_sum_nonnegative
    (M : Matrix Iota Iota Real) (hNonneg : forall i j, 0 <= M i j) :
    0 <= hamiltonianCycleSum M := by
  unfold hamiltonianCycleSum
  apply Finset.sum_nonneg
  intro f hf
  split_ifs
  next => exact Finset.prod_nonneg (fun i hi => hNonneg (f i) i)
  next => exact le_refl 0

theorem hamiltonian_cycle_sum_le_permanent
    (M : Matrix Iota Iota Real) (hNonneg : forall i j, 0 <= M i j) :
    hamiltonianCycleSum M <= finitePermutationSum M := by
  unfold hamiltonianCycleSum finitePermutationSum
  apply Finset.sum_le_sum
  intro f hf
  split_ifs
  next => exact le_refl _
  next => exact Finset.prod_nonneg (fun i hi => hNonneg (f i) i)

theorem hamiltonian_prescribed_path_reindex
    {Jota : Type*} [Fintype Jota] [DecidableEq Jota] [CommSemiring R]
    (e : Equiv Jota Iota) (M : Matrix Iota Iota R) (a b : Jota) :
    hamiltonianPrescribedPathSum (M.submatrix e e) a b =
      hamiltonianPrescribedPathSum M (e a) (e b) := by
  have hKernel :
      hamiltonianPathClosingKernel (M.submatrix e e) a b =
        (hamiltonianPathClosingKernel M (e a) (e b)).submatrix e e := by
    ext i j
    simp only [hamiltonianPathClosingKernel, Matrix.submatrix_apply,
      Equiv.apply_eq_iff_eq]
  unfold hamiltonianPrescribedPathSum
  rw [hKernel, hamiltonian_cycle_sum_reindex e]

theorem hamiltonian_prescribed_path_fin_expansion
    [CommSemiring R] {n : Nat}
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) R) (b : Fin (n + 1)) :
    hamiltonianPrescribedPathSum M 0 b =
      Finset.univ.sum (fun f : Equiv.Perm (Fin (n + 1)) =>
        if (hamiltonianPermutationOrbits f).card = 1 /\ f 0 = b then
          Finset.univ.prod (fun i : Fin n => M (f i.succ) i.succ) else 0) := by
  unfold hamiltonianPrescribedPathSum hamiltonianCycleSum
  apply Finset.sum_congr rfl
  intro f hf
  by_cases hOrbit : (hamiltonianPermutationOrbits f).card = 1
  case pos =>
    rw [ite_eq_left hOrbit, Fin.prod_univ_succ]
    by_cases hEnd : f 0 = b
    case pos =>
      simp [hamiltonianPathClosingKernel, hOrbit, hEnd]
    case neg =>
      simp [hamiltonianPathClosingKernel, hOrbit, hEnd]
  case neg =>
    simp only [hOrbit, false_and, ite_false]

theorem hamiltonian_prescribed_path_permanent_minor
    [CommSemiring R] {n : Nat}
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) R) (b : Fin (n + 1)) :
    finitePermutationSum (hamiltonianPathClosingKernel M 0 b) =
      finitePermutationSum
        (M.submatrix (fun i : Fin n => Equiv.swap 0 b i.succ) Fin.succ) := by
  have hMinor (j : Fin (n + 1)) :
      (hamiltonianPathClosingKernel M 0 b).submatrix
          (fun i : Fin n => Equiv.swap 0 j i.succ) Fin.succ =
        M.submatrix (fun i : Fin n => Equiv.swap 0 j i.succ) Fin.succ := by
    ext i k
    simp [hamiltonianPathClosingKernel]
  rw [finitePermutationSum_laplace]
  simp_rw [hMinor]
  simp [hamiltonianPathClosingKernel]

theorem hamiltonian_prescribed_path_le_minor {n : Nat}
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) Real) (b : Fin (n + 1))
    (hNonneg : forall i j, 0 <= M i j) :
    hamiltonianPrescribedPathSum M 0 b <=
      finitePermutationSum
        (M.submatrix (fun i : Fin n => Equiv.swap 0 b i.succ) Fin.succ) := by
  have h := hamiltonian_cycle_sum_le_permanent
    (hamiltonianPathClosingKernel M 0 b)
    (hamiltonian_path_closing_nonnegative M 0 b hNonneg)
  rw [hamiltonian_prescribed_path_permanent_minor] at h
  exact h

theorem hamiltonian_prescribed_path_zero_upper {n : Nat}
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) Real) (b : Fin (n + 1)) (a X : Real)
    (ha : 1 <= a) (hX1 : 1 <= X) (hX : (n + 1 : Real) <= X)
    (hNonneg : forall i j, 0 <= M i j)
    (hRow : forall i, Finset.univ.sum (fun j => M i j) <= 1)
    (hCap : forall i j, M i j <= a / X) :
    hamiltonianPrescribedPathSum M 0 b <=
      Real.exp (-(n : Real) + 16 * a * Real.log (2 * X)) := by
  let A := M.submatrix (fun i : Fin n => Equiv.swap 0 b i.succ) Fin.succ
  have hMinorRow (i : Fin n) : Finset.univ.sum (fun j => A i j) <= 1 := by
    have h := hRow (Equiv.swap 0 b i.succ)
    rw [Fin.sum_univ_succ] at h
    have hFirst := hNonneg (Equiv.swap 0 b i.succ) 0
    change Finset.univ.sum (fun j : Fin n => M (Equiv.swap 0 b i.succ) j.succ) <= 1
    linarith only [h, hFirst]
  have hSize : (Fintype.card (Fin n) : Real) <= X := by
    simp only [Fintype.card_fin]
    linarith only [hX]
  have hUpper := hamiltonian_finite_permanent_row_cap_upper A.transpose a X ha hX1 hSize
    (fun i j => hNonneg (Equiv.swap 0 b j.succ) i.succ) hMinorRow
    (fun i j => hCap (Equiv.swap 0 b j.succ) i.succ)
  rw [finitePermutationSum_transpose] at hUpper
  simpa only [Fintype.card_fin] using
    (hamiltonian_prescribed_path_le_minor M b hNonneg).trans hUpper

theorem hamiltonian_prescribed_path_uniform_upper {n : Nat}
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) Real)
    (u v : Fin (n + 1)) (a X : Real)
    (ha : 1 <= a) (hX1 : 1 <= X) (hX : (n + 1 : Real) <= X)
    (hNonneg : forall i j, 0 <= M i j)
    (hRow : forall i, Finset.univ.sum (fun j => M i j) <= 1)
    (hCap : forall i j, M i j <= a / X) :
    hamiltonianPrescribedPathSum M u v <=
      Real.exp (-(n : Real) + 16 * a * Real.log (2 * X)) := by
  let e : Equiv.Perm (Fin (n + 1)) := Equiv.swap 0 u
  have hRowNew (i : Fin (n + 1)) :
      Finset.univ.sum (fun j => M.submatrix e e i j) <= 1 := by
    change Finset.univ.sum (fun j => M (e i) (e j)) <= 1
    rw [Equiv.sum_comp e]
    exact hRow (e i)
  have h := hamiltonian_prescribed_path_zero_upper (M.submatrix e e) (e.symm v) a X
    ha hX1 hX (fun i j => hNonneg (e i) (e j)) hRowNew
    (fun i j => hCap (e i) (e j))
  rw [hamiltonian_prescribed_path_reindex] at h
  have hZero : e 0 = u := Equiv.swap_apply_left 0 u
  simpa only [hZero, Equiv.apply_symm_apply] using h

end PrimeFactorOscillations

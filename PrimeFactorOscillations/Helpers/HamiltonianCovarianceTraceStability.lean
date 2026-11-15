/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianTraceSupportCompensation

/-! # Exact support stability of both full covariance traces

The trace of the matrix square keeps every ordered covariance pair.
The removed-by-full and retained-by-removed packets are disjoint.
Only the exact trace differences are estimated.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

variable {Iota : Type*} [Fintype Iota] [DecidableEq Iota]

theorem hamiltonian_trace_entry_bound (M : Matrix Iota Iota Real) (c : Real)
    (hM : forall i j, abs (M i j) <= c) :
    abs (Matrix.trace M) <= (Fintype.card Iota : Real) * c := by
  change abs (Finset.sum Finset.univ (fun i => M i i)) <= _
  calc
    _ <= Finset.sum Finset.univ (fun i => abs (M i i)) := Finset.abs_sum_le_sum_abs _ _
    _ <= Finset.sum Finset.univ (fun _ : Iota => c) :=
      Finset.sum_le_sum (fun i _ => hM i i)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

theorem hamiltonian_trace_supported_difference_bound
    (M : Matrix Iota Iota Real) (D : Finset Iota)
    (N : Matrix (Compl.compl D : Finset Iota) (Compl.compl D : Finset Iota) Real)
    (c eps : Real)
    (hM : forall i j, abs (M i j) <= c)
    (hDiff : forall i j, abs (N i j - M i.val j.val) <= eps) :
    abs (Matrix.trace N - Matrix.trace M) <=
      ((Compl.compl D : Finset Iota).card : Real) * eps + (D.card : Real) * c := by
  let R : Finset Iota := Compl.compl D
  let rr := fun i : R => (i.val : Iota)
  let MR := M.submatrix rr rr
  have hLocal := hamiltonian_trace_entry_bound (N - MR) eps hDiff
  have hLocalEq : Matrix.trace (N - MR) = Matrix.trace N - Matrix.trace MR := by
    change Finset.sum Finset.univ (fun i => N i i - MR i i) =
      Finset.sum Finset.univ (fun i => N i i) - Finset.sum Finset.univ (fun i => MR i i)
    rw [Finset.sum_sub_distrib]
  rw [hLocalEq] at hLocal
  simp only [Fintype.card_coe] at hLocal
  have hRemovedSum : abs (Finset.sum Finset.univ (fun i : D => M i.val i.val)) <=
      (D.card : Real) * c := by
    calc
      _ <= Finset.sum Finset.univ (fun i : D => abs (M i.val i.val)) :=
        Finset.abs_sum_le_sum_abs _ _
      _ <= Finset.sum Finset.univ (fun _ : D => c) :=
        Finset.sum_le_sum (fun i _ => hM i.val i.val)
      _ = _ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul]
  have hPartition := hamiltonian_sum_support_partition (fun i => M i i) D
  change Matrix.trace M = Finset.sum Finset.univ (fun i : D => M i.val i.val) +
    Matrix.trace MR at hPartition
  have hRemoved : abs (Matrix.trace MR - Matrix.trace M) <= (D.card : Real) * c := by
    have hEq : Matrix.trace MR - Matrix.trace M =
        -(Finset.sum Finset.univ (fun i : D => M i.val i.val)) := by
      linarith only [hPartition]
    rw [hEq, abs_neg]
    exact hRemovedSum
  have hEq : Matrix.trace N - Matrix.trace M =
      (Matrix.trace N - Matrix.trace MR) + (Matrix.trace MR - Matrix.trace M) := by ring
  rw [hEq]
  have hTriangle := abs_add_le (Matrix.trace N - Matrix.trace MR) (Matrix.trace MR - Matrix.trace M)
  linarith only [hTriangle, hLocal, hRemoved]

theorem hamiltonian_trace_square_supported_difference_bound
    (M : Matrix Iota Iota Real) (D : Finset Iota)
    (N : Matrix (Compl.compl D : Finset Iota) (Compl.compl D : Finset Iota) Real)
    (c eps : Real) (hc : 0 <= c) (hEps : 0 <= eps)
    (hM : forall i j, abs (M i j) <= c) (hN : forall i j, abs (N i j) <= c)
    (hDiff : forall i j, abs (N i j - M i.val j.val) <= eps) :
    abs (Matrix.trace (N * N) - Matrix.trace (M * M)) <=
      2 * ((Compl.compl D : Finset Iota).card : Real) ^ 2 * c * eps +
        2 * (D.card : Real) * (Fintype.card Iota : Real) * c ^ 2 := by
  let R : Finset Iota := Compl.compl D
  let rr := fun i : R => (i.val : Iota)
  let MR := M.submatrix rr rr
  have hPair (i j : R) : abs (N i j * N j i - MR i j * MR j i) <= 2 * c * eps := by
    have hOne : abs ((N i j - MR i j) * N j i) <= eps * c := by
      rw [abs_mul]
      exact mul_le_mul (hDiff i j) (hN j i) (abs_nonneg _) hEps
    have hTwo : abs (MR i j * (N j i - MR j i)) <= c * eps := by
      rw [abs_mul]
      exact mul_le_mul (hM i.val j.val) (hDiff j i) (abs_nonneg _) hc
    have hEq : N i j * N j i - MR i j * MR j i =
        (N i j - MR i j) * N j i + MR i j * (N j i - MR j i) := by ring
    rw [hEq]
    have hTriangle := abs_add_le ((N i j - MR i j) * N j i) (MR i j * (N j i - MR j i))
    nlinarith only [hTriangle, hOne, hTwo]
  have hLocal : abs (Matrix.trace (N * N) - Matrix.trace (MR * MR)) <=
      2 * (R.card : Real) ^ 2 * c * eps := by
    have h := hamiltonian_rectangular_sum_entry_bound _ (2 * c * eps) hPair
    have hEq : Matrix.trace (N * N) - Matrix.trace (MR * MR) =
        Finset.sum Finset.univ (fun i : R => Finset.sum Finset.univ
          (fun j : R => N i j * N j i - MR i j * MR j i)) := by
      change (Finset.sum Finset.univ (fun i : R =>
        Finset.sum Finset.univ (fun j : R => N i j * N j i))) -
          (Finset.sum Finset.univ (fun i : R =>
            Finset.sum Finset.univ (fun j : R => MR i j * MR j i))) = _
      simp only [Finset.sum_sub_distrib]
    rw [<- hEq] at h
    simp only [Fintype.card_coe] at h
    nlinarith only [h]
  have hOldPair (i j : Iota) : abs (M i j * M j i) <= c ^ 2 := by
    rw [abs_mul, pow_two]
    exact mul_le_mul (hM i j) (hM j i) (abs_nonneg _) hc
  have hRemoved : abs (Matrix.trace (MR * MR) - Matrix.trace (M * M)) <=
      2 * (D.card : Real) * (Fintype.card Iota : Real) * c ^ 2 := by
    rw [abs_sub_comm]
    exact hamiltonian_trace_removed_pair_bound M M D (c ^ 2) (sq_nonneg c) hOldPair
  have hEq : Matrix.trace (N * N) - Matrix.trace (M * M) =
      (Matrix.trace (N * N) - Matrix.trace (MR * MR)) +
        (Matrix.trace (MR * MR) - Matrix.trace (M * M)) := by ring
  rw [hEq]
  have hTriangle := abs_add_le (Matrix.trace (N * N) - Matrix.trace (MR * MR))
    (Matrix.trace (MR * MR) - Matrix.trace (M * M))
  linarith only [hTriangle, hLocal, hRemoved]

end PrimeFactorOscillations

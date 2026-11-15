/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianBoundaryEquations
import PrimeFactorOscillations.Helpers.HamiltonianScalingPerturbation

/-! # Disjoint trace support compensation and explicit remainder budgets

The full signed trace is partitioned before bounding any correction.
The removed-by-full and retained-by-removed domains are disjoint.
Zero diagonals remove the identity contribution exactly.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

theorem hamiltonian_rectangular_sum_entry_bound
    {Rows Cols : Type*} [Fintype Rows] [Fintype Cols]
    (f : Rows -> Cols -> Real) (c : Real)
    (hBound : forall i j, abs (f i j) <= c) :
    abs (Finset.sum Finset.univ (fun i => Finset.sum Finset.univ (fun j => f i j))) <=
      (Fintype.card Rows : Real) * (Fintype.card Cols : Real) * c := by
  calc
    _ <= Finset.sum Finset.univ (fun i => abs (Finset.sum Finset.univ (fun j => f i j))) :=
      Finset.abs_sum_le_sum_abs _ _
    _ <= Finset.sum Finset.univ (fun i => Finset.sum Finset.univ (fun j => abs (f i j))) :=
      Finset.sum_le_sum (fun i _ => Finset.abs_sum_le_sum_abs _ _)
    _ <= Finset.sum Finset.univ (fun _ : Rows => Finset.sum Finset.univ (fun _ : Cols => c)) :=
      Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hBound i j))
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      ring

variable {Iota : Type*} [Fintype Iota] [DecidableEq Iota]

theorem hamiltonian_trace_product_entry_bound
    (A B : Matrix Iota Iota Real) (a b : Real) (ha : 0 <= a) (_hb : 0 <= b)
    (hA : forall i j, abs (A i j) <= a) (hB : forall i j, abs (B i j) <= b) :
    abs (Matrix.trace (A * B)) <= (Fintype.card Iota : Real) ^ 2 * a * b := by
  have hPair (i j : Iota) : abs (A i j * B j i) <= a * b := by
    rw [abs_mul]
    exact mul_le_mul (hA i j) (hB j i) (abs_nonneg _) ha
  have h := hamiltonian_rectangular_sum_entry_bound (fun i j : Iota => A i j * B j i)
    (a * b) hPair
  change abs (Matrix.trace (A * B)) <=
    (Fintype.card Iota : Real) * (Fintype.card Iota : Real) * (a * b) at h
  nlinarith only [h]

theorem hamiltonian_trace_support_partition
    (A B : Matrix Iota Iota Real) (D : Finset Iota) :
    Matrix.trace (A * B) =
      Matrix.trace (A.submatrix
          (fun i : (Compl.compl D : Finset Iota) => i.val)
          (fun i : (Compl.compl D : Finset Iota) => i.val) *
        B.submatrix (fun i : (Compl.compl D : Finset Iota) => i.val)
          (fun i : (Compl.compl D : Finset Iota) => i.val)) +
      Finset.sum Finset.univ (fun d : D =>
        Finset.sum Finset.univ (fun j : Iota => A d.val j * B j d.val)) +
      Finset.sum Finset.univ (fun i : (Compl.compl D : Finset Iota) =>
        Finset.sum Finset.univ (fun d : D => A i.val d.val * B d.val i.val)) := by
  let R : Finset Iota := Compl.compl D
  have hOuter := hamiltonian_sum_support_partition
    (fun i => Finset.sum Finset.univ (fun j => A i j * B j i)) D
  have hInner :
      Finset.sum Finset.univ (fun i : R =>
        Finset.sum Finset.univ (fun j : Iota => A i.val j * B j i.val)) =
      Finset.sum Finset.univ (fun i : R =>
        Finset.sum Finset.univ (fun d : D => A i.val d.val * B d.val i.val)) +
      Finset.sum Finset.univ (fun i : R =>
        Finset.sum Finset.univ (fun j : R => A i.val j.val * B j.val i.val)) := by
    calc
      _ = Finset.sum Finset.univ (fun i : R =>
          Finset.sum Finset.univ (fun d : D => A i.val d.val * B d.val i.val) +
          Finset.sum Finset.univ (fun j : R => A i.val j.val * B j.val i.val)) :=
        Finset.sum_congr rfl (fun i _ =>
          hamiltonian_sum_support_partition (fun j => A i.val j * B j i.val) D)
      _ = _ := Finset.sum_add_distrib
  have hRetained :
      Matrix.trace (A.submatrix (fun i : R => i.val) (fun i : R => i.val) *
        B.submatrix (fun i : R => i.val) (fun i : R => i.val)) =
      Finset.sum Finset.univ (fun i : R =>
        Finset.sum Finset.univ (fun j : R => A i.val j.val * B j.val i.val)) := rfl
  change Finset.sum Finset.univ (fun i => Finset.sum Finset.univ (fun j => A i j * B j i)) = _
  rw [hOuter, hRetained, hInner]
  ring

theorem hamiltonian_trace_removed_pair_bound
    (A B : Matrix Iota Iota Real) (D : Finset Iota) (c : Real) (hc : 0 <= c)
    (hPair : forall i j, abs (A i j * B j i) <= c) :
    abs (Matrix.trace (A * B) -
      Matrix.trace (A.submatrix
          (fun i : (Compl.compl D : Finset Iota) => i.val)
          (fun i : (Compl.compl D : Finset Iota) => i.val) *
        B.submatrix (fun i : (Compl.compl D : Finset Iota) => i.val)
          (fun i : (Compl.compl D : Finset Iota) => i.val))) <=
      2 * (D.card : Real) * (Fintype.card Iota : Real) * c := by
  let R : Finset Iota := Compl.compl D
  let u := Finset.sum Finset.univ (fun d : D =>
    Finset.sum Finset.univ (fun j : Iota => A d.val j * B j d.val))
  let v := Finset.sum Finset.univ (fun i : R =>
    Finset.sum Finset.univ (fun d : D => A i.val d.val * B d.val i.val))
  have hIdentity := hamiltonian_trace_support_partition A B D
  have hDiff :
      Matrix.trace (A * B) -
        Matrix.trace (A.submatrix (fun i : R => i.val) (fun i : R => i.val) *
          B.submatrix (fun i : R => i.val) (fun i : R => i.val)) = u + v := by
    change Matrix.trace (A * B) =
      Matrix.trace (A.submatrix (fun i : R => i.val) (fun i : R => i.val) *
        B.submatrix (fun i : R => i.val) (fun i : R => i.val)) + u + v at hIdentity
    linarith only [hIdentity]
  have hU : abs u <= (D.card : Real) * (Fintype.card Iota : Real) * c := by
    have h := hamiltonian_rectangular_sum_entry_bound
      (fun (d : D) (j : Iota) => A d.val j * B j d.val) c (fun d j => hPair d.val j)
    simpa only [Fintype.card_coe] using h
  have hV : abs v <= (R.card : Real) * (D.card : Real) * c := by
    have h := hamiltonian_rectangular_sum_entry_bound
      (fun (i : R) (d : D) => A i.val d.val * B d.val i.val) c (fun i d => hPair i.val d.val)
    simpa only [Fintype.card_coe] using h
  have hCard : (R.card : Real) <= (Fintype.card Iota : Real) := by
    have h : (R.card : Real) <= ((Finset.univ : Finset Iota).card : Real) :=
      Nat.cast_le.mpr (Finset.card_le_card (Finset.subset_univ R))
    simpa only [Finset.card_univ] using h
  have hMul := mul_le_mul_of_nonneg_right hCard
    (mul_nonneg (Nat.cast_nonneg D.card) hc)
  rw [hDiff]
  have hTriangle := abs_add_le u v
  nlinarith only [hTriangle, hU, hV, hMul]

theorem hamiltonian_trace_one_sub_zero_diagonal
    (G E : Matrix Iota Iota Real) (hDiag : forall i, E i i = 0) :
    Matrix.trace ((1 - G) * E) = -Matrix.trace (G * E) := by
  rw [sub_mul, one_mul]
  change Finset.sum Finset.univ (fun i => E i i - (G * E) i i) =
    -Finset.sum Finset.univ (fun i => (G * E) i i)
  simp only [hDiag, zero_sub, Finset.sum_neg_distrib]

theorem hamiltonian_bipartite_diagonal_zero (T : Matrix Iota Iota Real)
    (i : Sum Iota Iota) : bipartiteLift T i i = 0 := by
  cases i <;> rfl

theorem hamiltonian_retained_scaling_diagonal_zero
    (T : Matrix Iota Iota Real) (S U : Finset Iota)
    (z : forall _i : (Compl.compl (S.disjSum U) : Finset (Sum Iota Iota)), Real)
    (q qNew : Real) (i : (Compl.compl (S.disjSum U) : Finset (Sum Iota Iota))) :
    hamiltonianScalingPerturbation (hamiltonianRetainedKernel T S U)
      (hamiltonianRetainedCrossMask S U) z q qNew i i = 0 := by
  have hP : hamiltonianRetainedKernel T S U i i = 0 :=
    hamiltonian_bipartite_diagonal_zero T i.val
  have hC : hamiltonianRetainedCrossMask S U i i = 0 :=
    hamiltonian_bipartite_diagonal_zero (fun _ _ : Iota => (1 : Real)) i.val
  rw [hamiltonianScalingPerturbation_entry, hP, hC, mul_zero, mul_zero, add_zero]

end PrimeFactorOscillations

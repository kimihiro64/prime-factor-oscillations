/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianStochasticPeeling

/-! # Exact binary used-edge deletions and fresh perfect-matching extension -/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

variable {Iota : Type*} [Fintype Iota] [DecidableEq Iota]

def hamiltonianUsedEdgeDeletion (P H : Matrix Iota Iota Real) : Matrix Iota Iota Real :=
  fun i j => P i j * H i j

theorem hamiltonian_used_edge_deletion_budgets
    (P H : Matrix Iota Iota Real) (alpha : Real) (ha : 0 <= alpha) (n : Nat)
    (hP : forall i j, 0 <= P i j) (hCap : forall i j, P i j <= alpha)
    (hBinary : forall i j, H i j = 0 \/ H i j = 1)
    (hRows : forall i, Finset.univ.sum (fun j => H i j) = (n : Real))
    (hCols : forall j, Finset.univ.sum (fun i => H i j) = (n : Real)) :
    0 <= (n : Real) * alpha /\
      (forall i j, 0 <= hamiltonianUsedEdgeDeletion P H i j) /\
      (forall i j, hamiltonianUsedEdgeDeletion P H i j <= P i j) /\
      (forall i, Finset.univ.sum (fun j => hamiltonianUsedEdgeDeletion P H i j) <=
        (n : Real) * alpha) /\
      (forall j, Finset.univ.sum (fun i => hamiltonianUsedEdgeDeletion P H i j) <=
        (n : Real) * alpha) := by
  have hH0 (i j : Iota) : 0 <= H i j := by
    rcases hBinary i j with h | h <;> rw [h] <;> norm_num
  have hH1 (i j : Iota) : H i j <= 1 := by
    rcases hBinary i j with h | h <;> rw [h] <;> norm_num
  have hQ0 (i j : Iota) : 0 <= hamiltonianUsedEdgeDeletion P H i j :=
    mul_nonneg (hP i j) (hH0 i j)
  have hQP (i j : Iota) : hamiltonianUsedEdgeDeletion P H i j <= P i j := by
    exact (mul_le_mul_of_nonneg_left (hH1 i j) (hP i j)).trans_eq (mul_one _)
  have hQRows (i : Iota) : Finset.univ.sum
      (fun j => hamiltonianUsedEdgeDeletion P H i j) <= (n : Real) * alpha := by
    calc
      _ <= Finset.univ.sum (fun j => alpha * H i j) :=
        Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_right (hCap i j) (hH0 i j))
      _ = alpha * (n : Real) := by rw [<- Finset.mul_sum, hRows i]
      _ = _ := mul_comm _ _
  have hQCols (j : Iota) : Finset.univ.sum
      (fun i => hamiltonianUsedEdgeDeletion P H i j) <= (n : Real) * alpha := by
    calc
      _ <= Finset.univ.sum (fun i => alpha * H i j) :=
        Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_right (hCap i j) (hH0 i j))
      _ = alpha * (n : Real) := by rw [<- Finset.mul_sum, hCols j]
      _ = _ := mul_comm _ _
  exact And.intro (mul_nonneg (Nat.cast_nonneg _) ha)
    (And.intro hQ0 (And.intro hQP (And.intro hQRows hQCols)))

theorem hamiltonian_repaired_support_is_fresh
    (P H W : Matrix Iota Iota Real) (f : Equiv.Perm Iota)
    (hP : forall i j, 0 <= P i j)
    (hBinary : forall i j, H i j = 0 \/ H i j = 1)
    (hZero : forall i j, W i j = 0 <->
      (P - hamiltonianUsedEdgeDeletion P H) i j = 0)
    (hSupport : forall i, 0 < W i (f i)) :
    forall i, H i (f i) = 0 /\ 0 < P i (f i) := by
  intro i
  have hWNe : Not (W i (f i) = 0) := ne_of_gt (hSupport i)
  have hRemaining : Not ((P - hamiltonianUsedEdgeDeletion P H) i (f i) = 0) :=
    fun h => hWNe ((hZero i (f i)).mpr h)
  have hUsed : Not (H i (f i) = 1) := by
    intro h
    apply hRemaining
    change P i (f i) - P i (f i) * H i (f i) = 0
    rw [h]
    ring
  have hFresh : H i (f i) = 0 := (hBinary i (f i)).resolve_right hUsed
  have hPNe : Not (P i (f i) = 0) := by
    intro h
    apply hRemaining
    change P i (f i) - P i (f i) * H i (f i) = 0
    rw [h]
    ring
  exact And.intro hFresh (lt_of_le_of_ne (hP i (f i)) (Ne.symm hPNe))

theorem hamiltonian_fresh_matching_binary_extension
    (P H : Matrix Iota Iota Real) (f : Equiv.Perm Iota) (n : Nat)
    (hBinary : forall i j, H i j = 0 \/ H i j = 1)
    (hRows : forall i, Finset.univ.sum (fun j => H i j) = (n : Real))
    (hCols : forall j, Finset.univ.sum (fun i => H i j) = (n : Real))
    (hOldSupport : forall i j, P i j = 0 -> H i j = 0)
    (hFresh : forall i, H i (f i) = 0)
    (hNewSupport : forall i, 0 < P i (f i)) :
    (forall i j, (H + hamiltonianPermutationCross f) i j = 0 \/
      (H + hamiltonianPermutationCross f) i j = 1) /\
      (forall i, Finset.univ.sum (fun j => (H + hamiltonianPermutationCross f) i j) =
        ((n + 1 : Nat) : Real)) /\
      (forall j, Finset.univ.sum (fun i => (H + hamiltonianPermutationCross f) i j) =
        ((n + 1 : Nat) : Real)) /\
      (forall i j, P i j = 0 -> (H + hamiltonianPermutationCross f) i j = 0) := by
  have hPerm := hamiltonian_permutation_cross_stochastic f
  have hB (i j : Iota) : (H + hamiltonianPermutationCross f) i j = 0 \/
      (H + hamiltonianPermutationCross f) i j = 1 := by
    by_cases hij : j = f i
    . right
      simpa only [Matrix.add_apply, hamiltonianPermutationCross, hij, ite_true,
        hFresh i, zero_add]
    . simpa only [Matrix.add_apply, hamiltonianPermutationCross, if_neg hij, add_zero]
        using hBinary i j
  have hR (i : Iota) : Finset.univ.sum
      (fun j => (H + hamiltonianPermutationCross f) i j) = ((n + 1 : Nat) : Real) := by
    change Finset.univ.sum (fun j => H i j + hamiltonianPermutationCross f i j) = _
    rw [Finset.sum_add_distrib, hRows i, hPerm.2.1 i, Nat.cast_add, Nat.cast_one]
  have hC (j : Iota) : Finset.univ.sum
      (fun i => (H + hamiltonianPermutationCross f) i j) = ((n + 1 : Nat) : Real) := by
    change Finset.univ.sum (fun i => H i j + hamiltonianPermutationCross f i j) = _
    rw [Finset.sum_add_distrib, hCols j, hPerm.2.2 j, Nat.cast_add, Nat.cast_one]
  have hS (i j : Iota) (hP0 : P i j = 0) :
      (H + hamiltonianPermutationCross f) i j = 0 := by
    have hM0 : hamiltonianPermutationCross f i j = 0 := by
      by_cases hij : j = f i
      . have hBad : P i (f i) = 0 := by simpa only [hij] using hP0
        exact False.elim ((ne_of_gt (hNewSupport i)) hBad)
      . simp only [hamiltonianPermutationCross, if_neg hij]
    simp only [Matrix.add_apply, hOldSupport i j hP0, hM0, zero_add]
  exact And.intro hB (And.intro hR (And.intro hC hS))

end PrimeFactorOscillations

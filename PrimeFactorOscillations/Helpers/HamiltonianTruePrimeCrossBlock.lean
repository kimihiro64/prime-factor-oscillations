/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianPrimeCrossBlock
import PrimeFactorOscillations.Helpers.HamiltonianPrimeRealMatrix

/-! # The actual logarithmically weighted true-prime cross block -/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations.LPF

def hamiltonianTruePrimeCrossBlock (m : Nat) : Matrix (Fin m) (Fin m) Real :=
  fun i j => hamiltonianPrimeRealMatrix (2 * m)
    (hamiltonianParityIndex m (Sum.inl i)) (hamiltonianParityIndex m (Sum.inr j))

theorem hamiltonian_true_prime_cross_reindex (m : Nat) :
    (hamiltonianPrimeRealMatrix (2 * m)).submatrix
      (hamiltonianParityEquiv m) (hamiltonianParityEquiv m) =
      bipartiteLift (hamiltonianTruePrimeCrossBlock m) := by
  ext i j
  cases i with
  | inl i =>
      cases j with
      | inl j =>
          change hamiltonianPrimeRealMatrix (2 * m)
            (hamiltonianParityIndex m (Sum.inl i))
            (hamiltonianParityIndex m (Sum.inl j)) = 0
          apply hamiltonian_prime_real_bipartite
          simp [hamiltonianParityIndex]
      | inr j => rfl
  | inr i =>
      cases j with
      | inl j => exact hamiltonian_prime_real_symmetric _ _ _
      | inr j =>
          change hamiltonianPrimeRealMatrix (2 * m)
            (hamiltonianParityIndex m (Sum.inr i))
            (hamiltonianParityIndex m (Sum.inr j)) = 0
          apply hamiltonian_prime_real_bipartite
          simp [hamiltonianParityIndex]

theorem hamiltonian_true_prime_cross_centered_norm (m : Nat) (hm : 1 <= m) :
    norm (centeredKernel (hamiltonianTruePrimeCrossBlock m) (1 / (m : Real))) =
      norm (hamiltonianPrimeRealMatrix (2 * m) -
        hamiltonianRealConstantParityMatrix (2 * m)) := by
  have heq :
      (hamiltonianPrimeRealMatrix (2 * m) -
        hamiltonianRealConstantParityMatrix (2 * m)).submatrix
          (hamiltonianParityEquiv m) (hamiltonianParityEquiv m) =
      bipartiteLift (centeredKernel (hamiltonianTruePrimeCrossBlock m) (1 / (m : Real))) := by
    change (hamiltonianPrimeRealMatrix (2 * m)).submatrix
      (hamiltonianParityEquiv m) (hamiltonianParityEquiv m) -
      (hamiltonianRealConstantParityMatrix (2 * m)).submatrix
        (hamiltonianParityEquiv m) (hamiltonianParityEquiv m) = _
    rw [hamiltonian_true_prime_cross_reindex,
      hamiltonian_constant_parity_reindex m hm]
    ext i j
    cases i <;> cases j <;>
      simp [bipartiteLift, Matrix.fromBlocks, centeredKernel, averagingKernel,
        Matrix.sub_apply, Matrix.transpose]
  rw [<- hamiltonian_bipartite_lift_norm, <- heq, hamiltonian_reindex_matrix_norm]


theorem hamiltonian_true_prime_cross_row (m : Nat) (i : Fin m) :
    Finset.univ.sum (fun j => hamiltonianTruePrimeCrossBlock m i j) =
      Finset.univ.sum (fun k => hamiltonianPrimeRealMatrix (2 * m)
        (hamiltonianParityIndex m (Sum.inl i)) k) := by
  have h := hamiltonian_sum_reindex (hamiltonianParityEquiv m)
    (fun k => hamiltonianPrimeRealMatrix (2 * m)
      (hamiltonianParityIndex m (Sum.inl i)) k)
  have hs : Finset.univ.sum (fun s => hamiltonianPrimeRealMatrix (2 * m)
      (hamiltonianParityIndex m (Sum.inl i)) (hamiltonianParityEquiv m s)) =
      Finset.univ.sum (fun j => hamiltonianTruePrimeCrossBlock m i j) := by
    change Finset.univ.sum (fun s =>
      ((hamiltonianPrimeRealMatrix (2 * m)).submatrix
        (hamiltonianParityEquiv m) (hamiltonianParityEquiv m)) (Sum.inl i) s) = _
    rw [hamiltonian_true_prime_cross_reindex]
    simp [bipartiteLift, Matrix.fromBlocks, Fintype.sum_sum_type]
  exact hs.symm.trans h

theorem hamiltonian_true_prime_cross_column (m : Nat) (j : Fin m) :
    Finset.univ.sum (fun i => hamiltonianTruePrimeCrossBlock m i j) =
      Finset.univ.sum (fun k => hamiltonianPrimeRealMatrix (2 * m)
        (hamiltonianParityIndex m (Sum.inr j)) k) := by
  have h := hamiltonian_sum_reindex (hamiltonianParityEquiv m)
    (fun k => hamiltonianPrimeRealMatrix (2 * m)
      (hamiltonianParityIndex m (Sum.inr j)) k)
  have hs : Finset.univ.sum (fun s => hamiltonianPrimeRealMatrix (2 * m)
      (hamiltonianParityIndex m (Sum.inr j)) (hamiltonianParityEquiv m s)) =
      Finset.univ.sum (fun i => hamiltonianTruePrimeCrossBlock m i j) := by
    change Finset.univ.sum (fun s =>
      ((hamiltonianPrimeRealMatrix (2 * m)).submatrix
        (hamiltonianParityEquiv m) (hamiltonianParityEquiv m)) (Sum.inr j) s) = _
    rw [hamiltonian_true_prime_cross_reindex]
    simp [bipartiteLift, Matrix.fromBlocks, Matrix.transpose,
      Fintype.sum_sum_type]
  exact hs.symm.trans h

theorem hamiltonian_true_prime_cross_operator_uniform (eps : Real) (hEps : 0 < eps) :
    exists M0 : Nat, And (1 <= M0)
      (forall m : Nat, M0 <= m ->
        norm (centeredKernel (hamiltonianTruePrimeCrossBlock m) (1 / (m : Real))) <=
          (1 / 2 : Real) + eps) := by
  choose N0 hN0 hGap using hamiltonian_prime_real_operator_gap eps hEps
  refine Exists.intro N0 (And.intro hN0 ?_)
  intro m hm
  rw [hamiltonian_true_prime_cross_centered_norm m (hN0.trans hm)]
  exact hGap (2 * m) (by omega)


theorem hamiltonian_true_prime_cross_degree_uniform
    (eps : Real) (hEps : 0 < eps) :
    exists M0 : Nat, 256 <= M0 /\
      forall m : Nat, M0 <= m ->
        (forall i : Fin m,
          abs (Finset.univ.sum (fun j => hamiltonianTruePrimeCrossBlock m i j) - 1) <= eps) /\
        (forall j : Fin m,
          abs (Finset.univ.sum (fun i => hamiltonianTruePrimeCrossBlock m i j) - 1) <= eps) := by
  choose D hD N0 hN0 hDegree using hamiltonian_prime_real_degree_uniform 1
  let E := Nat.ceil (Real.exp (D / eps))
  let M0 := max N0 E
  refine Exists.intro M0 (And.intro (hN0.trans (le_max_left _ _)) ?_)
  intro m hm
  have hn0 : N0 <= 2 * m := by have h := (le_max_left N0 E).trans hm; omega
  have hME : E <= m := (le_max_right N0 E).trans hm
  have hm256 : 256 <= m := hN0.trans ((le_max_left N0 E).trans hm)
  have hmReal : (1 : Real) <= (m : Real) := by exact_mod_cast (show 1 <= m by omega)
  have hExp : Real.exp (D / eps) <= (2 * m : Nat) := by
    have hMEReal : (E : Real) <= (m : Real) := by exact_mod_cast hME
    have hExpM : Real.exp (D / eps) <= (m : Real) :=
      (Nat.le_ceil (Real.exp (D / eps))).trans hMEReal
    push_cast
    linarith only [hExpM, hmReal]
  have hLog : D / eps <= Real.log (2 * m : Nat) := by
    simpa only [Real.log_exp] using
      Real.log_le_log (Real.exp_pos (D / eps)) hExp
  have hLogPos : 0 < Real.log (2 * m : Nat) :=
    (div_pos hD hEps).trans_le hLog
  have hMul := mul_le_mul_of_nonneg_left hLog hEps.le
  have hCancel : eps * (D / eps) = D := by field_simp [ne_of_gt hEps]
  rw [hCancel] at hMul
  have hRatio : D / Real.log (2 * m : Nat) <= eps := by
    calc
      _ <= (eps * Real.log (2 * m : Nat)) / Real.log (2 * m : Nat) :=
        div_le_div_of_nonneg_right hMul hLogPos.le
      _ = _ := by field_simp [ne_of_gt hLogPos]
  constructor
  . intro i
    rw [hamiltonian_true_prime_cross_row]
    have h := hDegree (2 * m) hn0 (hamiltonianParityIndex m (Sum.inl i))
    simp only [pow_one] at h
    exact h.trans hRatio
  . intro j
    rw [hamiltonian_true_prime_cross_column]
    have h := hDegree (2 * m) hn0 (hamiltonianParityIndex m (Sum.inr j))
    simp only [pow_one] at h
    exact h.trans hRatio

end PrimeFactorOscillations.LPF

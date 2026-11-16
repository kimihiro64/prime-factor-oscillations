/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianMatrixGeometry
import PrimeFactorOscillations.Helpers.HamiltonianPrimeLogTransferDecay

/-! # The actual balanced odd/even prime cross block -/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations.LPF

def hamiltonianParityIndex (m : Nat) : Sum (Fin m) (Fin m) -> Fin (2 * m)
  | Sum.inl i => Fin.mk (2 * i.val) (by have h := i.isLt; omega)
  | Sum.inr i => Fin.mk (2 * i.val + 1) (by have h := i.isLt; omega)

theorem hamiltonian_parity_index_bijective (m : Nat) :
    Function.Bijective (hamiltonianParityIndex m) := by
  constructor
  . intro i j h
    have hv := congrArg Fin.val h
    cases i with
    | inl i =>
        cases j with
        | inl j =>
            congr 1
            apply Fin.ext
            change 2 * i.val = 2 * j.val at hv
            omega
        | inr j =>
            change 2 * i.val = 2 * j.val + 1 at hv
            omega
    | inr i =>
        cases j with
        | inl j =>
            change 2 * i.val + 1 = 2 * j.val at hv
            omega
        | inr j =>
            congr 1
            apply Fin.ext
            change 2 * i.val + 1 = 2 * j.val + 1 at hv
            omega
  . intro k
    have hk := k.isLt
    by_cases hp : k.val % 2 = 0
    . refine Exists.intro (Sum.inl (Fin.mk (k.val / 2) ?_)) ?_
      . omega
      . apply Fin.ext
        change 2 * (k.val / 2) = k.val
        omega
    . refine Exists.intro (Sum.inr (Fin.mk (k.val / 2) ?_)) ?_
      . omega
      . apply Fin.ext
        change 2 * (k.val / 2) + 1 = k.val
        omega

def hamiltonianParityEquiv (m : Nat) : Equiv (Sum (Fin m) (Fin m)) (Fin (2 * m)) :=
  Equiv.ofBijective (hamiltonianParityIndex m) (hamiltonian_parity_index_bijective m)

def hamiltonianPrimeCrossBlock (m : Nat) : Matrix (Fin m) (Fin m) Real :=
  fun i j => hamiltonianUnweightedPrimeMatrix (2 * m)
    (hamiltonianParityIndex m (Sum.inl i)) (hamiltonianParityIndex m (Sum.inr j))

theorem hamiltonian_unweighted_prime_bipartite (n : Nat) (i j : Fin n)
    (hParity : i.val % 2 = j.val % 2) :
    hamiltonianUnweightedPrimeMatrix n i j = 0 := by
  classical
  by_cases hij : i = j
  . simp only [hamiltonianUnweightedPrimeMatrix, hij, ite_true]
  . have hNotPrime : Not (Nat.Prime ((i.val + 1) + (j.val + 1))) := by
      intro hp
      cases hp.eq_two_or_odd with
      | inl hTwo =>
          apply hij
          apply Fin.ext
          omega
      | inr hOdd => omega
    simp only [hamiltonianUnweightedPrimeMatrix, hij, hNotPrime, ite_false]

theorem hamiltonian_prime_cross_reindex (m : Nat) :
    (hamiltonianUnweightedPrimeMatrix (2 * m)).submatrix
      (hamiltonianParityEquiv m) (hamiltonianParityEquiv m) =
      bipartiteLift (hamiltonianPrimeCrossBlock m) := by
  ext i j
  cases i with
  | inl i =>
      cases j with
      | inl j =>
          change hamiltonianUnweightedPrimeMatrix (2 * m)
            (hamiltonianParityIndex m (Sum.inl i))
            (hamiltonianParityIndex m (Sum.inl j)) = 0
          apply hamiltonian_unweighted_prime_bipartite
          simp [hamiltonianParityIndex]
      | inr j => rfl
  | inr i =>
      cases j with
      | inl j => exact hamiltonian_unweighted_prime_symmetric _ _ _
      | inr j =>
          change hamiltonianUnweightedPrimeMatrix (2 * m)
            (hamiltonianParityIndex m (Sum.inr i))
            (hamiltonianParityIndex m (Sum.inr j)) = 0
          apply hamiltonian_unweighted_prime_bipartite
          simp [hamiltonianParityIndex]

theorem hamiltonian_constant_parity_reindex (m : Nat) (hm : 1 <= m) :
    (hamiltonianRealConstantParityMatrix (2 * m)).submatrix
      (hamiltonianParityEquiv m) (hamiltonianParityEquiv m) =
      bipartiteLift (fun _ _ : Fin m => (1 : Real) / (m : Real)) := by
  have hm0 : Not ((m : Real) = 0) := by exact_mod_cast (by omega : Not (m = 0))
  ext i j
  cases i <;> cases j <;>
    simp [hamiltonianParityEquiv, hamiltonianParityIndex,
      hamiltonianRealConstantParityMatrix, Matrix.submatrix_apply,
      bipartiteLift, Matrix.fromBlocks, Matrix.transpose, pow_add, pow_mul]
  all_goals field_simp [hm0]
  all_goals ring

theorem hamiltonian_prime_cross_centered_norm (m : Nat) (hm : 1 <= m) :
    norm (centeredKernel (hamiltonianPrimeCrossBlock m) (1 / (m : Real))) =
      norm (hamiltonianUnweightedPrimeMatrix (2 * m) -
        hamiltonianRealConstantParityMatrix (2 * m)) := by
  have heq :
      (hamiltonianUnweightedPrimeMatrix (2 * m) -
        hamiltonianRealConstantParityMatrix (2 * m)).submatrix
          (hamiltonianParityEquiv m) (hamiltonianParityEquiv m) =
      bipartiteLift (centeredKernel (hamiltonianPrimeCrossBlock m) (1 / (m : Real))) := by
    change (hamiltonianUnweightedPrimeMatrix (2 * m)).submatrix
      (hamiltonianParityEquiv m) (hamiltonianParityEquiv m) -
      (hamiltonianRealConstantParityMatrix (2 * m)).submatrix
        (hamiltonianParityEquiv m) (hamiltonianParityEquiv m) = _
    rw [hamiltonian_prime_cross_reindex,
      hamiltonian_constant_parity_reindex m hm]
    ext i j
    cases i <;> cases j <;>
      simp [bipartiteLift, Matrix.fromBlocks, centeredKernel, averagingKernel,
        Matrix.sub_apply, Matrix.transpose]
  rw [<- hamiltonian_bipartite_lift_norm, <- heq, hamiltonian_reindex_matrix_norm]


theorem hamiltonian_prime_cross_row (m : Nat) (i : Fin m) :
    Finset.univ.sum (fun j => hamiltonianPrimeCrossBlock m i j) =
      Finset.univ.sum (fun k => hamiltonianUnweightedPrimeMatrix (2 * m)
        (hamiltonianParityIndex m (Sum.inl i)) k) := by
  have h := hamiltonian_sum_reindex (hamiltonianParityEquiv m)
    (fun k => hamiltonianUnweightedPrimeMatrix (2 * m)
      (hamiltonianParityIndex m (Sum.inl i)) k)
  have hs : Finset.univ.sum (fun s => hamiltonianUnweightedPrimeMatrix (2 * m)
      (hamiltonianParityIndex m (Sum.inl i)) (hamiltonianParityEquiv m s)) =
      Finset.univ.sum (fun j => hamiltonianPrimeCrossBlock m i j) := by
    change Finset.univ.sum (fun s =>
      ((hamiltonianUnweightedPrimeMatrix (2 * m)).submatrix
        (hamiltonianParityEquiv m) (hamiltonianParityEquiv m)) (Sum.inl i) s) = _
    rw [hamiltonian_prime_cross_reindex]
    simp [bipartiteLift, Matrix.fromBlocks, Fintype.sum_sum_type]
  exact hs.symm.trans h

theorem hamiltonian_prime_cross_column (m : Nat) (j : Fin m) :
    Finset.univ.sum (fun i => hamiltonianPrimeCrossBlock m i j) =
      Finset.univ.sum (fun k => hamiltonianUnweightedPrimeMatrix (2 * m)
        (hamiltonianParityIndex m (Sum.inr j)) k) := by
  have h := hamiltonian_sum_reindex (hamiltonianParityEquiv m)
    (fun k => hamiltonianUnweightedPrimeMatrix (2 * m)
      (hamiltonianParityIndex m (Sum.inr j)) k)
  have hs : Finset.univ.sum (fun s => hamiltonianUnweightedPrimeMatrix (2 * m)
      (hamiltonianParityIndex m (Sum.inr j)) (hamiltonianParityEquiv m s)) =
      Finset.univ.sum (fun i => hamiltonianPrimeCrossBlock m i j) := by
    change Finset.univ.sum (fun s =>
      ((hamiltonianUnweightedPrimeMatrix (2 * m)).submatrix
        (hamiltonianParityEquiv m) (hamiltonianParityEquiv m)) (Sum.inr j) s) = _
    rw [hamiltonian_prime_cross_reindex]
    simp [bipartiteLift, Matrix.fromBlocks, Matrix.transpose,
      Fintype.sum_sum_type]
  exact hs.symm.trans h

theorem hamiltonian_prime_cross_formula (m : Nat) (i j : Fin m) :
    hamiltonianPrimeCrossBlock m i j =
      if Nat.Prime (2 * i.val + 2 * j.val + 3)
        then Real.log (2 * m : Nat) / (2 * m : Nat) else 0 := by
  have hne : Not (hamiltonianParityIndex m (Sum.inl i) =
      hamiltonianParityIndex m (Sum.inr j)) := by
    intro h
    have hv := congrArg Fin.val h
    change 2 * i.val = 2 * j.val + 1 at hv
    omega
  have hs : (2 * i.val + 1) + (2 * j.val + 1 + 1) =
      2 * i.val + 2 * j.val + 3 := by omega
  unfold hamiltonianPrimeCrossBlock
  rw [hamiltonianUnweightedPrimeMatrix, if_neg hne]
  simp only [hamiltonianParityIndex, hs]

theorem hamiltonian_prime_cross_nonnegative (m : Nat) (hm : 1 <= m)
    (i j : Fin m) : 0 <= hamiltonianPrimeCrossBlock m i j := by
  rw [hamiltonian_prime_cross_formula]
  split_ifs
  . apply div_nonneg
    . apply Real.log_nonneg
      exact_mod_cast (by omega : 1 <= 2 * m)
    . positivity
  . exact le_refl 0

theorem hamiltonian_prime_cross_entry_bound (m : Nat) (hm : 1 <= m)
    (i j : Fin m) :
    hamiltonianPrimeCrossBlock m i j <= (Real.log (2 * m : Nat) / 2) / (m : Real) := by
  have hL : 0 <= Real.log (2 * m : Nat) := by
    apply Real.log_nonneg
    exact_mod_cast (by omega : 1 <= 2 * m)
  rw [hamiltonian_prime_cross_formula]
  split_ifs
  . apply le_of_eq
    push_cast
    ring
  . exact div_nonneg (div_nonneg hL (by norm_num)) (Nat.cast_nonneg m)

theorem hamiltonian_prime_cross_operator_uniform (eps : Real) (hEps : 0 < eps) :
    exists M0 : Nat, And (1 <= M0)
      (forall m : Nat, M0 <= m ->
        norm (centeredKernel (hamiltonianPrimeCrossBlock m) (1 / (m : Real))) <=
          (1 / 2 : Real) + eps) := by
  choose N0 hN0 hGap using hamiltonian_unweighted_prime_operator_gap eps hEps
  refine Exists.intro N0 (And.intro hN0 ?_)
  intro m hm
  rw [hamiltonian_prime_cross_centered_norm m (hN0.trans hm)]
  exact hGap (2 * m) (by omega)

theorem hamiltonian_prime_cross_degree_uniform (eps : Real) (hEps : 0 < eps) :
    exists M0 : Nat, And (1 <= M0)
      (forall m : Nat, M0 <= m ->
        And (forall i : Fin m,
          abs (Finset.univ.sum (fun j => hamiltonianPrimeCrossBlock m i j) - 1) <= eps)
          (forall j : Fin m,
          abs (Finset.univ.sum (fun i => hamiltonianPrimeCrossBlock m i j) - 1) <= eps)) := by
  choose N0 hN0 hDegree using hamiltonian_unweighted_prime_degree_uniform eps hEps
  refine Exists.intro N0 (And.intro hN0 ?_)
  intro m hm
  constructor
  . intro i
    rw [hamiltonian_prime_cross_row]
    exact hDegree (2 * m) (by omega) _
  . intro j
    rw [hamiltonian_prime_cross_column]
    exact hDegree (2 * m) (by omega) _

theorem hamiltonian_prime_cross_degree_rate (b : Nat) :
    exists D : Real, And (0 < D)
      (exists M0 : Nat, And (256 <= M0)
        (forall m : Nat, M0 <= m ->
          And (forall i : Fin m,
            abs (Finset.univ.sum (fun j => hamiltonianPrimeCrossBlock m i j) - 1) <=
              hamiltonianPrimeLogTransferError (2 * m) +
                D / Real.log (2 * m : Nat) ^ b)
            (forall j : Fin m,
            abs (Finset.univ.sum (fun i => hamiltonianPrimeCrossBlock m i j) - 1) <=
              hamiltonianPrimeLogTransferError (2 * m) +
                D / Real.log (2 * m : Nat) ^ b))) := by
  choose D hD N0 hN0 hDegree using hamiltonian_unweighted_prime_degree_rate b
  refine Exists.intro D (And.intro hD (Exists.intro N0 (And.intro hN0 ?_)))
  intro m hm
  constructor
  . intro i
    rw [hamiltonian_prime_cross_row]
    exact hDegree (2 * m) (by omega) _
  . intro j
    rw [hamiltonian_prime_cross_column]
    exact hDegree (2 * m) (by omega) _

end PrimeFactorOscillations.LPF

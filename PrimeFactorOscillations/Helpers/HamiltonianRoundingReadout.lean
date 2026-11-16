/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianNormalizedRounding
import PrimeFactorOscillations.Helpers.HamiltonianRetainedOperatorBounds

/-! # Spectral and both signed subset readouts on the same rounded matrix -/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations

variable {Iota : Type*} [Fintype Iota] [DecidableEq Iota]

theorem hamiltonian_joint_rounding_readouts
    (S1 S2 : Finset (Sum Iota Iota)) (C : Matrix Iota Iota Real) :
    norm (bipartiteLift C) <= norm (hamiltonianBipartiteJointLift S1 S2 C) /\
      (forall i, abs (S1.sum (fun j => bipartiteLift C i j)) <=
        norm (hamiltonianBipartiteJointLift S1 S2 C)) /\
      (forall i, abs (S2.sum (fun j => bipartiteLift C i j)) <=
        norm (hamiltonianBipartiteJointLift S1 S2 C)) := by
  let M := hamiltonianTwoObservableMatrix S1 S2 (bipartiteLift C)
  have hSpectral := hamiltonian_l2_injective_submatrix_le M Sum.inl
    (fun _ _ h => Sum.inl.inj h)
  have hSpec : norm (bipartiteLift C) <= norm M := by
    rw [hamiltonian_two_observable_spectral_block] at hSpectral
    exact hSpectral
  have hFirst (i : Sum Iota Iota) :
      abs (S1.sum (fun j => bipartiteLift C i j)) <= norm M := by
    have h := l2_matrix_entry_le_norm M (Sum.inr (Sum.inl i)) (Sum.inr (Sum.inl i))
    change norm (hamiltonianTwoObservableMatrix S1 S2 (bipartiteLift C)
      (Sum.inr (Sum.inl i)) (Sum.inr (Sum.inl i))) <= norm M at h
    rw [hamiltonian_two_observable_first_diagonal, Real.norm_eq_abs] at h
    exact h
  have hSecond (i : Sum Iota Iota) :
      abs (S2.sum (fun j => bipartiteLift C i j)) <= norm M := by
    have h := l2_matrix_entry_le_norm M (Sum.inr (Sum.inr i)) (Sum.inr (Sum.inr i))
    change norm (hamiltonianTwoObservableMatrix S1 S2 (bipartiteLift C)
      (Sum.inr (Sum.inr i)) (Sum.inr (Sum.inr i))) <= norm M at h
    rw [hamiltonian_two_observable_second_diagonal, Real.norm_eq_abs] at h
    exact h
  exact And.intro hSpec (And.intro hFirst hSecond)

theorem hamiltonian_bipartite_normalized_entry
    (H P : Matrix Iota Iota Real) (c : Real) (i j : Sum Iota Iota) :
    bipartiteLift (SMul.smul c H - P) i j =
      c * bipartiteLift H i j - bipartiteLift P i j := by
  have hScalar (a b : Iota) : SMul.smul c H a b = c * H a b := rfl
  rcases i with i | i <;> rcases j with j | j <;>
    simp [bipartiteLift, Matrix.fromBlocks, hScalar]

theorem hamiltonian_bipartite_normalized_matrix
    (H P : Matrix Iota Iota Real) (c : Real) :
    bipartiteLift (SMul.smul c H - P) =
      SMul.smul c (bipartiteLift H) - bipartiteLift P := by
  ext i j
  exact hamiltonian_bipartite_normalized_entry H P c i j

theorem hamiltonian_supported_rounding_spectral_and_observables [Nonempty Iota]
    (P : Matrix Iota Iota Real) (S1 S2 : Finset (Sum Iota Iota))
    (delta alpha : Real) (d : Nat) (hd : 1 <= d)
    (hd0 : 0 < delta) (hd1 : delta < 1) (ha : 0 <= alpha)
    (hP : forall i j, 0 <= P i j) (hCap : forall i j, P i j <= alpha)
    (hPRows : forall i, Finset.univ.sum (fun j => P i j) = 1)
    (hPCols : forall j, Finset.univ.sum (fun i => P i j) = 1)
    (hGap : norm (centeredKernel P (1 / (Fintype.card Iota : Real))) <= 1 - delta)
    (hSmall : ((d : Real) * alpha) * Real.log (4 * (Fintype.card Iota : Real)) ^ 2 <=
      hamiltonianForbiddenRepairSmall delta) :
    let E := 16 * Real.sqrt (Real.log (4 * (Fintype.card Iota : Real)) / (d : Real)) +
      hamiltonianRoundingDriftCost Iota delta alpha * (d : Real)
    exists H : Matrix Iota Iota Real,
      (forall i j, H i j = 0 \/ H i j = 1) /\
      (forall i, Finset.univ.sum (fun j => H i j) = (d : Real)) /\
      (forall j, Finset.univ.sum (fun i => H i j) = (d : Real)) /\
      (forall i j, P i j = 0 -> H i j = 0) /\
      norm (SMul.smul (1 / (d : Real)) (bipartiteLift H) - bipartiteLift P) <= E /\
      (forall i, abs ((1 / (d : Real)) * S1.sum (fun j => bipartiteLift H i j) -
        S1.sum (fun j => bipartiteLift P i j)) <= E) /\
      (forall i, abs ((1 / (d : Real)) * S2.sum (fun j => bipartiteLift H i j) -
        S2.sum (fun j => bipartiteLift P i j)) <= E) := by
  intro E
  cases hamiltonian_joint_normalized_rounding P S1 S2 delta alpha d hd
      hd0 hd1 ha hP hCap hPRows hPCols hGap hSmall with
  | intro H hH =>
    have hRead := hamiltonian_joint_rounding_readouts S1 S2
      (SMul.smul (1 / (d : Real)) H - P)
    have hSpec : norm (SMul.smul (1 / (d : Real)) (bipartiteLift H) -
        bipartiteLift P) <= E := by
      rw [<- hamiltonian_bipartite_normalized_matrix]
      exact hRead.1.trans hH.2.2.2.2
    have hFirst (i : Sum Iota Iota) :
        abs ((1 / (d : Real)) * S1.sum (fun j => bipartiteLift H i j) -
          S1.sum (fun j => bipartiteLift P i j)) <= E := by
      have h := (hRead.2.1 i).trans hH.2.2.2.2
      simpa only [hamiltonian_bipartite_normalized_entry,
        Finset.sum_sub_distrib, Finset.mul_sum] using h
    have hSecond (i : Sum Iota Iota) :
        abs ((1 / (d : Real)) * S2.sum (fun j => bipartiteLift H i j) -
          S2.sum (fun j => bipartiteLift P i j)) <= E := by
      have h := (hRead.2.2 i).trans hH.2.2.2.2
      simpa only [hamiltonian_bipartite_normalized_entry,
        Finset.sum_sub_distrib, Finset.mul_sum] using h
    exact Exists.intro H (And.intro hH.1 (And.intro hH.2.1
      (And.intro hH.2.2.1 (And.intro hH.2.2.2.1
        (And.intro hSpec (And.intro hFirst hSecond))))))

end PrimeFactorOscillations

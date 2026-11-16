/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianCountPowerDecay
import PrimeFactorOscillations.Helpers.HamiltonianPrimeFactorEigenvalues

/-! # Actual regular-factor kernels and Hamilton-cycle witnesses

The degree is a free integer. A positive signed relative count produces
an actual one-orbit permutation, with every used edge in the factor.
-/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations.LPF

def hamiltonianRegularFactorCross {m : Nat} (r : Nat)
    (F : Finset (Prod (Fin m) (Fin m))) : Matrix (Fin m) (Fin m) Real :=
  fun i j => (1 / (r : Real)) * (if Membership.mem F (i, j) then 1 else 0)

def hamiltonianRegularNormalizedAdjacency (m r : Nat)
    (F : Finset (Prod (Fin m) (Fin m))) : Matrix (Fin (2 * m)) (Fin (2 * m)) Real :=
  SMul.smul (1 / (r : Real)) (hamiltonianPrimeFactorAdjacency m F)

theorem hamiltonian_regular_factor_cross_lift
    (m r : Nat) (F : Finset (Prod (Fin m) (Fin m))) :
    bipartiteLift (hamiltonianRegularFactorCross r F) =
      SMul.smul (1 / (r : Real)) (hamiltonianFactorAdjacency F) := by
  ext i j
  change bipartiteLift (hamiltonianRegularFactorCross r F) i j =
    (1 / (r : Real)) * hamiltonianFactorAdjacency F i j
  cases i <;> cases j <;>
    simp [bipartiteLift, Matrix.fromBlocks, Matrix.transpose,
      hamiltonianRegularFactorCross, hamiltonianFactorAdjacency]

theorem hamiltonian_regular_factor_normalized_reindex
    (m r : Nat) (F : Finset (Prod (Fin m) (Fin m))) :
    (hamiltonianRegularNormalizedAdjacency m r F).submatrix
      (hamiltonianParityEquiv m) (hamiltonianParityEquiv m) =
      bipartiteLift (hamiltonianRegularFactorCross r F) := by
  rw [hamiltonian_regular_factor_cross_lift]
  ext i j
  change (1 / (r : Real)) * hamiltonianFactorAdjacency F
    ((hamiltonianParityEquiv m).symm ((hamiltonianParityEquiv m) i))
    ((hamiltonianParityEquiv m).symm ((hamiltonianParityEquiv m) j)) =
    (1 / (r : Real)) * hamiltonianFactorAdjacency F i j
  simp only [Equiv.symm_apply_apply]

theorem hamiltonian_regular_factor_cross_stochastic
    (m r : Nat) (hr : 0 < r) (F : Finset (Prod (Fin m) (Fin m)))
    (hLeft : forall i, (F.filter (fun e => e.1 = i)).card = r)
    (hRight : forall j, (F.filter (fun e => e.2 = j)).card = r) :
    And (forall i, Finset.univ.sum (fun j => hamiltonianRegularFactorCross r F i j) = 1)
      (forall j, Finset.univ.sum (fun i => hamiltonianRegularFactorCross r F i j) = 1) := by
  have hr0 : Not ((r : Real) = 0) := ne_of_gt (Nat.cast_pos.mpr hr)
  constructor
  . intro i
    unfold hamiltonianRegularFactorCross
    rw [<- Finset.mul_sum, hamiltonian_factor_left_row_count F i, hLeft i]
    field_simp [hr0]
  . intro j
    unfold hamiltonianRegularFactorCross
    rw [<- Finset.mul_sum, hamiltonian_factor_right_row_count F j, hRight j]
    field_simp [hr0]

theorem hamiltonian_regular_factor_centered_norm
    (m r : Nat) (hm : 1 <= m) (F : Finset (Prod (Fin m) (Fin m))) :
    norm (centeredKernel (hamiltonianRegularFactorCross r F) (1 / (m : Real))) =
      norm (hamiltonianRegularNormalizedAdjacency m r F -
        hamiltonianRealConstantParityMatrix (2 * m)) := by
  have hd :
      (hamiltonianRegularNormalizedAdjacency m r F -
        hamiltonianRealConstantParityMatrix (2 * m)).submatrix
          (hamiltonianParityEquiv m) (hamiltonianParityEquiv m) =
      bipartiteLift (centeredKernel (hamiltonianRegularFactorCross r F) (1 / (m : Real))) := by
    change (hamiltonianRegularNormalizedAdjacency m r F).submatrix
      (hamiltonianParityEquiv m) (hamiltonianParityEquiv m) -
      (hamiltonianRealConstantParityMatrix (2 * m)).submatrix
        (hamiltonianParityEquiv m) (hamiltonianParityEquiv m) = _
    rw [hamiltonian_regular_factor_normalized_reindex, hamiltonian_constant_parity_reindex m hm]
    ext i j
    cases i <;> cases j <;>
      simp [bipartiteLift, Matrix.fromBlocks, Matrix.transpose, centeredKernel,
        averagingKernel, Matrix.sub_apply]
  rw [<- hamiltonian_bipartite_lift_norm, <- hd, hamiltonian_reindex_matrix_norm]

theorem hamiltonian_regular_factor_cycle_witness
    (m r : Nat) (F : Finset (Prod (Fin m) (Fin m)))
    (hRatio : 0 < hamiltonianBipartiteCountRatio (hamiltonianRegularFactorCross r F)) :
    Exists (fun f : Equiv.Perm (Sum (Fin m) (Fin m)) =>
      And ((hamiltonianPermutationOrbits f).card = 1)
        (forall i, Not (hamiltonianFactorAdjacency F (f i) i = 0))) := by
  classical
  let T := hamiltonianRegularFactorCross r F
  have hCycle : 0 < hamiltonianCycleSum (bipartiteLift T) := by
    by_contra h
    have hle : hamiltonianCycleSum (bipartiteLift T) <= 0 := le_of_not_gt h
    have hCoeff : 0 <= ((Fintype.card (Fin m) : Real) ^ Fintype.card (Fin m) /
        ((Fintype.card (Fin m)).factorial : Real)) ^ 2 := sq_nonneg _
    have hNonpos := mul_nonpos_of_nonneg_of_nonpos hCoeff
      (mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg (Fintype.card (Fin m))) hle)
    exact (not_le_of_gt hRatio) hNonpos
  have hSum : 0 < Finset.univ.sum (fun f : Equiv.Perm (Sum (Fin m) (Fin m)) =>
      if (hamiltonianPermutationOrbits f).card = 1 then
        Finset.univ.prod (fun i => bipartiteLift T (f i) i) else 0) := hCycle
  have hWitness : Exists (fun f : Equiv.Perm (Sum (Fin m) (Fin m)) =>
      0 < if (hamiltonianPermutationOrbits f).card = 1 then
        Finset.univ.prod (fun i => bipartiteLift T (f i) i) else 0) := by
    by_contra h
    push Not at h
    have hNonpos : Finset.univ.sum (fun f : Equiv.Perm (Sum (Fin m) (Fin m)) =>
        if (hamiltonianPermutationOrbits f).card = 1 then
          Finset.univ.prod (fun i => bipartiteLift T (f i) i) else 0) <= 0 :=
      Finset.sum_nonpos (fun f _ => h f)
    exact (not_le_of_gt hSum) hNonpos
  choose f hPos using hWitness
  have hOne : (hamiltonianPermutationOrbits f).card = 1 := by
    by_contra h
    simp only [h, ite_false] at hPos
    exact (lt_irrefl (0 : Real)) hPos
  rw [if_pos hOne] at hPos
  refine Exists.intro f (And.intro hOne ?_)
  intro i hi
  have hZero : bipartiteLift T (f i) i = 0 := by
    change bipartiteLift (hamiltonianRegularFactorCross r F) (f i) i = 0
    rw [hamiltonian_regular_factor_cross_lift]
    change (1 / (r : Real)) * hamiltonianFactorAdjacency F (f i) i = 0
    rw [hi, mul_zero]
  have hpZero : Finset.univ.prod (fun j => bipartiteLift T (f j) j) = 0 :=
    Finset.prod_eq_zero (f := fun j => bipartiteLift T (f j) j) (Finset.mem_univ i) hZero
  rw [hpZero] at hPos
  exact (lt_irrefl (0 : Real)) hPos

end PrimeFactorOscillations.LPF

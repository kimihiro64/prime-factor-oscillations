/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianPrimeSharpScaling

/-! # The repaired prime kernel on the original integer vertex set -/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations.LPF

def hamiltonianPrimePhysicalKernel (m : Nat) (z : Sum (Fin m) (Fin m) -> Real) :
    Matrix (Fin (2 * m)) (Fin (2 * m)) Real :=
  (bipartiteLift (hamiltonianScaledCross (hamiltonianPrimeCrossBlock m) z)).submatrix
    (hamiltonianParityEquiv m).symm (hamiltonianParityEquiv m).symm

theorem hamiltonian_prime_original_from_cross (m : Nat) :
    hamiltonianUnweightedPrimeMatrix (2 * m) =
      (bipartiteLift (hamiltonianPrimeCrossBlock m)).submatrix
        (hamiltonianParityEquiv m).symm (hamiltonianParityEquiv m).symm := by
  have h := congrArg
    (fun M : Matrix (Sum (Fin m) (Fin m)) (Sum (Fin m) (Fin m)) Real =>
      M.submatrix (hamiltonianParityEquiv m).symm (hamiltonianParityEquiv m).symm)
    (hamiltonian_prime_cross_reindex m)
  ext i j
  have hp := congrArg (fun M => M i j) h
  simpa only [Matrix.submatrix_apply, Equiv.apply_symm_apply] using hp

theorem hamiltonian_prime_reference_from_cross (m : Nat) (hm : 1 <= m) :
    hamiltonianRealConstantParityMatrix (2 * m) =
      (bipartiteLift (fun _ _ : Fin m => (1 : Real) / (m : Real))).submatrix
        (hamiltonianParityEquiv m).symm (hamiltonianParityEquiv m).symm := by
  have h := congrArg
    (fun M : Matrix (Sum (Fin m) (Fin m)) (Sum (Fin m) (Fin m)) Real =>
      M.submatrix (hamiltonianParityEquiv m).symm (hamiltonianParityEquiv m).symm)
    (hamiltonian_constant_parity_reindex m hm)
  ext i j
  have hp := congrArg (fun M => M i j) h
  simpa only [Matrix.submatrix_apply, Equiv.apply_symm_apply] using hp

theorem hamiltonian_prime_physical_error_norm (m : Nat)
    (z : Sum (Fin m) (Fin m) -> Real) :
    norm (hamiltonianPrimePhysicalKernel m z - hamiltonianUnweightedPrimeMatrix (2 * m)) =
      norm (hamiltonianScaledCross (hamiltonianPrimeCrossBlock m) z -
        hamiltonianPrimeCrossBlock m) := by
  rw [hamiltonian_prime_original_from_cross]
  change norm (((bipartiteLift (hamiltonianScaledCross (hamiltonianPrimeCrossBlock m) z)) -
    bipartiteLift (hamiltonianPrimeCrossBlock m)).submatrix
      (hamiltonianParityEquiv m).symm (hamiltonianParityEquiv m).symm) = _
  rw [hamiltonian_reindex_matrix_norm]
  have hLift :
      bipartiteLift (hamiltonianScaledCross (hamiltonianPrimeCrossBlock m) z) -
        bipartiteLift (hamiltonianPrimeCrossBlock m) =
      bipartiteLift (hamiltonianScaledCross (hamiltonianPrimeCrossBlock m) z -
        hamiltonianPrimeCrossBlock m) := by
    ext i j
    cases i <;> cases j <;> simp [bipartiteLift, Matrix.fromBlocks,
      Matrix.transpose, Matrix.sub_apply]
  rw [hLift, hamiltonian_bipartite_lift_norm]

theorem hamiltonian_prime_physical_centered_norm (m : Nat) (hm : 1 <= m)
    (z : Sum (Fin m) (Fin m) -> Real) :
    norm (hamiltonianPrimePhysicalKernel m z - hamiltonianRealConstantParityMatrix (2 * m)) =
      norm (centeredKernel (hamiltonianScaledCross (hamiltonianPrimeCrossBlock m) z)
        (1 / (m : Real))) := by
  rw [hamiltonian_prime_reference_from_cross m hm]
  change norm (((bipartiteLift (hamiltonianScaledCross (hamiltonianPrimeCrossBlock m) z)) -
    bipartiteLift (fun _ _ : Fin m => (1 : Real) / (m : Real))).submatrix
      (hamiltonianParityEquiv m).symm (hamiltonianParityEquiv m).symm) = _
  rw [hamiltonian_reindex_matrix_norm]
  have hLift :
      bipartiteLift (hamiltonianScaledCross (hamiltonianPrimeCrossBlock m) z) -
        bipartiteLift (fun _ _ : Fin m => (1 : Real) / (m : Real)) =
      bipartiteLift (centeredKernel
        (hamiltonianScaledCross (hamiltonianPrimeCrossBlock m) z) (1 / (m : Real))) := by
    ext i j
    cases i <;> cases j <;> simp [bipartiteLift, Matrix.fromBlocks,
      Matrix.transpose, Matrix.sub_apply, centeredKernel, averagingKernel]
  rw [hLift, hamiltonian_bipartite_lift_norm]

theorem hamiltonian_prime_physical_stochastic (m : Nat)
    (z : Sum (Fin m) (Fin m) -> Real)
    (hRows : forall i, Finset.univ.sum (fun j =>
      hamiltonianScaledCross (hamiltonianPrimeCrossBlock m) z i j) = 1)
    (hCols : forall j, Finset.univ.sum (fun i =>
      hamiltonianScaledCross (hamiltonianPrimeCrossBlock m) z i j) = 1)
    (i : Fin (2 * m)) :
    Finset.univ.sum (fun j => hamiltonianPrimePhysicalKernel m z i j) = 1 := by
  have hLift (s : Sum (Fin m) (Fin m)) :
      Finset.univ.sum (fun t =>
        bipartiteLift (hamiltonianScaledCross (hamiltonianPrimeCrossBlock m) z) s t) = 1 := by
    cases s with
    | inl s => simpa [bipartiteLift, Matrix.fromBlocks, Fintype.sum_sum_type] using hRows s
    | inr s => simpa [bipartiteLift, Matrix.fromBlocks, Matrix.transpose,
        Fintype.sum_sum_type] using hCols s
  calc
    _ = Finset.univ.sum (fun s =>
        bipartiteLift (hamiltonianScaledCross (hamiltonianPrimeCrossBlock m) z)
          ((hamiltonianParityEquiv m).symm i) s) :=
      hamiltonian_sum_reindex (hamiltonianParityEquiv m).symm _
    _ = 1 := hLift _

theorem hamiltonian_prime_physical_symmetric (m : Nat)
    (z : Sum (Fin m) (Fin m) -> Real) (i j : Fin (2 * m)) :
    hamiltonianPrimePhysicalKernel m z i j = hamiltonianPrimePhysicalKernel m z j i := by
  let s := (hamiltonianParityEquiv m).symm i
  let t := (hamiltonianParityEquiv m).symm j
  change bipartiteLift _ s t = bipartiteLift _ t s
  cases s <;> cases t <;> rfl

theorem hamiltonian_prime_physical_support (m : Nat)
    (z : Sum (Fin m) (Fin m) -> Real)
    (hSupport : forall i j, hamiltonianScaledCross (hamiltonianPrimeCrossBlock m) z i j = 0 <->
      hamiltonianPrimeCrossBlock m i j = 0)
    (i j : Fin (2 * m)) :
    hamiltonianPrimePhysicalKernel m z i j = 0 <->
      hamiltonianUnweightedPrimeMatrix (2 * m) i j = 0 := by
  rw [hamiltonian_prime_original_from_cross]
  let s := (hamiltonianParityEquiv m).symm i
  let t := (hamiltonianParityEquiv m).symm j
  change bipartiteLift (hamiltonianScaledCross (hamiltonianPrimeCrossBlock m) z) s t = 0 <->
    bipartiteLift (hamiltonianPrimeCrossBlock m) s t = 0
  cases s <;> cases t <;>
    simp [bipartiteLift, Matrix.fromBlocks, Matrix.transpose, hSupport]

theorem hamiltonian_prime_physical_nonnegative (m : Nat)
    (z : Sum (Fin m) (Fin m) -> Real)
    (hNonneg : forall i j, 0 <= hamiltonianScaledCross (hamiltonianPrimeCrossBlock m) z i j)
    (i j : Fin (2 * m)) : 0 <= hamiltonianPrimePhysicalKernel m z i j := by
  let s := (hamiltonianParityEquiv m).symm i
  let t := (hamiltonianParityEquiv m).symm j
  change 0 <= bipartiteLift (hamiltonianScaledCross (hamiltonianPrimeCrossBlock m) z) s t
  cases s <;> cases t <;>
    simp [bipartiteLift, Matrix.fromBlocks, Matrix.transpose, hNonneg]

theorem hamiltonian_prime_physical_sharp_uniform (eps : Real) (hEps : 0 < eps) :
    exists M0 : Nat, And (256 <= M0)
      (forall m : Nat, M0 <= m ->
        exists z : Sum (Fin m) (Fin m) -> Real,
          norm z <= eps /\
          (forall i, 0 < 1 + z i) /\
          (forall i j, 0 <= hamiltonianPrimePhysicalKernel m z i j) /\
          (forall i, Finset.univ.sum (fun j => hamiltonianPrimePhysicalKernel m z i j) = 1) /\
          (forall i j, hamiltonianPrimePhysicalKernel m z i j = hamiltonianPrimePhysicalKernel m z j i) /\
          (forall i j, hamiltonianPrimePhysicalKernel m z i j = 0 <->
            hamiltonianUnweightedPrimeMatrix (2 * m) i j = 0) /\
          norm (hamiltonianPrimePhysicalKernel m z - hamiltonianUnweightedPrimeMatrix (2 * m)) <= eps /\
          norm (hamiltonianPrimePhysicalKernel m z - hamiltonianRealConstantParityMatrix (2 * m)) <=
            (1 / 2 : Real) + eps) := by
  choose M0 hM0 hScale using hamiltonian_prime_cross_sharp_scaling eps hEps
  refine Exists.intro M0 (And.intro hM0 ?_)
  intro m hm
  have hmPos : 1 <= m := by omega
  choose z hZ hPos hNonneg hRows hCols hSupport hCap hError hGap hCount using hScale m hm
  refine Exists.intro z (And.intro hZ (And.intro hPos ?_))
  refine And.intro (hamiltonian_prime_physical_nonnegative m z hNonneg) ?_
  refine And.intro (hamiltonian_prime_physical_stochastic m z hRows hCols) ?_
  refine And.intro (hamiltonian_prime_physical_symmetric m z) ?_
  refine And.intro (hamiltonian_prime_physical_support m z hSupport) ?_
  rw [hamiltonian_prime_physical_error_norm, hamiltonian_prime_physical_centered_norm m hmPos]
  exact And.intro hError hGap

end PrimeFactorOscillations.LPF

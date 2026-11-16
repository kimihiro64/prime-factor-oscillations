/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianGaussianSpectralRealization
import PrimeFactorOscillations.Helpers.HamiltonianJointObservableLift
import PrimeFactorOscillations.Helpers.HamiltonianLinearMatchingDirection

/-! # Actual supported matching steps for the joint spectral/observable packet -/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations

variable {Iota : Type*} [Fintype Iota] [DecidableEq Iota]

def hamiltonianBipartiteLinearLift :
    LinearMap (RingHom.id Real) (Matrix Iota Iota Real)
      (Matrix (Sum Iota Iota) (Sum Iota Iota) Real) where
  toFun P := bipartiteLift P
  map_add' P Q := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      simp [bipartiteLift, Matrix.fromBlocks]
  map_smul' r P := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      simp [bipartiteLift, Matrix.fromBlocks, smul_eq_mul]

def hamiltonianBipartiteJointLift (S1 S2 : Finset (Sum Iota Iota)) :
    LinearMap (RingHom.id Real) (Matrix Iota Iota Real)
      (Matrix (Sum (Sum Iota Iota) (Sum (Sum Iota Iota) (Sum Iota Iota)))
        (Sum (Sum Iota Iota) (Sum (Sum Iota Iota) (Sum Iota Iota))) Real) :=
  (hamiltonianTwoObservableLift S1 S2).comp hamiltonianBipartiteLinearLift

theorem hamiltonian_bipartite_lift_symmetric (P : Matrix Iota Iota Real) :
    forall i j, bipartiteLift P i j = bipartiteLift P j i := by
  intro i j
  rcases i with i | i <;> rcases j with j | j <;> rfl

theorem hamiltonian_stochastic_bipartite_absolute_rows
    (P : Matrix Iota Iota Real) (hP : forall i j, 0 <= P i j)
    (hRows : forall i, Finset.univ.sum (fun j => P i j) = 1)
    (hCols : forall j, Finset.univ.sum (fun i => P i j) = 1) :
    forall i, Finset.univ.sum (fun j => abs (bipartiteLift P i j)) = 1 := by
  have hAbs (i j : Iota) : abs (P i j) = P i j := abs_of_nonneg (hP i j)
  intro i
  rcases i with i | i
  . simpa [bipartiteLift, Matrix.fromBlocks, Fintype.sum_sum_type, hAbs] using hRows i
  . simpa [bipartiteLift, Matrix.fromBlocks, Fintype.sum_sum_type, hAbs] using hCols i

theorem hamiltonian_stochastic_bipartite_joint_norm
    (S1 S2 : Finset (Sum Iota Iota))
    (P : Matrix Iota Iota Real) (hP : forall i j, 0 <= P i j)
    (hRows : forall i, Finset.univ.sum (fun j => P i j) = 1)
    (hCols : forall j, Finset.univ.sum (fun i => P i j) = 1) :
    norm (hamiltonianBipartiteJointLift S1 S2 P) <= 1 := by
  exact hamiltonian_two_observable_norm_from_rows S1 S2 (bipartiteLift P)
    (hamiltonian_bipartite_lift_symmetric P) 1 (by norm_num)
    (fun i => (hamiltonian_stochastic_bipartite_absolute_rows P hP hRows hCols i).le)

theorem hamiltonian_bipartite_joint_hermitian
    (S1 S2 : Finset (Sum Iota Iota)) (P : Matrix Iota Iota Real) :
    (hamiltonianBipartiteJointLift S1 S2 P).IsHermitian :=
  hamiltonian_two_observable_hermitian S1 S2 (bipartiteLift P) (bipartiteLift_hermitian P)

theorem hamiltonian_supported_joint_matching_direction [Nonempty Iota]
    (S1 S2 : Finset (Sum Iota Iota))
    (Z : Matrix (Sum (Sum Iota Iota) (Sum (Sum Iota Iota) (Sum Iota Iota)))
      (Sum (Sum Iota Iota) (Sum (Sum Iota Iota) (Sum Iota Iota))) Real)
    (p : Nat) (P : Matrix Iota Iota Real) (hP : forall i j, 0 <= P i j)
    (hRows : forall i, Finset.univ.sum (fun j => P i j) = 1)
    (hCols : forall j, Finset.univ.sum (fun i => P i j) = 1) :
    exists f : Equiv.Perm Iota, (forall i, 0 < P i (f i)) /\
      let X := hamiltonianBipartiteJointLift S1 S2 (hamiltonianPermutationCross f - P)
      X.IsHermitian /\ norm X <= 2 /\ Matrix.trace (Z ^ p.pred * X) <= 0 := by
  let L := hamiltonianBipartiteJointLift S1 S2
  choose f hSupport hDirection using hamiltonian_stochastic_matching_trace_direction
    (Z ^ p.pred) L P hP hRows hCols
  have hPerm := hamiltonian_permutation_cross_stochastic f
  have hN1 : norm (L (hamiltonianPermutationCross f)) <= 1 :=
    hamiltonian_stochastic_bipartite_joint_norm S1 S2 _ hPerm.1 hPerm.2.1 hPerm.2.2
  have hN2 : norm (L P) <= 1 :=
    hamiltonian_stochastic_bipartite_joint_norm S1 S2 P hP hRows hCols
  have hNorm : norm (L (hamiltonianPermutationCross f - P)) <= 2 := by
    rw [map_sub]
    exact (norm_sub_le _ _).trans (by linarith only [hN1, hN2])
  refine Exists.intro f (And.intro hSupport ?_)
  exact And.intro (hamiltonian_bipartite_joint_hermitian S1 S2 _)
    (And.intro hNorm hDirection)

end PrimeFactorOscillations

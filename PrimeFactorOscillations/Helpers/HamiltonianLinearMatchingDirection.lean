/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.LinearAlgebra.Matrix.Trace
import PrimeFactorOscillations.Helpers.HamiltonianMatchingCostSelection

/-! # Supported matchings controlling the exact derivative of any linear lift -/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

variable {Iota : Type*} [Fintype Iota] [DecidableEq Iota]

theorem hamiltonian_matrix_coordinate_expansion (B : Matrix Iota Iota Real) :
    B = Finset.univ.sum (fun i => Finset.univ.sum
      (fun j => SMul.smul (B i j) (Matrix.single i j (1 : Real)))) := by
  ext a b
  simp only [Matrix.sum_apply]
  change B a b = Finset.univ.sum (fun i => Finset.univ.sum
    (fun j => B i j * Matrix.single i j (1 : Real) a b))
  simp [Matrix.single, mul_ite, ite_and]

theorem hamiltonian_matrix_linear_cost_representation
    (phi : LinearMap (RingHom.id Real) (Matrix Iota Iota Real) Real)
    (B : Matrix Iota Iota Real) :
    phi B = hamiltonianCrossCost (fun i j => phi (Matrix.single i j (1 : Real))) B := by
  calc
    _ = phi (Finset.univ.sum (fun i => Finset.univ.sum
        (fun j => SMul.smul (B i j) (Matrix.single i j (1 : Real))))) :=
      congrArg phi (hamiltonian_matrix_coordinate_expansion B)
    _ = _ := by
      simp only [map_sum]
      unfold hamiltonianCrossCost
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      simpa only [RingHom.id_apply, smul_eq_mul, mul_comm] using!
        phi.map_smul (B i j) (Matrix.single i j (1 : Real))

theorem hamiltonian_stochastic_matching_linear_direction [Nonempty Iota]
    (phi : LinearMap (RingHom.id Real) (Matrix Iota Iota Real) Real)
    (P : Matrix Iota Iota Real) (hP : forall i j, 0 <= P i j)
    (hRows : forall i, Finset.univ.sum (fun j => P i j) = 1)
    (hCols : forall j, Finset.univ.sum (fun i => P i j) = 1) :
    exists f : Equiv.Perm Iota, (forall i, 0 < P i (f i)) /\
      phi (hamiltonianPermutationCross f - P) <= 0 := by
  let C : Matrix Iota Iota Real := fun i j => phi (Matrix.single i j (1 : Real))
  choose f hSupport hCost using
    hamiltonian_stochastic_matching_nonpositive_direction C P hP hRows hCols
  refine Exists.intro f (And.intro hSupport ?_)
  rw [hamiltonian_matrix_linear_cost_representation]
  exact hCost

variable {Kappa : Type*} [Fintype Kappa] [DecidableEq Kappa]

def hamiltonianTraceLiftFunctional
    (A : Matrix Kappa Kappa Real)
    (L : LinearMap (RingHom.id Real) (Matrix Iota Iota Real) (Matrix Kappa Kappa Real)) :
    LinearMap (RingHom.id Real) (Matrix Iota Iota Real) Real where
  toFun B := Matrix.trace (A * L B)
  map_add' B C := by rw [map_add, Matrix.mul_add, Matrix.trace_add]
  map_smul' r B := by
    simp only [map_smul, Matrix.mul_smul, Matrix.trace_smul, RingHom.id_apply]

theorem hamiltonian_stochastic_matching_trace_direction [Nonempty Iota]
    (A : Matrix Kappa Kappa Real)
    (L : LinearMap (RingHom.id Real) (Matrix Iota Iota Real) (Matrix Kappa Kappa Real))
    (P : Matrix Iota Iota Real) (hP : forall i j, 0 <= P i j)
    (hRows : forall i, Finset.univ.sum (fun j => P i j) = 1)
    (hCols : forall j, Finset.univ.sum (fun i => P i j) = 1) :
    exists f : Equiv.Perm Iota, (forall i, 0 < P i (f i)) /\
      Matrix.trace (A * L (hamiltonianPermutationCross f - P)) <= 0 := by
  exact hamiltonian_stochastic_matching_linear_direction
    (hamiltonianTraceLiftFunctional A L) P hP hRows hCols

end PrimeFactorOscillations

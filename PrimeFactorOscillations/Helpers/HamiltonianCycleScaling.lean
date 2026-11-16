/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianEntropy

/-! # Exact Hamiltonian cycle weights under positive vertex scaling -/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

variable {Iota : Type*} [Fintype Iota] [DecidableEq Iota]

def hamiltonianVertexScaled (M : Matrix Iota Iota Real) (w : Iota -> Real) :
    Matrix Iota Iota Real := fun i j => w i * M i j * w j

theorem hamiltonian_cycle_sum_vertex_scaling
    (M : Matrix Iota Iota Real) (w : Iota -> Real) :
    hamiltonianCycleSum (hamiltonianVertexScaled M w) =
      (Finset.univ.prod w) ^ 2 * hamiltonianCycleSum M := by
  classical
  unfold hamiltonianCycleSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro f hf
  by_cases h : (hamiltonianPermutationOrbits f).card = 1
  . simp only [h, ite_true, hamiltonianVertexScaled, Finset.prod_mul_distrib]
    rw [Equiv.prod_comp f w]
    ring
  . simp only [h, ite_false, mul_zero]

def hamiltonianCrossScaled (T : Matrix Iota Iota Real) (x y : Iota -> Real) :
    Matrix Iota Iota Real := fun i j => x i * T i j * y j

theorem hamiltonian_cross_scaled_lift
    (T : Matrix Iota Iota Real) (x y : Iota -> Real) :
    bipartiteLift (hamiltonianCrossScaled T x y) =
      hamiltonianVertexScaled (bipartiteLift T) (Sum.elim x y) := by
  ext i j
  cases i <;> cases j <;>
    simp [bipartiteLift, Matrix.fromBlocks, Matrix.transpose,
      hamiltonianCrossScaled, hamiltonianVertexScaled, mul_comm, mul_left_comm, mul_assoc]

theorem hamiltonian_cycle_sum_cross_scaling
    (T : Matrix Iota Iota Real) (x y : Iota -> Real) :
    hamiltonianCycleSum (bipartiteLift (hamiltonianCrossScaled T x y)) =
      (Finset.univ.prod x * Finset.univ.prod y) ^ 2 *
        hamiltonianCycleSum (bipartiteLift T) := by
  rw [hamiltonian_cross_scaled_lift, hamiltonian_cycle_sum_vertex_scaling]
  simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr]

theorem hamiltonian_positive_product_exp (w : Iota -> Real) (hw : forall i, 0 < w i) :
    Finset.univ.prod w = Real.exp (Finset.univ.sum (fun i => Real.log (w i))) := by
  rw [Real.exp_sum]
  apply Finset.prod_congr rfl
  intro i hi
  exact (Real.exp_log (hw i)).symm

theorem hamiltonian_cycle_sum_entropy_scaling
    (T : Matrix Iota Iota Real) (x y : Iota -> Real) (H : Real)
    (hx : forall i, 0 < x i) (hy : forall i, 0 < y i)
    (hH : H = -Finset.univ.sum (fun i => Real.log (x i)) -
      Finset.univ.sum (fun i => Real.log (y i))) :
    hamiltonianCycleSum (bipartiteLift (hamiltonianCrossScaled T x y)) =
      Real.exp (-2 * H) * hamiltonianCycleSum (bipartiteLift T) := by
  rw [hamiltonian_cycle_sum_cross_scaling,
    hamiltonian_positive_product_exp x hx, hamiltonian_positive_product_exp y hy]
  have hExp : (Real.exp (Finset.univ.sum (fun i => Real.log (x i))) *
      Real.exp (Finset.univ.sum (fun i => Real.log (y i)))) ^ 2 = Real.exp (-2 * H) := by
    rw [<- Real.exp_add]
    rw [pow_two, <- Real.exp_add]
    congr 1
    linarith only [hH]
  rw [hExp]

end PrimeFactorOscillations

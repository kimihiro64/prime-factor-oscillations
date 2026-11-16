/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianAperiodicCount
import PrimeFactorOscillations.Helpers.HamiltonianCycleOrientation
import PrimeFactorOscillations.Helpers.HamiltonianSymmetricDeterminantRatio

/-! # Actual unoriented graph counts under positive vertex scaling

Every graph cycle is counted through its reversal class. The exact
vertex gauge and the symmetric determinant quotient are transported
before any asymptotic comparison is applied.
-/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations

variable {Iota : Type*} [Fintype Iota] [DecidableEq Iota]

def hamiltonianGraphUnorientedCount (R : Iota -> Iota -> Prop) : Nat :=
  (hamiltonianUnorientedCycles R).card

def hamiltonianGraphScaledKernel (R : Iota -> Iota -> Prop) [DecidableRel R]
    (u : Iota -> Real) : Matrix Iota Iota Real :=
  hamiltonianVertexScaled (fun i j => if R i j then 1 else 0) u

def hamiltonianGraphLogGauge (u : Iota -> Real) : Real :=
  Finset.univ.sum (fun i => Real.log (u i))

theorem hamiltonian_graph_cycle_weight
    (R : Iota -> Iota -> Prop) [DecidableRel R] (u : Iota -> Real)
    (hSym : forall i j, R i j -> R j i) (hCard : 3 <= Fintype.card Iota)
    (hPos : forall i, 0 < u i) :
    hamiltonianCycleSum (hamiltonianGraphScaledKernel R u) =
      Real.exp (2 * hamiltonianGraphLogGauge u) *
        (2 * (hamiltonianGraphUnorientedCount R : Real)) := by
  have hCount :
      hamiltonianCycleSum (fun i j => if R i j then (1 : Real) else 0) =
        2 * (hamiltonianGraphUnorientedCount R : Real) := by
    rw [hamiltonian_indicator_cycle_count]
    exact_mod_cast hamiltonian_unoriented_cycle_card R hSym hCard
  unfold hamiltonianGraphScaledKernel
  rw [hamiltonian_cycle_sum_vertex_scaling
    (show Matrix Iota Iota Real from fun i j => if R i j then 1 else 0) u,
    hCount, hamiltonian_positive_product_exp u hPos]
  have hExp : (Real.exp (hamiltonianGraphLogGauge u)) ^ 2 =
      Real.exp (2 * hamiltonianGraphLogGauge u) := by
    rw [pow_two, <- Real.exp_add]
    congr 1
    ring
  rw [show Finset.univ.sum (fun i => Real.log (u i)) =
    hamiltonianGraphLogGauge u from rfl, hExp]

theorem hamiltonian_graph_entropy_gauge_ratio
    (R : Iota -> Iota -> Prop) [DecidableRel R] (u : Iota -> Real)
    (hSym : forall i j, R i j -> R j i) (hCard : 3 <= Fintype.card Iota)
    (hPos : forall i, 0 < u i) (H : Real) (hH : Not (H = 0)) :
    (hamiltonianGraphUnorientedCount R : Real) /
        (H * Real.exp (-2 * hamiltonianGraphLogGauge u)) =
      (hamiltonianCycleSum (hamiltonianGraphScaledKernel R u) / 2) / H := by
  rw [hamiltonian_graph_cycle_weight R u hSym hCard hPos]
  have hNeg : Real.exp (-2 * hamiltonianGraphLogGauge u) =
      1 / Real.exp (2 * hamiltonianGraphLogGauge u) := by
    rw [show -2 * hamiltonianGraphLogGauge u =
      -(2 * hamiltonianGraphLogGauge u) by ring, Real.exp_neg]
    exact (one_div _).symm
  rw [hNeg]
  field_simp
  <;> ring

theorem hamiltonian_graph_scaled_symmetric
    (R : Iota -> Iota -> Prop) [DecidableRel R] (u : Iota -> Real)
    (hSym : forall i j, R i j -> R j i) :
    (hamiltonianGraphScaledKernel R u).transpose = hamiltonianGraphScaledKernel R u := by
  ext i j
  change u j * (if R j i then (1 : Real) else 0) * u i =
    u i * (if R i j then (1 : Real) else 0) * u j
  have hIff : R j i <-> R i j := Iff.intro (hSym j i) (hSym i j)
  simp only [hIff]
  ring

theorem hamiltonian_graph_centered_symmetric
    (R : Iota -> Iota -> Prop) [DecidableRel R] (u : Iota -> Real) (q : Real)
    (hSym : forall i j, R i j -> R j i) :
    (centeredKernel (hamiltonianGraphScaledKernel R u) q).transpose =
      centeredKernel (hamiltonianGraphScaledKernel R u) q := by
  unfold centeredKernel
  rw [Matrix.transpose_sub, hamiltonian_graph_scaled_symmetric R u hSym,
    averagingKernel_transpose]

def hamiltonianGraphEntropyReference
    (R : Iota -> Iota -> Prop) [DecidableRel R] (u : Iota -> Real) (q : Real) : Real :=
  (((Fintype.card Iota - 1).factorial : Real) /
      (2 * (Fintype.card Iota : Real) ^ Fintype.card Iota)) *
    Real.exp (-2 * hamiltonianGraphLogGauge u) *
      Real.sqrt
        (Matrix.det ((1 : Matrix Iota Iota Real) -
            centeredKernel (hamiltonianGraphScaledKernel R u) q) /
          Matrix.det ((1 : Matrix Iota Iota Real) +
            centeredKernel (hamiltonianGraphScaledKernel R u) q))

theorem hamiltonian_graph_entropy_reference_identity
    (R : Iota -> Iota -> Prop) [DecidableRel R] (u : Iota -> Real) (q rho : Real)
    (hSym : forall i j, R i j -> R j i) (hCard : 3 <= Fintype.card Iota)
    (hRho : rho < 1) (hNorm : norm (centeredKernel (hamiltonianGraphScaledKernel R u) q) <= rho) :
    hamiltonianGraphEntropyReference R u q =
      (hamiltonianAperiodicCycleReference (hamiltonianGraphScaledKernel R u) q / 2) *
        Real.exp (-2 * hamiltonianGraphLogGauge u) := by
  letI : Nonempty Iota := Fintype.card_pos_iff.mp (by omega)
  have hnPos : 0 < (Fintype.card Iota : Real) := by
    exact_mod_cast (show 0 < Fintype.card Iota by omega)
  have hFactor := hamiltonian_symmetric_gram_factor_quotient
    (centeredKernel (hamiltonianGraphScaledKernel R u) q)
    (hamiltonian_graph_centered_symmetric R u q hSym) rho hRho hNorm
  unfold hamiltonianGraphEntropyReference hamiltonianAperiodicCycleReference
  rw [<- hFactor]
  field_simp
  <;> ring

theorem hamiltonian_graph_aperiodic_entropy_ratio
    (R : Iota -> Iota -> Prop) [DecidableRel R] (u : Iota -> Real) (q rho : Real)
    (hSym : forall i j, R i j -> R j i) (hCard : 3 <= Fintype.card Iota)
    (hPos : forall i, 0 < u i) (hRho : rho < 1)
    (hNorm : norm (centeredKernel (hamiltonianGraphScaledKernel R u) q) <= rho)
    (hReference : Not (hamiltonianAperiodicCycleReference (hamiltonianGraphScaledKernel R u) q = 0)) :
    (hamiltonianGraphUnorientedCount R : Real) / hamiltonianGraphEntropyReference R u q =
      hamiltonianCycleSum (hamiltonianGraphScaledKernel R u) /
        hamiltonianAperiodicCycleReference (hamiltonianGraphScaledKernel R u) q := by
  rw [hamiltonian_graph_entropy_reference_identity R u q rho hSym hCard hRho hNorm]
  have hHalf : Not (hamiltonianAperiodicCycleReference (hamiltonianGraphScaledKernel R u) q / 2 = 0) :=
    div_ne_zero hReference (by norm_num)
  rw [hamiltonian_graph_entropy_gauge_ratio R u hSym hCard hPos _ hHalf]
  field_simp
  <;> ring

theorem hamiltonian_graph_bipartite_pi_ratio
    {m : Nat} (R : Sum (Fin m) (Fin m) -> Sum (Fin m) (Fin m) -> Prop)
    [DecidableRel R] (u : Sum (Fin m) (Fin m) -> Real)
    (T : Matrix (Fin m) (Fin m) Real) (hm : 2 <= m)
    (hSym : forall i j, R i j -> R j i) (hPos : forall i, 0 < u i)
    (hBlock : hamiltonianGraphScaledKernel R u = bipartiteLift T) :
    (hamiltonianGraphUnorientedCount R : Real) /
        (Real.pi * Real.exp (-2 * (m : Real) - 2 * hamiltonianGraphLogGauge u)) =
      (hamiltonianCycleSum (bipartiteLift T) / 2) /
        (Real.pi * Real.exp (-2 * (m : Real))) := by
  have hCard : 3 <= Fintype.card (Sum (Fin m) (Fin m)) := by
    simp only [Fintype.card_sum, Fintype.card_fin]
    omega
  have hH : Not (Real.pi * Real.exp (-2 * (m : Real)) = 0) :=
    ne_of_gt (mul_pos Real.pi_pos (Real.exp_pos _))
  have h := hamiltonian_graph_entropy_gauge_ratio R u hSym hCard hPos
    (Real.pi * Real.exp (-2 * (m : Real))) hH
  rw [hBlock] at h
  have hDen : (Real.pi * Real.exp (-2 * (m : Real))) *
      Real.exp (-2 * hamiltonianGraphLogGauge u) =
        Real.pi * Real.exp (-2 * (m : Real) - 2 * hamiltonianGraphLogGauge u) := by
    rw [mul_assoc, <- Real.exp_add]
    congr 1
    ring
  rw [hDen] at h
  exact h

end PrimeFactorOscillations

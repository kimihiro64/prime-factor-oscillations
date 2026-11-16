/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianBipartiteRoundingStep
import PrimeFactorOscillations.Helpers.HamiltonianForbiddenObservableDrift
import PrimeFactorOscillations.Helpers.HamiltonianUsedEdgeMass

/-! # One original-kernel used-edge repair with a fresh joint signed direction -/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations

variable {Iota : Type*} [Fintype Iota] [DecidableEq Iota]

theorem hamiltonian_bipartite_joint_absolute_mass
    (S1 S2 : Finset (Sum Iota Iota)) (D : Matrix Iota Iota Real)
    (b : Real) (hb : 0 <= b)
    (hRows : forall i, Finset.univ.sum (fun j => abs (D i j)) <= b)
    (hCols : forall j, Finset.univ.sum (fun i => abs (D i j)) <= b) :
    norm (hamiltonianBipartiteJointLift S1 S2 D) <= b := by
  apply hamiltonian_two_observable_norm_from_rows S1 S2 (bipartiteLift D)
    (hamiltonian_bipartite_lift_symmetric D) b hb
  intro i
  rcases i with i | i
  . simpa [bipartiteLift, Matrix.fromBlocks, Fintype.sum_sum_type] using hRows i
  . simpa [bipartiteLift, Matrix.fromBlocks, Fintype.sum_sum_type] using hCols i

theorem hamiltonian_used_edge_joint_repair_step [Nonempty Iota]
    (S1 S2 : Finset (Sum Iota Iota))
    (P H : Matrix Iota Iota Real) (delta alpha : Real) (n p : Nat)
    (Z : Matrix (Sum (Sum Iota Iota) (Sum (Sum Iota Iota) (Sum Iota Iota)))
      (Sum (Sum Iota Iota) (Sum (Sum Iota Iota) (Sum Iota Iota))) Real)
    (hd0 : 0 < delta) (hd1 : delta < 1) (ha : 0 <= alpha)
    (hP : forall i j, 0 <= P i j) (hCap : forall i j, P i j <= alpha)
    (hPRows : forall i, Finset.univ.sum (fun j => P i j) = 1)
    (hPCols : forall j, Finset.univ.sum (fun i => P i j) = 1)
    (hGap : norm (centeredKernel P (1 / (Fintype.card Iota : Real))) <= 1 - delta)
    (hBinary : forall i j, H i j = 0 \/ H i j = 1)
    (hRows : forall i, Finset.univ.sum (fun j => H i j) = (n : Real))
    (hCols : forall j, Finset.univ.sum (fun i => H i j) = (n : Real))
    (hOldSupport : forall i j, P i j = 0 -> H i j = 0)
    (hSmall : ((n : Real) * alpha) * Real.log (4 * (Fintype.card Iota : Real)) ^ 2 <=
      hamiltonianForbiddenRepairSmall delta) :
    exists W : Matrix Iota Iota Real, exists f : Equiv.Perm Iota,
      (forall i j, 0 <= W i j) /\
      (forall i, Finset.univ.sum (fun j => W i j) = 1) /\
      (forall j, Finset.univ.sum (fun i => W i j) = 1) /\
      (forall i j, W i j = 0 <->
        (P - hamiltonianUsedEdgeDeletion P H) i j = 0) /\
      norm (hamiltonianBipartiteJointLift S1 S2 (W - P)) <=
        hamiltonianForbiddenObservableCost delta * ((n : Real) * alpha) *
          Real.log (4 * (Fintype.card Iota : Real)) /\
      (forall i, H i (f i) = 0 /\ 0 < P i (f i)) /\
      ((forall i j, (H + hamiltonianPermutationCross f) i j = 0 \/
        (H + hamiltonianPermutationCross f) i j = 1) /\
        (forall i, Finset.univ.sum (fun j => (H + hamiltonianPermutationCross f) i j) =
          ((n + 1 : Nat) : Real)) /\
        (forall j, Finset.univ.sum (fun i => (H + hamiltonianPermutationCross f) i j) =
          ((n + 1 : Nat) : Real)) /\
        (forall i j, P i j = 0 -> (H + hamiltonianPermutationCross f) i j = 0)) /\
      let X := hamiltonianBipartiteJointLift S1 S2 (hamiltonianPermutationCross f - W)
      X.IsHermitian /\ norm X <= 2 /\ Matrix.trace (Z ^ p.pred * X) <= 0 := by
  have hBudget := hamiltonian_used_edge_deletion_budgets P H alpha ha n hP hCap
    hBinary hRows hCols
  choose z hRepair using hamiltonian_bounded_mass_deletion_repair_observables
    P (hamiltonianUsedEdgeDeletion P H) delta ((n : Real) * alpha)
    hd0 hd1 hBudget.1 hP hPRows hPCols hGap
    hBudget.2.1 hBudget.2.2.1 hBudget.2.2.2.1 hBudget.2.2.2.2 hSmall
  let W := hamiltonianScaledCross (P - hamiltonianUsedEdgeDeletion P H) z
  have hSpec := hRepair.1
  have hW0 : forall i j, 0 <= W i j := hSpec.2.2.1
  have hWR : forall i, Finset.univ.sum (fun j => W i j) = 1 := hSpec.2.2.2.1
  have hWC : forall j, Finset.univ.sum (fun i => W i j) = 1 := hSpec.2.2.2.2.1
  have hWZero : forall i j, W i j = 0 <->
      (P - hamiltonianUsedEdgeDeletion P H) i j = 0 := hSpec.2.2.2.2.2.1
  have hCardNat : 1 <= Fintype.card Iota := Nat.succ_le_of_lt Fintype.card_pos
  have hCard : (1 : Real) <= Fintype.card Iota := by exact_mod_cast hCardNat
  have hLog : 0 <= Real.log (4 * (Fintype.card Iota : Real)) :=
    (Real.log_pos (by nlinarith only [hCard])).le
  have hb : 0 <= hamiltonianForbiddenObservableCost delta * ((n : Real) * alpha) *
      Real.log (4 * (Fintype.card Iota : Real)) :=
    mul_nonneg
      (mul_nonneg (hamiltonian_forbidden_observable_constant_positive delta hd0 hd1).le
        hBudget.1) hLog
  have hDrift := hamiltonian_bipartite_joint_absolute_mass S1 S2 (W - P) _
    hb hRepair.2.1 hRepair.2.2.1
  choose f hSupport hDirection using
    hamiltonian_supported_joint_matching_direction S1 S2 Z p W hW0 hWR hWC
  have hFresh := hamiltonian_repaired_support_is_fresh P H W f hP hBinary hWZero hSupport
  have hExtension := hamiltonian_fresh_matching_binary_extension P H f n
    hBinary hRows hCols hOldSupport (fun i => (hFresh i).1) (fun i => (hFresh i).2)
  exact Exists.intro W (Exists.intro f
    (And.intro hW0 (And.intro hWR (And.intro hWC (And.intro hWZero
      (And.intro hDrift (And.intro hFresh (And.intro hExtension hDirection))))))))

end PrimeFactorOscillations

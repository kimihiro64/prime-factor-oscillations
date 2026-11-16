/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianRoundingPrefixExtension

/-! # Full finite supported binary rounding with its actual joint error bound -/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations

variable {Iota : Type*} [Fintype Iota] [DecidableEq Iota] [Nonempty Iota]

theorem hamiltonian_rounding_prefix_exists
    (P : Matrix Iota Iota Real) (S1 S2 : Finset (Sum Iota Iota))
    (delta alpha : Real) (p d : Nat)
    (hd0 : 0 < delta) (hd1 : delta < 1) (ha : 0 <= alpha)
    (hP : forall i j, 0 <= P i j) (hCap : forall i j, P i j <= alpha)
    (hPRows : forall i, Finset.univ.sum (fun j => P i j) = 1)
    (hPCols : forall j, Finset.univ.sum (fun i => P i j) = 1)
    (hGap : norm (centeredKernel P (1 / (Fintype.card Iota : Real))) <= 1 - delta)
    (hSmall : ((d : Real) * alpha) * Real.log (4 * (Fintype.card Iota : Real)) ^ 2 <=
      hamiltonianForbiddenRepairSmall delta) :
    Nonempty (HamiltonianRoundingPrefix P S1 S2 delta alpha p d) := by
  have hAux : forall k, k <= d ->
      Nonempty (HamiltonianRoundingPrefix P S1 S2 delta alpha p k) := by
    intro k
    induction k with
    | zero =>
      intro _
      exact Nonempty.intro (hamiltonianRoundingPrefixZero P S1 S2 delta alpha p)
    | succ k ih =>
      intro hkd
      have hk : k <= d := by omega
      have hkReal : (k : Real) <= d := by exact_mod_cast hk
      have hSmallK : ((k : Real) * alpha) *
          Real.log (4 * (Fintype.card Iota : Real)) ^ 2 <=
          hamiltonianForbiddenRepairSmall delta :=
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hkReal ha) (sq_nonneg _)).trans hSmall
      cases ih hk with
      | intro h =>
        exact hamiltonian_rounding_prefix_extension P S1 S2 delta alpha p k
          hd0 hd1 ha hP hCap hPRows hPCols hGap hSmallK h
  exact hAux d le_rfl

theorem hamiltonian_joint_rounding_with_moment_order
    (P : Matrix Iota Iota Real) (S1 S2 : Finset (Sum Iota Iota))
    (delta alpha : Real) (p d : Nat)
    (hd0 : 0 < delta) (hd1 : delta < 1) (ha : 0 <= alpha)
    (hP : forall i j, 0 <= P i j) (hCap : forall i j, P i j <= alpha)
    (hPRows : forall i, Finset.univ.sum (fun j => P i j) = 1)
    (hPCols : forall j, Finset.univ.sum (fun i => P i j) = 1)
    (hGap : norm (centeredKernel P (1 / (Fintype.card Iota : Real))) <= 1 - delta)
    (hSmall : ((d : Real) * alpha) * Real.log (4 * (Fintype.card Iota : Real)) ^ 2 <=
      hamiltonianForbiddenRepairSmall delta)
    (hp : 2 <= p) (hEven : Even p) :
    exists H : Matrix Iota Iota Real,
      (forall i j, H i j = 0 \/ H i j = 1) /\
      (forall i, Finset.univ.sum (fun j => H i j) = (d : Real)) /\
      (forall j, Finset.univ.sum (fun i => H i j) = (d : Real)) /\
      (forall i j, P i j = 0 -> H i j = 0) /\
      norm (hamiltonianBipartiteJointLift S1 S2 (H - HSMul.hSMul (d : Real) P)) <=
        Real.sqrt (1 + 8 * (p.pred : Real) * (d : Real) *
          (6 * (Fintype.card Iota : Real)) ^ (2 / (p : Real))) +
        hamiltonianRoundingDriftCost Iota delta alpha * (d : Real) ^ 2 := by
  cases hamiltonian_rounding_prefix_exists P S1 S2 delta alpha p d
      hd0 hd1 ha hP hCap hPRows hPCols hGap hSmall with
  | intro h =>
    have hCard : Fintype.card (HamiltonianRoundingIndex Iota) =
        6 * Fintype.card Iota := by
      simp only [HamiltonianRoundingIndex, Fintype.card_sum]
      omega
    let C : Real := 1 + 8 * (p.pred : Real) * (d : Real) *
      (6 * (Fintype.card Iota : Real)) ^ (2 / (p : Real))
    have hMoment : norm (h.centered d) ^ 2 <= C := by
      have hM := hamiltonian_rounding_prefix_moment P S1 S2 delta alpha p d h hp hEven
      simpa only [hCard, Nat.cast_mul, Nat.cast_ofNat] using hM
    have hC : 0 <= C := (sq_nonneg _).trans hMoment
    have hZ : norm (h.centered d) <= Real.sqrt C := by
      have hSq := Real.sq_sqrt hC
      have hRoot := Real.sqrt_nonneg C
      nlinarith only [hMoment, hSq, hRoot, norm_nonneg (h.centered d)]
    have hError : norm (hamiltonianBipartiteJointLift S1 S2
        (h.cross - HSMul.hSMul (d : Real) P)) <=
        Real.sqrt C + hamiltonianRoundingDriftCost Iota delta alpha * (d : Real) ^ 2 := by
      rw [h.error_identity]
      exact (norm_add_le _ _).trans (add_le_add hZ h.drift_norm)
    exact Exists.intro h.cross (And.intro h.binary
      (And.intro h.rows (And.intro h.cols (And.intro h.support hError))))

end PrimeFactorOscillations

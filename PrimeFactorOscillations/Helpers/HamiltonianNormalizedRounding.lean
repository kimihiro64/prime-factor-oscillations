/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianFactorNormalization
import PrimeFactorOscillations.Helpers.HamiltonianLogarithmicRounding

/-! # Positive-degree normalization of the same supported binary rounding -/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations

variable {Iota : Type*} [Fintype Iota] [DecidableEq Iota] [Nonempty Iota]

theorem hamiltonian_rounding_sqrt_normalization
    (d L : Real) (hd : 0 < d) :
    (1 / d) * Real.sqrt (d * L) = Real.sqrt (L / d) := by
  have hdNe : Not (d = 0) := ne_of_gt hd
  have hRearr : d * L = d ^ 2 * (L / d) := by
    field_simp [hdNe]
    <;> ring
  rw [hRearr, Real.sqrt_mul (sq_nonneg d), Real.sqrt_sq hd.le]
  field_simp [hdNe]

theorem hamiltonian_joint_error_normalization
    (P H : Matrix Iota Iota Real) (S1 S2 : Finset (Sum Iota Iota))
    (d : Real) (hd : 0 < d) :
    norm (hamiltonianBipartiteJointLift S1 S2 (SMul.smul (1 / d) H - P)) =
      (1 / d) *
        norm (hamiltonianBipartiteJointLift S1 S2 (H - SMul.smul d P)) := by
  have hNormalize := hamiltonian_factor_normalization_identity P H d d (ne_of_gt hd)
  simp only [sub_self, zero_div] at hNormalize
  have hZero : SMul.smul (0 : Real) P = 0 := by
    ext i j
    change 0 * P i j = 0
    exact zero_mul _
  rw [hZero, add_zero] at hNormalize
  rw [hNormalize]
  have hMap :
      hamiltonianBipartiteJointLift S1 S2
          (SMul.smul (1 / d) (H - SMul.smul d P)) =
        SMul.smul (1 / d)
          (hamiltonianBipartiteJointLift S1 S2 (H - SMul.smul d P)) := by
    simpa only [RingHom.id_apply] using!
      (hamiltonianBipartiteJointLift S1 S2).map_smul (1 / d) (H - SMul.smul d P)
  rw [hMap, hamiltonian_matrix_real_smul_norm,
    Real.norm_of_nonneg (div_nonneg (by norm_num) hd.le)]

theorem hamiltonian_joint_normalized_rounding
    (P : Matrix Iota Iota Real) (S1 S2 : Finset (Sum Iota Iota))
    (delta alpha : Real) (d : Nat) (hd : 1 <= d)
    (hd0 : 0 < delta) (hd1 : delta < 1) (ha : 0 <= alpha)
    (hP : forall i j, 0 <= P i j) (hCap : forall i j, P i j <= alpha)
    (hPRows : forall i, Finset.univ.sum (fun j => P i j) = 1)
    (hPCols : forall j, Finset.univ.sum (fun i => P i j) = 1)
    (hGap : norm (centeredKernel P (1 / (Fintype.card Iota : Real))) <= 1 - delta)
    (hSmall : ((d : Real) * alpha) * Real.log (4 * (Fintype.card Iota : Real)) ^ 2 <=
      hamiltonianForbiddenRepairSmall delta) :
    exists H : Matrix Iota Iota Real,
      (forall i j, H i j = 0 \/ H i j = 1) /\
      (forall i, Finset.univ.sum (fun j => H i j) = (d : Real)) /\
      (forall j, Finset.univ.sum (fun i => H i j) = (d : Real)) /\
      (forall i j, P i j = 0 -> H i j = 0) /\
      norm (hamiltonianBipartiteJointLift S1 S2 (SMul.smul (1 / (d : Real)) H - P)) <=
        16 * Real.sqrt (Real.log (4 * (Fintype.card Iota : Real)) / (d : Real)) +
        hamiltonianRoundingDriftCost Iota delta alpha * (d : Real) := by
  have hdReal : (0 : Real) < (d : Real) := by exact_mod_cast (show 0 < d by omega)
  have hdNe : Not ((d : Real) = 0) := ne_of_gt hdReal
  have hInv : 0 <= 1 / (d : Real) := div_nonneg (by norm_num) hdReal.le
  cases hamiltonian_joint_logarithmic_rounding P S1 S2 delta alpha d hd
      hd0 hd1 ha hP hCap hPRows hPCols hGap hSmall with
  | intro H hH =>
    have hError :
        norm (hamiltonianBipartiteJointLift S1 S2
          (SMul.smul (1 / (d : Real)) H - P)) <=
        16 * Real.sqrt (Real.log (4 * (Fintype.card Iota : Real)) / (d : Real)) +
          hamiltonianRoundingDriftCost Iota delta alpha * (d : Real) := by
      rw [hamiltonian_joint_error_normalization P H S1 S2 (d : Real) hdReal]
      calc
        _ <= (1 / (d : Real)) *
            (16 * Real.sqrt ((d : Real) * Real.log (4 * (Fintype.card Iota : Real))) +
              hamiltonianRoundingDriftCost Iota delta alpha * (d : Real) ^ 2) :=
          mul_le_mul_of_nonneg_left hH.2.2.2.2 hInv
        _ = 16 * ((1 / (d : Real)) *
              Real.sqrt ((d : Real) * Real.log (4 * (Fintype.card Iota : Real)))) +
              hamiltonianRoundingDriftCost Iota delta alpha * (d : Real) := by
          field_simp [hdNe]
          <;> ring
        _ = _ := by rw [hamiltonian_rounding_sqrt_normalization _ _ hdReal]
    exact Exists.intro H (And.intro hH.1
      (And.intro hH.2.1 (And.intro hH.2.2.1 (And.intro hH.2.2.2.1 hError))))

end PrimeFactorOscillations

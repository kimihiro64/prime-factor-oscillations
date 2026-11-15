/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianCovarianceCorrection

/-! # The actual parity-corrected stochastic repair kernel

The rank-two constant/parity correction is kept explicitly. Its entry
and row bounds are used for the nonlinear scaling remainder, not to
replace the signed quadratic compensation in the minor expansion.
-/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations

variable {Iota : Type*} [Fintype Iota] [DecidableEq Iota]

def hamiltonianParitySign : Sum Iota Iota -> Real :=
  fun i => match i with
    | Sum.inl _ => 1
    | Sum.inr _ => -1

def hamiltonianRepairProjection (q : Real) :
    Matrix (Sum Iota Iota) (Sum Iota Iota) Real :=
  fun i j => q / 4 + q / 2 * hamiltonianParitySign i * hamiltonianParitySign j

def hamiltonianRepairKernel (T : Matrix Iota Iota Real) (q : Real) :
    Matrix (Sum Iota Iota) (Sum Iota Iota) Real :=
  Ring.inverse ((1 : Matrix (Sum Iota Iota) (Sum Iota Iota) Real) +
      bipartiteLift (centeredKernel T q)) - hamiltonianRepairProjection q

theorem hamiltonianRepairProjection_entry (q : Real) (hq : 0 <= q)
    (i j : Sum Iota Iota) :
    abs (hamiltonianRepairProjection q i j) <= 3 * q / 4 := by
  apply abs_le.mpr
  constructor <;> cases i <;> cases j <;>
    dsimp only [hamiltonianRepairProjection, hamiltonianParitySign] <;> nlinarith only [hq]

variable [Nonempty Iota]

theorem hamiltonianRepairKernel_covariance (T : Matrix Iota Iota Real)
    (q rho : Real) (hNorm : norm (centeredKernel T q) <= rho) (hRho : rho < 1) :
    hamiltonianRepairKernel T q =
      1 - resolventCovariance (bipartiteLift (centeredKernel T q)) -
        hamiltonianRepairProjection q := by
  let Q := bipartiteLift (centeredKernel T q)
  let R := Ring.inverse ((1 : Matrix (Sum Iota Iota) (Sum Iota Iota) Real) + Q)
  have hQNorm : norm Q <= rho := le_trans (bipartiteLift_l2_norm_le _) hNorm
  have hUnit : IsUnit ((1 : Matrix (Sum Iota Iota) (Sum Iota Iota) Real) + Q) := by
    have hNeg : norm (-Q) < 1 := by
      rw [norm_neg]
      exact lt_of_le_of_lt hQNorm hRho
    simpa only [sub_neg_eq_add] using isUnit_one_sub_of_norm_lt_one hNeg
  have hCancel : ((1 : Matrix (Sum Iota Iota) (Sum Iota Iota) Real) + Q) * R = 1 :=
    Ring.mul_inverse_cancel _ hUnit
  have hR : R = 1 - resolventCovariance Q := by
    apply eq_sub_iff_add_eq.mpr
    simpa only [add_mul, one_mul, resolventCovariance] using hCancel
  change R - hamiltonianRepairProjection q = 1 - resolventCovariance Q -
    hamiltonianRepairProjection q
  rw [hR]

theorem stochastic_repair_kernel_entry (T : Matrix Iota Iota Real)
    (q a rho : Real)
    (hq : (Fintype.card Iota : Real) * q = 1) (ha : 1 <= a)
    (hRow : forall i, Finset.sum Finset.univ (fun j => T i j) = 1)
    (hCol : forall j, Finset.sum Finset.univ (fun i => T i j) = 1)
    (hNonneg : forall i j, 0 <= T i j) (hUpper : forall i j, T i j <= a * q)
    (hNorm : norm (centeredKernel T q) <= rho) (hRho : rho < 1)
    (i j : Sum Iota Iota) :
    (1 - rho) * abs ((hamiltonianRepairKernel T q -
      (1 : Matrix (Sum Iota Iota) (Sum Iota Iota) Real)) i j) <= 4 * a * q := by
  let G := resolventCovariance (bipartiteLift (centeredKernel T q))
  have hRho0 : 0 <= rho := le_trans (norm_nonneg _) hNorm
  have hGap : 0 <= 1 - rho := le_of_lt (sub_pos.mpr hRho)
  have hCard : 0 < (Fintype.card Iota : Real) := Nat.cast_pos.mpr Fintype.card_pos
  have hq0 : 0 <= q := by nlinarith only [hq, hCard]
  have hAq0 : 0 <= a * q := mul_nonneg (le_trans (by norm_num) ha) hq0
  have hqA : q <= a * q := by simpa only [one_mul] using
    mul_le_mul_of_nonneg_right ha hq0
  have hG := stochastic_block_covariance_entry_bound T q a rho hq ha
    hRow hCol hNonneg hUpper hRho hNorm i j
  change (1 - rho) * norm (G i j) <= (2 - rho) * (a * q) at hG
  rw [Real.norm_eq_abs] at hG
  have hGTwo : (2 - rho) * (a * q) <= 2 * (a * q) :=
    mul_le_mul_of_nonneg_right (by linarith only [hRho0]) hAq0
  have hP := hamiltonianRepairProjection_entry q hq0 i j
  have hPSmall : (1 - rho) * abs (hamiltonianRepairProjection q i j) <= 3 * q / 4 := by
    calc
      _ <= (1 - rho) * (3 * q / 4) := mul_le_mul_of_nonneg_left hP hGap
      _ <= 1 * (3 * q / 4) :=
        mul_le_mul_of_nonneg_right (by linarith only [hRho0]) (by positivity)
      _ = _ := one_mul _
  have hEntry : (hamiltonianRepairKernel T q -
      (1 : Matrix (Sum Iota Iota) (Sum Iota Iota) Real)) i j =
        -G i j - hamiltonianRepairProjection q i j := by
    rw [hamiltonianRepairKernel_covariance T q rho hNorm hRho]
    simp only [Matrix.sub_apply]
    change (1 : Matrix (Sum Iota Iota) (Sum Iota Iota) Real) i j - G i j -
      hamiltonianRepairProjection q i j -
      (1 : Matrix (Sum Iota Iota) (Sum Iota Iota) Real) i j = _
    ring
  have hAbs : abs ((hamiltonianRepairKernel T q -
      (1 : Matrix (Sum Iota Iota) (Sum Iota Iota) Real)) i j) <=
        abs (G i j) + abs (hamiltonianRepairProjection q i j) := by
    rw [hEntry]
    have h := norm_sub_le (-G i j) (hamiltonianRepairProjection q i j)
    simpa only [Real.norm_eq_abs, abs_neg] using h
  have hScaled := mul_le_mul_of_nonneg_left hAbs hGap
  nlinarith only [hScaled, hG, hGTwo, hPSmall, hqA, hAq0]

theorem stochastic_repair_kernel_row (T : Matrix Iota Iota Real)
    (q a rho : Real)
    (hq : (Fintype.card Iota : Real) * q = 1) (ha : 1 <= a)
    (hRow : forall i, Finset.sum Finset.univ (fun j => T i j) = 1)
    (hCol : forall j, Finset.sum Finset.univ (fun i => T i j) = 1)
    (hNonneg : forall i j, 0 <= T i j) (hUpper : forall i j, T i j <= a * q)
    (hNorm : norm (centeredKernel T q) <= rho) (hRho : rho < 1)
    (i : Sum Iota Iota) :
    (1 - rho) * Finset.sum Finset.univ (fun j => abs (hamiltonianRepairKernel T q i j)) <=
      (1 - rho) + 8 * a := by
  have hGap : 0 <= 1 - rho := le_of_lt (sub_pos.mpr hRho)
  have hEach (j : Sum Iota Iota) :
      (1 - rho) * abs (hamiltonianRepairKernel T q i j) <=
        (1 - rho) * abs ((1 : Matrix (Sum Iota Iota) (Sum Iota Iota) Real) i j) +
          4 * a * q := by
    have hBound := stochastic_repair_kernel_entry T q a rho hq ha
      hRow hCol hNonneg hUpper hNorm hRho i j
    have hAbs : abs (hamiltonianRepairKernel T q i j) <=
        abs ((1 : Matrix (Sum Iota Iota) (Sum Iota Iota) Real) i j) +
          abs ((hamiltonianRepairKernel T q -
            (1 : Matrix (Sum Iota Iota) (Sum Iota Iota) Real)) i j) := by
      have h := abs_add_le
        ((1 : Matrix (Sum Iota Iota) (Sum Iota Iota) Real) i j)
        ((hamiltonianRepairKernel T q -
          (1 : Matrix (Sum Iota Iota) (Sum Iota Iota) Real)) i j)
      simpa only [Matrix.sub_apply, add_sub_cancel] using h
    have hScaled := mul_le_mul_of_nonneg_left hAbs hGap
    nlinarith only [hScaled, hBound]
  have hDiag : Finset.sum Finset.univ
      (fun j => abs ((1 : Matrix (Sum Iota Iota) (Sum Iota Iota) Real) i j)) = 1 := by
    cases i <;> simp [Matrix.one_apply, abs_ite]
  have hCard : (Fintype.card (Sum Iota Iota) : Real) * q = 2 := by
    simp only [Fintype.card_sum, Nat.cast_add]
    nlinarith only [hq]
  rw [Finset.mul_sum]
  calc
    _ <= Finset.sum Finset.univ (fun j =>
        (1 - rho) * abs ((1 : Matrix (Sum Iota Iota) (Sum Iota Iota) Real) i j) +
          4 * a * q) := Finset.sum_le_sum (fun j _ => hEach j)
    _ = (1 - rho) * 1 + (Fintype.card (Sum Iota Iota) : Real) * (4 * a * q) := by
      rw [Finset.sum_add_distrib, <- Finset.mul_sum, hDiag]
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ = (1 - rho) + 8 * a := by
      calc
        _ = (1 - rho) + 4 * a * ((Fintype.card (Sum Iota Iota) : Real) * q) := by ring
        _ = _ := by rw [hCard]; ring

theorem stochastic_repair_kernel_mulVec (T : Matrix Iota Iota Real)
    (q a rho : Real)
    (hq : (Fintype.card Iota : Real) * q = 1) (ha : 1 <= a)
    (hRow : forall i, Finset.sum Finset.univ (fun j => T i j) = 1)
    (hCol : forall j, Finset.sum Finset.univ (fun i => T i j) = 1)
    (hNonneg : forall i j, 0 <= T i j) (hUpper : forall i j, T i j <= a * q)
    (hNorm : norm (centeredKernel T q) <= rho) (hRho : rho < 1)
    (x : Sum Iota Iota -> Real) (i : Sum Iota Iota) :
    (1 - rho) * abs ((hamiltonianRepairKernel T q).mulVec x i) <=
      (1 - rho) * abs (x i) + 4 * a * q * Finset.sum Finset.univ (fun j => abs (x j)) := by
  let E := hamiltonianRepairKernel T q -
    (1 : Matrix (Sum Iota Iota) (Sum Iota Iota) Real)
  have hIdentity : (hamiltonianRepairKernel T q).mulVec x i =
      x i + Finset.sum Finset.univ (fun j => E i j * x j) := by
    change Finset.sum Finset.univ (fun j => hamiltonianRepairKernel T q i j * x j) = _
    calc
      _ = Finset.sum Finset.univ (fun j =>
          ((1 : Matrix (Sum Iota Iota) (Sum Iota Iota) Real) i j + E i j) * x j) := by
        apply Finset.sum_congr rfl
        intro j hj
        dsimp only [E, Matrix.sub_apply]
        ring
      _ = _ := by
        simp [add_mul, Finset.sum_add_distrib, Matrix.one_apply]
  have hAbs : abs ((hamiltonianRepairKernel T q).mulVec x i) <=
      abs (x i) + Finset.sum Finset.univ (fun j => abs (E i j) * abs (x j)) := by
    rw [hIdentity]
    calc
      _ <= abs (x i) + abs (Finset.sum Finset.univ (fun j => E i j * x j)) := abs_add_le _ _
      _ <= abs (x i) + Finset.sum Finset.univ (fun j => abs (E i j * x j)) :=
        add_le_add (le_refl _) (Finset.abs_sum_le_sum_abs _ _)
      _ = _ := by simp only [abs_mul]
  have hGap : 0 <= 1 - rho := le_of_lt (sub_pos.mpr hRho)
  calc
    _ <= (1 - rho) *
        (abs (x i) + Finset.sum Finset.univ (fun j => abs (E i j) * abs (x j))) :=
      mul_le_mul_of_nonneg_left hAbs hGap
    _ = (1 - rho) * abs (x i) + Finset.sum Finset.univ
        (fun j => ((1 - rho) * abs (E i j)) * abs (x j)) := by
      rw [mul_add, Finset.mul_sum]
      simp only [mul_assoc]
    _ <= (1 - rho) * abs (x i) + Finset.sum Finset.univ
        (fun j => (4 * a * q) * abs (x j)) := by
      apply add_le_add (le_refl _)
      apply Finset.sum_le_sum
      intro j hj
      exact mul_le_mul_of_nonneg_right
        (stochastic_repair_kernel_entry T q a rho hq ha
          hRow hCol hNonneg hUpper hNorm hRho i j) (abs_nonneg _)
    _ = _ := by rw [Finset.mul_sum]

end PrimeFactorOscillations

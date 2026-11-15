/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianCovarianceCorrection
import PrimeFactorOscillations.Helpers.HamiltonianRepairSymmetry

/-! # Coefficients of the exact signed occupancy jets

Coordinate energy bounds apply after the parity-root cancellation.
The constant and parity directions are retained in the exact matrix
identity for the derivative, rather than estimated separately.
-/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations

variable {Iota : Type*} [Fintype Iota] [DecidableEq Iota] [Nonempty Iota]

theorem hamiltonian_symmetric_square_entry_energy_bound
    (M : Matrix Iota Iota Real) (g k : Real)
    (hSym : M.transpose = M)
    (hRow : forall i, g ^ 2 * Finset.univ.sum (fun j => M i j ^ 2) <= k)
    (i j : Iota) :
    g ^ 2 * abs ((M * M) i j) <= k := by
  let u : EuclideanSpace Real Iota := WithLp.toLp 2 (fun a => M i a)
  let v : EuclideanSpace Real Iota := WithLp.toLp 2 (fun a => M a j)
  have hSymEntry (a b : Iota) : M a b = M b a :=
    congrFun (congrFun hSym b) a
  have hu : g ^ 2 * norm u ^ 2 <= k := by
    simpa only [EuclideanSpace.real_norm_sq_eq] using hRow i
  have hv : g ^ 2 * norm v ^ 2 <= k := by
    have hEq : norm v ^ 2 = Finset.univ.sum (fun a => M j a ^ 2) := by
      rw [EuclideanSpace.real_norm_sq_eq]
      apply Finset.sum_congr rfl
      intro a ha
      change M a j ^ 2 = M j a ^ 2
      rw [hSymEntry a j]
    rw [hEq]
    exact hRow j
  have hProduct : g ^ 2 * (norm u * norm v) <= k := by
    nlinarith only [hu, hv, sq_nonneg (g * norm u - g * norm v)]
  have hEntry : abs ((M * M) i j) <= norm u * norm v := by
    simpa only [mul_one, norm_one, Real.norm_eq_abs] using
      (l2_sandwich_entry_bound M (1 : Matrix Iota Iota Real) M i j)
  exact le_trans (mul_le_mul_of_nonneg_left hEntry (sq_nonneg g)) hProduct

theorem stochastic_covariance_root_row_energy
    (T : Matrix Iota Iota Real) (q a rho : Real)
    (hq : (Fintype.card Iota : Real) * q = 1)
    (hRow : forall i, Finset.univ.sum (fun j => T i j) = 1)
    (hCol : forall j, Finset.univ.sum (fun i => T i j) = 1)
    (hNonneg : forall i j, 0 <= T i j) (hUpper : forall i j, T i j <= a * q)
    (hNorm : norm (centeredKernel T q) <= rho) (hRho : rho < 1)
    (i : Sum Iota Iota) :
    (1 - rho) ^ 2 * Finset.univ.sum (fun j =>
      resolventCovariance (bipartiteLift (centeredKernel T q)) i j ^ 2) <= a * q := by
  let B := centeredKernel T q
  let Q := bipartiteLift B
  have hq0 : 0 <= q := by
    have hCard : 0 < (Fintype.card Iota : Real) := Nat.cast_pos.mpr Fintype.card_pos
    nlinarith only [hq, hCard]
  have hEnergy : Finset.univ.sum (fun j => Q i j ^ 2) <= (a - 1) * q := by
    cases i with
    | inl i =>
        simpa [Q, bipartiteLift, Matrix.fromBlocks, Fintype.sum_sum_type,
          Matrix.transpose_apply] using
          (stochastic_row_energy T q a hq hRow hNonneg hUpper i)
    | inr i =>
        simpa [Q, bipartiteLift, Matrix.fromBlocks, Fintype.sum_sum_type,
          Matrix.transpose_apply] using
          (stochastic_column_energy T q a hq hCol hNonneg hUpper i)
  have hBase := resolventCovariance_row_energy Q rho
    (le_trans (bipartiteLift_l2_norm_le B) hNorm) hRho i
  change (1 - rho) ^ 2 * Finset.univ.sum (fun j => resolventCovariance Q i j ^ 2) <= a * q
  linarith only [hBase, hEnergy, hq0]

theorem stochastic_covariance_transpose (T : Matrix Iota Iota Real)
    (q rho : Real) (hNorm : norm (centeredKernel T q) <= rho) (hRho : rho < 1) :
    (resolventCovariance (bipartiteLift (centeredKernel T q))).transpose =
      resolventCovariance (bipartiteLift (centeredKernel T q)) := by
  let G := resolventCovariance (bipartiteLift (centeredKernel T q))
  let H := hamiltonianRepairProjection (Iota := Iota) q
  let K := hamiltonianRepairKernel T q
  have hH : H.transpose = H := by
    apply Matrix.ext
    intro i j
    simp only [H, Matrix.transpose_apply, hamiltonianRepairProjection]
    ring
  have hK : K = 1 - G - H := hamiltonianRepairKernel_covariance T q rho hNorm hRho
  have hTrans := congrArg Matrix.transpose hK
  rw [stochastic_repair_kernel_transpose T q rho hNorm hRho,
    Matrix.transpose_sub, Matrix.transpose_sub, Matrix.transpose_one, hH] at hTrans
  change K = 1 - G.transpose - H at hTrans
  calc
    G.transpose = 1 - H - K := by rw [hTrans]; abel
    _ = G := by rw [hK]; abel

theorem stochastic_covariance_square_entry
    (T : Matrix Iota Iota Real) (q a rho : Real)
    (hq : (Fintype.card Iota : Real) * q = 1)
    (hRow : forall i, Finset.univ.sum (fun j => T i j) = 1)
    (hCol : forall j, Finset.univ.sum (fun i => T i j) = 1)
    (hNonneg : forall i j, 0 <= T i j) (hUpper : forall i j, T i j <= a * q)
    (hNorm : norm (centeredKernel T q) <= rho) (hRho : rho < 1)
    (i j : Sum Iota Iota) :
    let G := resolventCovariance (bipartiteLift (centeredKernel T q))
    (1 - rho) ^ 2 * abs ((G * G) i j) <= a * q := by
  exact hamiltonian_symmetric_square_entry_energy_bound _ (1 - rho) (a * q)
    (stochastic_covariance_transpose T q rho hNorm hRho)
    (stochastic_covariance_root_row_energy T q a rho hq hRow hCol hNonneg hUpper hNorm hRho) i j

theorem stochastic_regularized_covariance_jet_identity
    (T : Matrix Iota Iota Real) (q rho : Real)
    (hq : (Fintype.card Iota : Real) * q = 1)
    (hRow : forall i, Finset.univ.sum (fun j => T i j) = 1)
    (hCol : forall j, Finset.univ.sum (fun i => T i j) = 1)
    (hNorm : norm (centeredKernel T q) <= rho) (hRho : rho < 1) :
    let G := resolventCovariance (bipartiteLift (centeredKernel T q))
    (hamiltonianRepairKernel T q) ^ 2 - hamiltonianRepairKernel T q +
      hamiltonianParityProjection q =
        -G + G * G - averagingKernel (Iota := Sum Iota Iota) (q / 8) +
          hamiltonianParityProjection q := by
  let B := centeredKernel T q
  let Q := bipartiteLift B
  let R := Ring.inverse ((1 : Matrix (Sum Iota Iota) (Sum Iota Iota) Real) + Q)
  let G := resolventCovariance Q
  let H := hamiltonianRepairProjection (Iota := Iota) q
  let K := hamiltonianRepairKernel T q
  have hBRow (i : Iota) : Finset.univ.sum (fun j => B i j) = 0 := by
    change Finset.univ.sum (fun j => T i j - q) = 0
    rw [Finset.sum_sub_distrib, hRow i, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, hq, sub_self]
  have hBCol (j : Iota) : Finset.univ.sum (fun i => B i j) = 0 := by
    change Finset.univ.sum (fun i => T i j - q) = 0
    rw [Finset.sum_sub_distrib, hCol j, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, hq, sub_self]
  have hQH : Q * H = 0 := by
    apply Matrix.ext
    intro i j
    cases i <;> cases j <;>
      simp [Q, H, Matrix.mul_apply, Fintype.sum_sum_type, bipartiteLift,
        Matrix.fromBlocks, Matrix.transpose_apply, hamiltonianRepairProjection,
        hamiltonianParitySign, mul_assoc, <- Finset.sum_mul, hBRow, hBCol]
  have hQT : Q.transpose = Q := by
    apply Matrix.ext
    intro i j
    cases i <;> cases j <;> rfl
  have hHT : H.transpose = H := by
    apply Matrix.ext
    intro i j
    simp only [H, Matrix.transpose_apply, hamiltonianRepairProjection]
    ring
  have hHQ : H * Q = 0 := by
    simpa only [Matrix.transpose_mul, hQT, hHT, Matrix.transpose_zero] using
      congrArg Matrix.transpose hQH
  have hUnit : IsUnit ((1 : Matrix (Sum Iota Iota) (Sum Iota Iota) Real) + Q) := by
    have hSmall : norm (-Q) < 1 := by
      rw [norm_neg]
      exact lt_of_le_of_lt (le_trans (bipartiteLift_l2_norm_le B) hNorm) hRho
    simpa only [sub_neg_eq_add] using isUnit_one_sub_of_norm_lt_one hSmall
  have hRH : R * H = H := by
    have hFactor : ((1 : Matrix (Sum Iota Iota) (Sum Iota Iota) Real) + Q) * H = H := by
      rw [add_mul, one_mul, hQH, add_zero]
    calc
      _ = R * (((1 : Matrix (Sum Iota Iota) (Sum Iota Iota) Real) + Q) * H) := by rw [hFactor]
      _ = H := by rw [<- mul_assoc, Ring.inverse_mul_cancel _ hUnit, one_mul]
  have hGH : G * H = 0 := by
    change (Q * R) * H = 0
    rw [mul_assoc, hRH, hQH]
  have hHG : H * G = 0 := by
    change H * (Q * R) = 0
    rw [<- mul_assoc, hHQ, zero_mul]
  have hQQ : (Fintype.card Iota : Real) * q ^ 2 = q := by
    have h := congrArg (fun x : Real => x * q) hq
    nlinarith only [h]
  have hHsquare : H * H - H =
      -averagingKernel (Iota := Sum Iota Iota) (q / 8) := by
    apply Matrix.ext
    intro i j
    cases i <;> cases j <;>
      simp [H, Matrix.mul_apply, Matrix.sub_apply, Fintype.sum_sum_type,
        hamiltonianRepairProjection, hamiltonianParitySign, averagingKernel]
      <;> nlinarith only [hQQ]
  have hK : K = 1 - G - H := hamiltonianRepairKernel_covariance T q rho hNorm hRho
  calc
    K ^ 2 - K + hamiltonianParityProjection q =
        -G + G * G + (H * H - H) + hamiltonianParityProjection q := by
      rw [hK]
      simp only [pow_two, sub_mul, mul_sub, one_mul, mul_one,
        hGH, hHG, sub_zero, zero_sub]
      abel
    _ = _ := by rw [hHsquare]; abel

end PrimeFactorOscillations

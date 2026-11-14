/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianBipartiteDeterminant
import PrimeFactorOscillations.Helpers.HamiltonianL2Resolvent

/-! # Full block covariance bounds from the actual stochastic matrix

The bipartite lift is bounded by its block in the Euclidean operator norm.
The resolvent bound is applied only to coordinate coefficients after retaining
the determinant's signed algebra. The final theorem discharges the entry
hypothesis for the actual full Gaussian covariance, including both parts.
-/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations

variable {Iota : Type*} [DecidableEq Iota] [Fintype Iota]

theorem bipartiteLift_l2_norm_le (B : Matrix Iota Iota Real) :
    norm (bipartiteLift B) <= norm B := by
  let op := (@Matrix.toEuclideanCLM Real (Sum Iota Iota) _ _ _) (bipartiteLift B)
  have hTranspose : B.conjTranspose = B.transpose := by
    ext i j
    simp [Matrix.conjTranspose_apply, Matrix.transpose_apply]
  have hTransposeNorm : norm B.transpose = norm B := by
    simpa only [hTranspose] using Matrix.l2_opNorm_conjTranspose B
  have hOp : norm op <= norm B := by
    apply ContinuousLinearMap.opNorm_le_bound op (norm_nonneg B)
    intro x
    let u : EuclideanSpace Real Iota := WithLp.toLp 2 (fun i => x.ofLp (Sum.inl i))
    let v : EuclideanSpace Real Iota := WithLp.toLp 2 (fun i => x.ofLp (Sum.inr i))
    let y : EuclideanSpace Real Iota := WithLp.toLp 2 (B.mulVec v.ofLp)
    let z : EuclideanSpace Real Iota := WithLp.toLp 2 (B.transpose.mulVec u.ofLp)
    have hy : norm y <= norm B * norm v := by
      exact Matrix.l2_opNorm_mulVec B v
    have hz : norm z <= norm B * norm u := by
      have hz0 : norm z <= norm B.transpose * norm u :=
        Matrix.l2_opNorm_mulVec B.transpose u
      rwa [hTransposeNorm] at hz0
    have hxSq : norm x ^ 2 = norm u ^ 2 + norm v ^ 2 := by
      simp only [EuclideanSpace.real_norm_sq_eq, Fintype.sum_sum_type]
      rfl
    have hOpSq : norm (op x) ^ 2 = norm y ^ 2 + norm z ^ 2 := by
      simp only [EuclideanSpace.real_norm_sq_eq]
      change Finset.sum Finset.univ
        (fun k => ((bipartiteLift B).mulVec x.ofLp k) ^ 2) = _
      simp [bipartiteLift, Matrix.mulVec, dotProduct, Fintype.sum_sum_type,
        Matrix.fromBlocks, y, z, u, v]
    have hySq : norm y ^ 2 <= (norm B * norm v) ^ 2 := by
      simpa only [pow_two] using mul_le_mul hy hy (norm_nonneg y)
        (mul_nonneg (norm_nonneg B) (norm_nonneg v))
    have hzSq : norm z ^ 2 <= (norm B * norm u) ^ 2 := by
      simpa only [pow_two] using mul_le_mul hz hz (norm_nonneg z)
        (mul_nonneg (norm_nonneg B) (norm_nonneg u))
    have hSq : norm (op x) ^ 2 <= (norm B * norm x) ^ 2 := by
      calc
        _ = norm y ^ 2 + norm z ^ 2 := hOpSq
        _ <= (norm B * norm v) ^ 2 + (norm B * norm u) ^ 2 := add_le_add hySq hzSq
        _ = norm B ^ 2 * (norm u ^ 2 + norm v ^ 2) := by ring
        _ = norm B ^ 2 * norm x ^ 2 := by rw [<- hxSq]
        _ = (norm B * norm x) ^ 2 := by ring
    have hNonneg : 0 <= norm B * norm x :=
      mul_nonneg (norm_nonneg B) (norm_nonneg x)
    nlinarith only [hSq, norm_nonneg (op x), hNonneg]
  change norm ((@Matrix.toEuclideanCLM Real (Sum Iota Iota) _ _ _)
    (bipartiteLift B)) <= norm B at hOp
  rwa [Matrix.l2_opNorm_toEuclideanCLM] at hOp

variable [Nonempty Iota]

theorem l2_resolvent_coordinate_bound (Q : Matrix Iota Iota Real)
    (rho k : Real) (hRho : rho < 1) (hNorm : norm Q <= rho)
    (hEntry : forall i j, norm (Q i j) <= k)
    (hRow : forall i, Finset.sum Finset.univ (fun j => Q i j ^ 2) <= k)
    (hCol : forall j, Finset.sum Finset.univ (fun i => Q i j ^ 2) <= k)
    (i j : Iota) :
    (1 - rho) * norm ((Q * Ring.inverse ((1 : Matrix Iota Iota Real) + Q)) i j) <=
      (2 - rho) * k := by
  let R := Ring.inverse ((1 : Matrix Iota Iota Real) + Q)
  have hUnit : IsUnit ((1 : Matrix Iota Iota Real) + Q) := by
    have hNeg : norm (-Q) < 1 := by
      rw [norm_neg]
      exact lt_of_le_of_lt hNorm hRho
    simpa only [sub_neg_eq_add] using isUnit_one_sub_of_norm_lt_one hNeg
  have hCancel : R * ((1 : Matrix Iota Iota Real) + Q) = 1 :=
    Ring.inverse_mul_cancel _ hUnit
  have hR : R = 1 - R * Q := by
    apply eq_sub_iff_add_eq.mpr
    simpa only [mul_add, mul_one] using hCancel
  have hCoupled : Q * R = Q - Q * R * Q := by
    calc
      _ = Q * (1 - R * Q) := congrArg (fun M => Q * M) hR
      _ = _ := by rw [mul_sub, mul_one, <- mul_assoc]
  let u : EuclideanSpace Real Iota := WithLp.toLp 2 (fun a => Q i a)
  let v : EuclideanSpace Real Iota := WithLp.toLp 2 (fun a => Q a j)
  have hu : norm u ^ 2 <= k := by
    simpa only [EuclideanSpace.real_norm_sq_eq] using hRow i
  have hv : norm v ^ 2 <= k := by
    simpa only [EuclideanSpace.real_norm_sq_eq] using hCol j
  have hProduct : norm u * norm v <= k := by
    nlinarith only [hu, hv, sq_nonneg (norm u - norm v)]
  have hSandwich : norm ((Q * R * Q) i j) <= norm u * norm R * norm v :=
    l2_sandwich_entry_bound Q R Q i j
  have hNeumann : (1 - rho) * norm R <= 1 := by
    simpa only [norm_neg, sub_neg_eq_add] using
      l2_neumann_certificate (-Q) rho (by simpa only [norm_neg] using hNorm) hRho
  have hGap : 0 <= 1 - rho := le_of_lt (sub_pos.mpr hRho)
  have hCorrection : (1 - rho) * norm ((Q * R * Q) i j) <= k := by
    calc
      _ <= (1 - rho) * (norm u * norm R * norm v) :=
        mul_le_mul_of_nonneg_left hSandwich hGap
      _ = (norm u * norm v) * ((1 - rho) * norm R) := by ring
      _ <= (norm u * norm v) * 1 :=
        mul_le_mul_of_nonneg_left hNeumann
          (mul_nonneg (norm_nonneg u) (norm_nonneg v))
      _ = norm u * norm v := mul_one _
      _ <= k := hProduct
  have hCoordinate : norm ((Q * R) i j) <= norm (Q i j) + norm ((Q * R * Q) i j) := by
    conv_lhs => rw [hCoupled]
    exact norm_sub_le (Q i j) ((Q * R * Q) i j)
  calc
    _ <= (1 - rho) * (norm (Q i j) + norm ((Q * R * Q) i j)) :=
      mul_le_mul_of_nonneg_left hCoordinate hGap
    _ <= (1 - rho) * k + k := by
      nlinarith only [mul_le_mul_of_nonneg_left (hEntry i j) hGap, hCorrection]
    _ = (2 - rho) * k := by ring

theorem stochastic_block_covariance_entry_bound
    (T : Matrix Iota Iota Real) (q a rho : Real)
    (hq : (Fintype.card Iota : Real) * q = 1) (ha : 1 <= a)
    (hrow : forall i, Finset.sum Finset.univ (fun j => T i j) = 1)
    (hcol : forall j, Finset.sum Finset.univ (fun i => T i j) = 1)
    (hnonneg : forall i j, 0 <= T i j) (hupper : forall i j, T i j <= a * q)
    (hRho : rho < 1) (hNorm : norm (centeredKernel T q) <= rho)
    (i j : Sum Iota Iota) :
    (1 - rho) * norm
      ((bipartiteLift (centeredKernel T q) *
        Ring.inverse ((1 : Matrix (Sum Iota Iota) (Sum Iota Iota) Real) +
          bipartiteLift (centeredKernel T q))) i j) <= (2 - rho) * (a * q) := by
  let B := centeredKernel T q
  let Q := bipartiteLift B
  have hCard : 0 < (Fintype.card Iota : Real) := by
    exact Nat.cast_pos.mpr Fintype.card_pos
  have hq0 : 0 <= q := by nlinarith only [hq, hCard]
  have hAq : 0 <= a * q := mul_nonneg (le_trans (by norm_num) ha) hq0
  have hBEntry : forall r s, norm (B r s) <= a * q := by
    intro r s
    rw [Real.norm_eq_abs]
    apply abs_le.mpr
    constructor
    case left =>
      change -(a * q) <= T r s - q
      nlinarith only [hnonneg r s, mul_le_mul_of_nonneg_right ha hq0]
    case right =>
      change T r s - q <= a * q
      linarith only [hupper r s, hq0]
  have hRow : forall r, Finset.sum Finset.univ (fun s => B r s ^ 2) <= a * q := by
    intro r
    have h := stochastic_row_energy T q a hq hrow hnonneg hupper r
    nlinarith only [h, hq0]
  have hCol : forall s, Finset.sum Finset.univ (fun r => B r s ^ 2) <= a * q := by
    intro s
    have h := stochastic_column_energy T q a hq hcol hnonneg hupper s
    nlinarith only [h, hq0]
  have hQNorm : norm Q <= rho :=
    le_trans (bipartiteLift_l2_norm_le B) hNorm
  have hBAbs : forall r s, abs (B r s) <= a * q := by
    simpa only [Real.norm_eq_abs] using hBEntry
  have hQEntry : forall r s, norm (Q r s) <= a * q := by
    intro r s
    cases r <;> cases s <;> simp [Q, bipartiteLift, Matrix.fromBlocks,
      Matrix.transpose_apply, hBAbs, hAq]
  have hQRow : forall r, Finset.sum Finset.univ (fun s => Q r s ^ 2) <= a * q := by
    intro r
    cases r with
    | inl r =>
        simpa [Q, bipartiteLift, Matrix.fromBlocks, Fintype.sum_sum_type,
          Matrix.transpose_apply] using hRow r
    | inr r =>
        simpa [Q, bipartiteLift, Matrix.fromBlocks, Fintype.sum_sum_type,
          Matrix.transpose_apply] using hCol r
  have hQCol : forall s, Finset.sum Finset.univ (fun r => Q r s ^ 2) <= a * q := by
    intro s
    cases s with
    | inl s =>
        simpa [Q, bipartiteLift, Matrix.fromBlocks, Fintype.sum_sum_type,
          Matrix.transpose_apply] using hRow s
    | inr s =>
        simpa [Q, bipartiteLift, Matrix.fromBlocks, Fintype.sum_sum_type,
          Matrix.transpose_apply] using hCol s
  exact l2_resolvent_coordinate_bound Q rho (a * q) hRho hQNorm hQEntry hQRow hQCol i j

end PrimeFactorOscillations

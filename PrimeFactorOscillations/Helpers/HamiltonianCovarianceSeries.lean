/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianCovarianceCorrection

/-! # The full signed covariance series and all-coefficient bounds

The coefficients retain Q*(-Q)^k exactly. Their matrix sum is the actual
resolvent covariance, with convergence proved in the Euclidean operator norm.
Squared row and column energy give a coefficient bound linear in the entry
parameter, uniformly in every degree. These bounds control the Wick remainder;
they do not replace its retained signed low-degree correction.
-/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations

variable {Iota : Type*} [DecidableEq Iota] [Fintype Iota] [Nonempty Iota]

def covarianceSeriesCoefficient (Q : Matrix Iota Iota Real) (k : Nat) :
    Matrix Iota Iota Real := Q * (-Q) ^ k

theorem resolventCovariance_hasSum (Q : Matrix Iota Iota Real) (hNorm : norm Q < 1) :
    HasSum (covarianceSeriesCoefficient Q) (resolventCovariance Q) := by
  have hNeg : norm (-Q) < 1 := by simpa only [norm_neg] using hNorm
  let ringStructure : NormedRing (Matrix Iota Iota Real) := inferInstance
  have hGeom := @hasSum_geom_series_inverse (Matrix Iota Iota Real) ringStructure
    (inferInstance : HasSummableGeomSeries (Matrix Iota Iota Real)) (-Q) hNeg
  have h := hGeom.mul_left Q
  convert! h using 1 <;>
    simp only [sub_neg_eq_add, covarianceSeriesCoefficient, resolventCovariance]

private theorem covariance_power_mono (a b : Real) (ha : 0 <= a)
    (hab : a <= b) (k : Nat) : a ^ k <= b ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, pow_succ]
    exact mul_le_mul ih hab ha (pow_nonneg (le_trans ha hab) k)

theorem covarianceSeriesCoefficient_bound (Q : Matrix Iota Iota Real) (kappa theta : Real)
    (hKappa : 0 <= kappa) (hTheta : 1 / 2 <= theta)
    (hNorm : norm Q <= theta)
    (hEntry : forall i j, norm (Q i j) <= kappa)
    (hRow : forall i, Finset.sum Finset.univ (fun j => Q i j ^ 2) <= kappa)
    (hCol : forall j, Finset.sum Finset.univ (fun i => Q i j ^ 2) <= kappa)
    (k : Nat) (i j : Iota) :
    norm ((covarianceSeriesCoefficient Q k) i j) <= 2 * kappa * theta ^ k := by
  have hTheta0 : 0 <= theta := by linarith only [hTheta]
  cases k with
  | zero =>
    simpa only [covarianceSeriesCoefficient, pow_zero, mul_one] using
      le_trans (hEntry i j) (show kappa <= 2 * kappa * theta ^ 0 by
        norm_num
        linarith only [hKappa])
  | succ k =>
    let u : EuclideanSpace Real Iota := WithLp.toLp 2 (fun a => Q i a)
    let v : EuclideanSpace Real Iota := WithLp.toLp 2 (fun a => Q a j)
    have hu : norm u ^ 2 <= kappa := by
      simpa only [EuclideanSpace.real_norm_sq_eq] using hRow i
    have hv : norm v ^ 2 <= kappa := by
      simpa only [EuclideanSpace.real_norm_sq_eq] using hCol j
    have hProduct : norm u * norm v <= kappa := by
      nlinarith only [hu, hv, sq_nonneg (norm u - norm v)]
    have hPower : norm ((-Q) ^ k) <= theta ^ k := by
      exact le_trans (norm_pow_le (-Q) k)
        (covariance_power_mono (norm (-Q)) theta (norm_nonneg _)
          (by simpa only [norm_neg] using hNorm) k)
    have hSign : covarianceSeriesCoefficient Q (k + 1) =
        -(Q * ((-Q) ^ k) * Q) := by
      simp only [covarianceSeriesCoefficient, pow_succ, mul_neg, mul_assoc]
    rw [hSign, Matrix.neg_apply, norm_neg]
    have hSandwich : norm ((Q * ((-Q) ^ k) * Q) i j) <=
        norm u * norm ((-Q) ^ k) * norm v :=
      l2_sandwich_entry_bound Q ((-Q) ^ k) Q i j
    calc
      _ <= norm u * norm ((-Q) ^ k) * norm v := hSandwich
      _ <= norm u * theta ^ k * norm v :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hPower (norm_nonneg u)) (norm_nonneg v)
      _ = (norm u * norm v) * theta ^ k := by ring
      _ <= kappa * theta ^ k :=
        mul_le_mul_of_nonneg_right hProduct (pow_nonneg hTheta0 k)
      _ <= (kappa * theta ^ k) * (2 * theta) := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left
          (show 1 <= 2 * theta by linarith only [hTheta])
          (mul_nonneg hKappa (pow_nonneg hTheta0 k))
      _ = 2 * kappa * theta ^ (k + 1) := by rw [pow_succ]; ring


theorem stochastic_covariance_series_data
    (T : Matrix Iota Iota Real) (q a delta b s : Real)
    (hq : (Fintype.card Iota : Real) * q = 1) (ha : 1 <= a)
    (hrow : forall i, Finset.sum Finset.univ (fun j => T i j) = 1)
    (hcol : forall j, Finset.sum Finset.univ (fun i => T i j) = 1)
    (hnonneg : forall i j, 0 <= T i j) (hupper : forall i j, T i j <= a * q)
    (hDelta0 : 0 < delta) (hDelta1 : delta <= 1)
    (hNorm : norm (centeredKernel T q) <= 1 - delta)
    (hb : 1 <= b) (hs : abs s <= b) (hTheta1 : b * (1 - delta / 2) < 1) :
    And
      (HasSum (covarianceSeriesCoefficient
          (HSMul.hSMul s (bipartiteLift (centeredKernel T q))))
        (resolventCovariance (HSMul.hSMul s (bipartiteLift (centeredKernel T q)))))
      (forall k i j,
        norm ((covarianceSeriesCoefficient
          (HSMul.hSMul s (bipartiteLift (centeredKernel T q))) k) i j) <=
          2 * b ^ 2 * a * q * (b * (1 - delta / 2)) ^ k) := by
  let B := centeredKernel T q
  let Q := bipartiteLift B
  let U : Matrix (Sum Iota Iota) (Sum Iota Iota) Real := HSMul.hSMul s Q
  let theta : Real := b * (1 - delta / 2)
  have hb0 : 0 <= b := le_trans (by norm_num) hb
  have hCardPos : 0 < (Fintype.card Iota : Real) :=
    Nat.cast_pos.mpr Fintype.card_pos
  have hq0 : 0 <= q := by nlinarith only [hq, hCardPos]
  have ha0 : 0 <= a := le_trans (by norm_num) ha
  have hAq : 0 <= a * q := mul_nonneg ha0 hq0
  have hBSquare : b <= b ^ 2 := by nlinarith only [hb]
  have hsSquare : s ^ 2 <= b ^ 2 := by
    have h := mul_le_mul hs hs (abs_nonneg s) hb0
    simpa only [<- pow_two, sq_abs] using h
  have hThetaHalf : 1 / 2 <= theta := by
    have hHalf : (1 / 2 : Real) <= 1 - delta / 2 := by linarith only [hDelta1]
    have h := mul_le_mul hb hHalf (by norm_num) hb0
    change (1 : Real) * (1 / 2) <= theta at h
    simpa only [one_mul] using h
  have hQNorm : norm Q <= 1 - delta :=
    le_trans (bipartiteLift_l2_norm_le B) hNorm
  have hUNorm : norm U <= theta := by
    calc
      _ = abs s * norm Q := by
        change norm (HSMul.hSMul s Q) = _
        rw [norm_smul, Real.norm_eq_abs]
      _ <= b * (1 - delta) :=
        mul_le_mul hs hQNorm (norm_nonneg Q) hb0
      _ <= theta := by
        dsimp only [theta]
        nlinarith only [hDelta0, hb0, mul_nonneg hb0 (le_of_lt hDelta0)]
  have hBEntry : forall i j, abs (B i j) <= a * q := by
    intro i j
    apply abs_le.mpr
    constructor
    case left =>
      change -(a * q) <= T i j - q
      have h := mul_le_mul_of_nonneg_right ha hq0
      nlinarith only [hnonneg i j, h]
    case right =>
      change T i j - q <= a * q
      linarith only [hupper i j, hq0]
  have hBRow : forall i, Finset.sum Finset.univ (fun j => B i j ^ 2) <= a * q := by
    intro i
    have h := stochastic_row_energy T q a hq hrow hnonneg hupper i
    nlinarith only [h, hq0]
  have hBCol : forall j, Finset.sum Finset.univ (fun i => B i j ^ 2) <= a * q := by
    intro j
    have h := stochastic_column_energy T q a hq hcol hnonneg hupper j
    nlinarith only [h, hq0]
  have hQEntry : forall i j, abs (Q i j) <= a * q := by
    intro i j
    cases i <;> cases j <;>
      simp [Q, bipartiteLift, Matrix.fromBlocks, Matrix.transpose_apply, hBEntry, hAq]
  have hQRow : forall i, Finset.sum Finset.univ (fun j => Q i j ^ 2) <= a * q := by
    intro i
    cases i with
    | inl i => simpa [Q, bipartiteLift, Matrix.fromBlocks, Fintype.sum_sum_type,
        Matrix.transpose_apply] using hBRow i
    | inr i => simpa [Q, bipartiteLift, Matrix.fromBlocks, Fintype.sum_sum_type,
        Matrix.transpose_apply] using hBCol i
  have hQCol : forall j, Finset.sum Finset.univ (fun i => Q i j ^ 2) <= a * q := by
    intro j
    cases j with
    | inl j => simpa [Q, bipartiteLift, Matrix.fromBlocks, Fintype.sum_sum_type,
        Matrix.transpose_apply] using hBRow j
    | inr j => simpa [Q, bipartiteLift, Matrix.fromBlocks, Fintype.sum_sum_type,
        Matrix.transpose_apply] using hBCol j
  have hUEntry : forall i j, norm (U i j) <= b ^ 2 * a * q := by
    intro i j
    change norm (s * Q i j) <= _
    rw [Real.norm_eq_abs, abs_mul]
    have h1 := mul_le_mul hs (hQEntry i j) (abs_nonneg (Q i j)) hb0
    have h2 := mul_le_mul_of_nonneg_right hBSquare hAq
    nlinarith only [h1, h2]
  have hURow : forall i,
      Finset.sum Finset.univ (fun j => U i j ^ 2) <= b ^ 2 * a * q := by
    intro i
    have hScale : Finset.sum Finset.univ (fun j => U i j ^ 2) =
        s ^ 2 * Finset.sum Finset.univ (fun j => Q i j ^ 2) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      change (s * Q i j) ^ 2 = s ^ 2 * Q i j ^ 2
      ring
    rw [hScale]
    have h1 := mul_le_mul_of_nonneg_left (hQRow i) (sq_nonneg s)
    have h2 := mul_le_mul_of_nonneg_right hsSquare hAq
    nlinarith only [h1, h2]
  have hUCol : forall j,
      Finset.sum Finset.univ (fun i => U i j ^ 2) <= b ^ 2 * a * q := by
    intro j
    have hScale : Finset.sum Finset.univ (fun i => U i j ^ 2) =
        s ^ 2 * Finset.sum Finset.univ (fun i => Q i j ^ 2) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      change (s * Q i j) ^ 2 = s ^ 2 * Q i j ^ 2
      ring
    rw [hScale]
    have h1 := mul_le_mul_of_nonneg_left (hQCol j) (sq_nonneg s)
    have h2 := mul_le_mul_of_nonneg_right hsSquare hAq
    nlinarith only [h1, h2]
  have hSeries : HasSum (covarianceSeriesCoefficient U) (resolventCovariance U) :=
    resolventCovariance_hasSum U (lt_of_le_of_lt hUNorm hTheta1)
  have hCoefficients : forall k i j,
      norm ((covarianceSeriesCoefficient U k) i j) <= 2 * b ^ 2 * a * q * theta ^ k := by
    intro k i j
    have h := covarianceSeriesCoefficient_bound U (b ^ 2 * a * q) theta
      (by positivity) hThetaHalf hUNorm hUEntry hURow hUCol k i j
    nlinarith only [h]
  exact And.intro hSeries hCoefficients

end PrimeFactorOscillations

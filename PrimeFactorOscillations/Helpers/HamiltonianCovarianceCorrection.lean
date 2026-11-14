/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianBlockCovariance

/-! # The full covariance correction with explicit energy bounds

The resolvent covariance is the actual matrix Q(1+Q)^{-1}. Its squared-entry
energy is bounded using the Euclidean operator norm and the original energy,
without replacing that energy by the matrix dimension. The correction keeps
the diagonal, quadratic-form and entry-cubic terms together.
-/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations

variable {Iota : Type*} [DecidableEq Iota] [Fintype Iota]

def matrixSquareEnergy (M : Matrix Iota Iota Real) : Real :=
  Finset.sum Finset.univ (fun i => Finset.sum Finset.univ (fun j => M i j ^ 2))

def resolventCovariance (Q : Matrix Iota Iota Real) : Matrix Iota Iota Real :=
  Q * Ring.inverse ((1 : Matrix Iota Iota Real) + Q)

def covarianceDiagonalEnergy (M : Matrix Iota Iota Real) : Real :=
  Finset.sum Finset.univ (fun i => M i i ^ 2)

def covarianceTriple (M : Matrix Iota Iota Real) : Real :=
  Finset.sum Finset.univ (fun i => Finset.sum Finset.univ
    (fun j => M i i * M j j * M i j))

def covarianceCubic (M : Matrix Iota Iota Real) : Real :=
  Finset.sum Finset.univ (fun i => Finset.sum Finset.univ (fun j => M i j ^ 3))

def covarianceCorrection (M : Matrix Iota Iota Real) : Real :=
  -(3 / 4 : Real) * covarianceDiagonalEnergy M +
    (1 / 2 : Real) * covarianceTriple M + (1 / 3 : Real) * covarianceCubic M

theorem matrixSquareEnergy_nonnegative (M : Matrix Iota Iota Real) :
    0 <= matrixSquareEnergy M := by
  exact Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => sq_nonneg (M i j)))

theorem covarianceDiagonalEnergy_nonnegative (M : Matrix Iota Iota Real) :
    0 <= covarianceDiagonalEnergy M := by
  exact Finset.sum_nonneg (fun i _ => sq_nonneg (M i i))

theorem covarianceDiagonalEnergy_entry_bound (M : Matrix Iota Iota Real) (c : Real)
    (hc : 0 <= c) (hEntry : forall i j, abs (M i j) <= c) :
    covarianceDiagonalEnergy M <= (Fintype.card Iota : Real) * c ^ 2 := by
  calc
    _ <= Finset.sum Finset.univ (fun _ : Iota => c ^ 2) := by
      apply Finset.sum_le_sum
      intro i hi
      have h := hEntry i i
      have hMul := mul_le_mul h h (abs_nonneg (M i i)) hc
      simpa only [<- pow_two, sq_abs] using hMul
    _ = _ := by simp

theorem covarianceTriple_bound (M : Matrix Iota Iota Real) :
    abs (covarianceTriple M) <= norm M * covarianceDiagonalEnergy M := by
  let u : EuclideanSpace Real Iota := WithLp.toLp 2 (fun i => M i i)
  let op := (@Matrix.toEuclideanCLM Real Iota _ _ _) M
  have hTriple : covarianceTriple M = inner Real u (op u) := by
    rw [Matrix.inner_toEuclideanCLM]
    unfold covarianceTriple
    change Finset.sum Finset.univ
      (fun i => Finset.sum Finset.univ (fun j => M i i * M j j * M i j)) =
      Finset.sum Finset.univ (fun i => M i i *
        Finset.sum Finset.univ (fun j => M i j * M j j))
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  have hNorm : norm op = norm M := Matrix.l2_opNorm_toEuclideanCLM M
  calc
    _ = norm (inner Real u (op u)) := by rw [hTriple, Real.norm_eq_abs]
    _ <= norm u * norm (op u) := norm_inner_le_norm _ _
    _ <= norm u * (norm op * norm u) :=
      mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm op u) (norm_nonneg u)
    _ = norm M * norm u ^ 2 := by rw [hNorm]; ring
    _ = _ := by rw [EuclideanSpace.real_norm_sq_eq]; rfl

theorem covarianceCubic_bound (M : Matrix Iota Iota Real) (c : Real)
    (hEntry : forall i j, abs (M i j) <= c) :
    abs (covarianceCubic M) <= c * matrixSquareEnergy M := by
  calc
    _ <= Finset.sum Finset.univ (fun i => Finset.sum Finset.univ
        (fun j => abs (M i j ^ 3))) := by
      apply le_trans (Finset.abs_sum_le_sum_abs _ _)
      apply Finset.sum_le_sum
      intro i hi
      exact Finset.abs_sum_le_sum_abs _ _
    _ <= Finset.sum Finset.univ (fun i => Finset.sum Finset.univ
        (fun j => c * M i j ^ 2)) := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      calc
        _ = abs (M i j) * M i j ^ 2 := by rw [pow_succ, abs_mul, abs_sq]; ring
        _ <= _ := mul_le_mul_of_nonneg_right (hEntry i j) (sq_nonneg (M i j))
    _ = _ := by simp only [matrixSquareEnergy, Finset.mul_sum]

theorem covarianceCorrection_bound (M : Matrix Iota Iota Real) (c : Real)
    (hEntry : forall i j, abs (M i j) <= c) :
    abs (covarianceCorrection M) <=
      ((3 / 4 : Real) + norm M / 2) * covarianceDiagonalEnergy M +
        (c / 3) * matrixSquareEnergy M := by
  have hD := covarianceDiagonalEnergy_nonnegative M
  have hT := covarianceTriple_bound M
  have hC := covarianceCubic_bound M c hEntry
  have h0 := abs_add_le
    (-(3 / 4 : Real) * covarianceDiagonalEnergy M + (1 / 2 : Real) * covarianceTriple M)
    ((1 / 3 : Real) * covarianceCubic M)
  have h1 := abs_add_le (-(3 / 4 : Real) * covarianceDiagonalEnergy M)
    ((1 / 2 : Real) * covarianceTriple M)
  have hAbsD : abs (-(3 / 4 : Real) * covarianceDiagonalEnergy M) =
      (3 / 4 : Real) * covarianceDiagonalEnergy M := by
    rw [abs_mul, abs_of_nonneg hD]
    norm_num
  have hAbsT : abs ((1 / 2 : Real) * covarianceTriple M) =
      (1 / 2 : Real) * abs (covarianceTriple M) := by rw [abs_mul]; norm_num
  have hAbsC : abs ((1 / 3 : Real) * covarianceCubic M) =
      (1 / 3 : Real) * abs (covarianceCubic M) := by rw [abs_mul]; norm_num
  unfold covarianceCorrection
  nlinarith only [h0, h1, hAbsD, hAbsT, hAbsC, hT, hC]

variable [Nonempty Iota]

theorem resolventCovariance_norm_bound (Q : Matrix Iota Iota Real) (rho : Real)
    (hNorm : norm Q <= rho) (hRho : rho < 1) :
    (1 - rho) * norm (resolventCovariance Q) <= rho := by
  let R := Ring.inverse ((1 : Matrix Iota Iota Real) + Q)
  have hGap : 0 <= 1 - rho := le_of_lt (sub_pos.mpr hRho)
  have hNeumann : (1 - rho) * norm R <= 1 := by
    simpa only [norm_neg, sub_neg_eq_add] using
      l2_neumann_certificate (-Q) rho (by simpa only [norm_neg] using hNorm) hRho
  calc
    _ <= (1 - rho) * (norm Q * norm R) :=
      mul_le_mul_of_nonneg_left (norm_mul_le Q R) hGap
    _ = norm Q * ((1 - rho) * norm R) := by ring
    _ <= norm Q * 1 := mul_le_mul_of_nonneg_left hNeumann (norm_nonneg Q)
    _ <= rho := by simpa only [mul_one] using hNorm

theorem resolventCovariance_row_energy (Q : Matrix Iota Iota Real) (rho : Real)
    (hNorm : norm Q <= rho) (hRho : rho < 1) (i : Iota) :
    (1 - rho) ^ 2 *
      Finset.sum Finset.univ (fun j => resolventCovariance Q i j ^ 2) <=
      Finset.sum Finset.univ (fun j => Q i j ^ 2) := by
  let R := Ring.inverse ((1 : Matrix Iota Iota Real) + Q)
  let u : EuclideanSpace Real Iota := WithLp.toLp 2 (fun j => Q i j)
  let w : EuclideanSpace Real Iota := WithLp.toLp 2 (fun j => resolventCovariance Q i j)
  have hTranspose : R.conjTranspose = R.transpose := by
    ext j k
    simp [Matrix.conjTranspose_apply, Matrix.transpose_apply]
  have hTransposeNorm : norm R.transpose = norm R := by
    simpa only [hTranspose] using Matrix.l2_opNorm_conjTranspose R
  have hVector : WithLp.toLp 2 (R.transpose.mulVec u.ofLp) = w := by
    ext j
    change Finset.sum Finset.univ (fun k => R k j * Q i k) =
      Finset.sum Finset.univ (fun k => Q i k * R k j)
    apply Finset.sum_congr rfl
    intro k hk
    ring
  have hVectorNorm : norm w <= norm R * norm u := by
    have h := Matrix.l2_opNorm_mulVec R.transpose u
    change norm (WithLp.toLp 2 (R.transpose.mulVec u.ofLp) : EuclideanSpace Real Iota) <=
      norm R.transpose * norm u at h
    rw [hVector, hTransposeNorm] at h
    exact h
  have hNeumann : (1 - rho) * norm R <= 1 := by
    simpa only [norm_neg, sub_neg_eq_add] using
      l2_neumann_certificate (-Q) rho (by simpa only [norm_neg] using hNorm) hRho
  have hGap : 0 <= 1 - rho := le_of_lt (sub_pos.mpr hRho)
  have hScaled : (1 - rho) * norm w <= norm u := by
    calc
      _ <= (1 - rho) * (norm R * norm u) :=
        mul_le_mul_of_nonneg_left hVectorNorm hGap
      _ = ((1 - rho) * norm R) * norm u := by ring
      _ <= 1 * norm u := mul_le_mul_of_nonneg_right hNeumann (norm_nonneg u)
      _ = norm u := one_mul _
  have hSquared := mul_le_mul hScaled hScaled
    (mul_nonneg hGap (norm_nonneg w)) (norm_nonneg u)
  simpa only [<- pow_two, mul_pow, EuclideanSpace.real_norm_sq_eq] using hSquared

theorem resolventCovariance_energy_bound (Q : Matrix Iota Iota Real) (rho : Real)
    (hNorm : norm Q <= rho) (hRho : rho < 1) :
    (1 - rho) ^ 2 * matrixSquareEnergy (resolventCovariance Q) <= matrixSquareEnergy Q := by
  unfold matrixSquareEnergy
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum (fun i _ => resolventCovariance_row_energy Q rho hNorm hRho i)

theorem stochastic_block_covariance_energy_bound
    (T : Matrix Iota Iota Real) (q a rho : Real)
    (hq : (Fintype.card Iota : Real) * q = 1)
    (hrow : forall i, Finset.sum Finset.univ (fun j => T i j) = 1)
    (hnonneg : forall i j, 0 <= T i j) (hupper : forall i j, T i j <= a * q)
    (hRho : rho < 1) (hNorm : norm (centeredKernel T q) <= rho) :
    (1 - rho) ^ 2 * matrixSquareEnergy
        (resolventCovariance (bipartiteLift (centeredKernel T q))) <= 2 * (a - 1) := by
  let B := centeredKernel T q
  have hBlock : matrixSquareEnergy (bipartiteLift B) = 2 * matrixSquareEnergy B := by
    unfold matrixSquareEnergy
    simp only [Fintype.sum_sum_type]
    have hTransposeEnergy :
        Finset.sum Finset.univ (fun i => Finset.sum Finset.univ (fun j => B j i ^ 2)) =
          Finset.sum Finset.univ (fun i => Finset.sum Finset.univ (fun j => B i j ^ 2)) :=
      Finset.sum_comm
    simp [bipartiteLift, Matrix.fromBlocks, Matrix.transpose_apply]
    linarith only [hTransposeEnergy]
  have hEnergy : matrixSquareEnergy B <= a - 1 :=
    stochastic_total_energy T q a hq hrow hnonneg hupper
  have hBase := resolventCovariance_energy_bound (bipartiteLift B) rho
    (le_trans (bipartiteLift_l2_norm_le B) hNorm) hRho
  rw [hBlock] at hBase
  linarith only [hBase, hEnergy]

theorem stochastic_block_covariance_correction_bound
    (T : Matrix Iota Iota Real) (q a rho : Real)
    (hq : (Fintype.card Iota : Real) * q = 1) (ha : 1 <= a)
    (hrow : forall i, Finset.sum Finset.univ (fun j => T i j) = 1)
    (hcol : forall j, Finset.sum Finset.univ (fun i => T i j) = 1)
    (hnonneg : forall i j, 0 <= T i j) (hupper : forall i j, T i j <= a * q)
    (hRho : rho < 1) (hNorm : norm (centeredKernel T q) <= rho) :
    (1 - rho) ^ 3 *
      abs (covarianceCorrection (resolventCovariance (bipartiteLift (centeredKernel T q)))) <=
        8 * a ^ 2 * q := by
  let B := centeredKernel T q
  let Q := bipartiteLift B
  let G := resolventCovariance Q
  let g : Real := 1 - rho
  let c : Real := (2 - rho) * a * q / g
  let r : Real := rho / g
  let E : Real := 2 * (a - 1) / g ^ 2
  have hRho0 : 0 <= rho := le_trans (norm_nonneg _) hNorm
  have hGap : 0 < g := sub_pos.mpr hRho
  have hGapNe : Not (g = 0) := ne_of_gt hGap
  have hCardPos : 0 < (Fintype.card Iota : Real) :=
    Nat.cast_pos.mpr Fintype.card_pos
  have hq0 : 0 <= q := by nlinarith only [hq, hCardPos]
  have ha0 : 0 <= a := le_trans (by norm_num) ha
  have hTwoRho : 0 <= 2 - rho := by linarith only [hRho]
  have hc0 : 0 <= c := by dsimp only [c]; positivity
  have hr0 : 0 <= r := by dsimp only [r]; positivity
  have hEntry : forall i j, abs (G i j) <= c := by
    intro i j
    have hScaled := stochastic_block_covariance_entry_bound T q a rho hq ha
      hrow hcol hnonneg hupper hRho hNorm i j
    change g * norm (G i j) <= (2 - rho) * (a * q) at hScaled
    calc
      _ = (Inv.inv g) * (g * norm (G i j)) := by
        rw [Real.norm_eq_abs]
        field_simp
      _ <= (Inv.inv g) * ((2 - rho) * (a * q)) :=
        mul_le_mul_of_nonneg_left hScaled (le_of_lt (inv_pos.mpr hGap))
      _ = c := by dsimp only [c]; ring
  have hNormScaled : g * norm G <= rho :=
    resolventCovariance_norm_bound Q rho
      (le_trans (bipartiteLift_l2_norm_le B) hNorm) hRho
  have hNormDiv : norm G <= r := by
    calc
      _ = (Inv.inv g) * (g * norm G) := by field_simp
      _ <= (Inv.inv g) * rho :=
        mul_le_mul_of_nonneg_left hNormScaled (le_of_lt (inv_pos.mpr hGap))
      _ = r := by dsimp only [r]; ring
  have hEnergyScaled : g ^ 2 * matrixSquareEnergy G <= 2 * (a - 1) :=
    stochastic_block_covariance_energy_bound T q a rho hq hrow hnonneg hupper hRho hNorm
  have hEnergyDiv : matrixSquareEnergy G <= E := by
    calc
      _ = (Inv.inv (g ^ 2)) * (g ^ 2 * matrixSquareEnergy G) := by field_simp
      _ <= (Inv.inv (g ^ 2)) * (2 * (a - 1)) :=
        mul_le_mul_of_nonneg_left hEnergyScaled (by positivity)
      _ = E := by dsimp only [E]; ring
  have hDiag := covarianceDiagonalEnergy_entry_bound G c hc0 hEntry
  have hSumCard : (Fintype.card (Sum Iota Iota) : Real) =
      2 * (Fintype.card Iota : Real) := by
    simp only [Fintype.card_sum, Nat.cast_add]
    ring
  rw [hSumCard] at hDiag
  have hCoef : (3 / 4 : Real) + norm G / 2 <= (3 / 4 : Real) + r / 2 := by
    linarith only [hNormDiv]
  have hPair := mul_le_mul hCoef hDiag (covarianceDiagonalEnergy_nonnegative G)
    (show 0 <= (3 / 4 : Real) + r / 2 by positivity)
  have hThird := mul_le_mul_of_nonneg_left hEnergyDiv
    (show 0 <= c / 3 by positivity)
  have hBase := covarianceCorrection_bound G c hEntry
  have hCombined : abs (covarianceCorrection G) <=
      ((3 / 4 : Real) + r / 2) * (2 * (Fintype.card Iota : Real) * c ^ 2) +
        (c / 3) * E := by
    linarith only [hPair, hThird, hBase]
  have hNq : (Fintype.card Iota : Real) * q ^ 2 = q := by
    calc
      _ = ((Fintype.card Iota : Real) * q) * q := by ring
      _ = q := by rw [hq, one_mul]
  have hAlgebra :
      g ^ 3 * (((3 / 4 : Real) + r / 2) *
        (2 * (Fintype.card Iota : Real) * c ^ 2) + (c / 3) * E) =
      (((3 / 2 : Real) * g + rho) * (2 - rho) ^ 2 * a ^ 2) *
        ((Fintype.card Iota : Real) * q ^ 2) +
        (2 / 3 : Real) * (2 - rho) * a * (a - 1) * q := by
    dsimp only [r, c, E]
    field_simp
    <;> ring
  have hSquare : (2 - rho) ^ 2 <= 4 := by nlinarith only [hRho0, hRho]
  have hCoefSmall : (3 / 2 : Real) * g + rho <= 3 / 2 := by
    dsimp only [g]
    linarith only [hRho0]
  have hFirst : ((3 / 2 : Real) * g + rho) * (2 - rho) ^ 2 <= 6 := by
    have h := mul_le_mul hCoefSmall hSquare (sq_nonneg (2 - rho))
      (show (0 : Real) <= 3 / 2 by norm_num)
    norm_num at h
    exact h
  have hSecond : (2 - rho) * a * (a - 1) <= 2 * a ^ 2 := by
    have hA : a * (a - 1) <= a ^ 2 := by nlinarith only [ha0]
    have hAR : 0 <= a * (a - 1) := mul_nonneg ha0 (sub_nonneg.mpr ha)
    have h1 := mul_le_mul_of_nonneg_right
      (show 2 - rho <= 2 by linarith only [hRho0]) hAR
    nlinarith only [hA, h1]
  have hCoeffFinal :
      (((3 / 2 : Real) * g + rho) * (2 - rho) ^ 2 * a ^ 2) +
        (2 / 3 : Real) * (2 - rho) * a * (a - 1) <= 8 * a ^ 2 := by
    have h := mul_le_mul_of_nonneg_right hFirst (sq_nonneg a)
    nlinarith only [h, hSecond, sq_nonneg a]
  change g ^ 3 * abs (covarianceCorrection G) <= 8 * a ^ 2 * q
  calc
    _ <= g ^ 3 * (((3 / 4 : Real) + r / 2) *
        (2 * (Fintype.card Iota : Real) * c ^ 2) + (c / 3) * E) :=
      mul_le_mul_of_nonneg_left hCombined (pow_nonneg (le_of_lt hGap) 3)
    _ = ((((3 / 2 : Real) * g + rho) * (2 - rho) ^ 2 * a ^ 2) +
        (2 / 3 : Real) * (2 - rho) * a * (a - 1)) * q := by
      rw [hAlgebra, hNq]
      ring
    _ <= _ := mul_le_mul_of_nonneg_right hCoeffFinal hq0

end PrimeFactorOscillations

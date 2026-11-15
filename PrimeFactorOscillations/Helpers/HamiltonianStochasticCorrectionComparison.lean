/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianCovarianceCorrectionStability
import PrimeFactorOscillations.Helpers.HamiltonianRetainedCovarianceComparison

/-! # The full signed covariance correction after actual stochastic repair

The comparison retains the diagonal squares, mixed triple products and
entry cubes jointly. It includes both independent deleted supports and
every removed-by-removed overlap. Only their exact difference is bounded.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations

variable {Iota : Type*} [Fintype Iota] [DecidableEq Iota] [Nonempty Iota]

theorem stochastic_repaired_covariance_correction_comparison
    (T : Matrix Iota Iota Real) (S U : Finset Iota) (hCard : S.card = U.card)
    (q a rho : Real) (hq : (Fintype.card Iota : Real) * q = 1) (ha : 1 <= a)
    (hRow : forall i, Finset.sum Finset.univ (fun j => T i j) = 1)
    (hCol : forall j, Finset.sum Finset.univ (fun i => T i j) = 1)
    (hNonneg : forall i j, 0 <= T i j) (hUpper : forall i j, T i j <= a * q)
    (hNorm : norm (centeredKernel T q) <= rho) (hRho : rho < 1)
    (hSmall : (U.card : Real) * (a / (1 - rho)) ^ 3 * q <= 1 / 10000)
    (z : forall _i : (Compl.compl (S.disjSum U) : Finset (Sum Iota Iota)), Real)
    (hZ : norm z <= 20 * (U.card : Real) * a * q / (1 - rho)) :
    let D := S.disjSum U
    let R : Finset (Sum Iota Iota) := Compl.compl D
    let Omega := bipartiteLift (centeredKernel T q)
    let H := (1 : Matrix (Sum Iota Iota) (Sum Iota Iota) Real) + Omega
    let Gamma := Omega * Ring.inverse H
    let HR := H.submatrix (fun i : R => i.val) (fun i : R => i.val)
    let qNew := q / (1 - (U.card : Real) * q)
    let E := hamiltonianScalingPerturbation (hamiltonianRetainedKernel T S U)
      (hamiltonianRetainedCrossMask S U) z q qNew
    let GammaNew := (HR + E - 1) * Ring.inverse (HR + E)
    abs (covarianceCorrection GammaNew - covarianceCorrection Gamma) <=
      400000 * (U.card : Real) * (a / (1 - rho)) ^ 6 * q ^ 2 := by
  let delta := 1 - rho
  let r : Real := U.card
  let p := a / delta
  let D := S.disjSum U
  let R : Finset (Sum Iota Iota) := Compl.compl D
  let rr := fun i : R => (i.val : Sum Iota Iota)
  let Omega := bipartiteLift (centeredKernel T q)
  let H := (1 : Matrix (Sum Iota Iota) (Sum Iota Iota) Real) + Omega
  let Gamma := Omega * Ring.inverse H
  let HR := H.submatrix rr rr
  let qNew := q / (1 - r * q)
  let E := hamiltonianScalingPerturbation (hamiltonianRetainedKernel T S U)
    (hamiltonianRetainedCrossMask S U) z q qNew
  let GammaNew := (HR + E - 1) * Ring.inverse (HR + E)
  let c := 3 * p * q
  let eps := 3200 * r * p ^ 4 * q ^ 2
  have hDelta : 0 < delta := sub_pos.mpr hRho
  have hDen : Not (delta = 0) := ne_of_gt hDelta
  have hRho0 : 0 <= rho := le_trans (norm_nonneg _) hNorm
  have hDelta1 : delta <= 1 := by dsimp only [delta]; linarith only [hRho0]
  have ha0 : 0 <= a := le_trans (by norm_num) ha
  have hN : 0 < (Fintype.card Iota : Real) := Nat.cast_pos.mpr Fintype.card_pos
  have hq0 : 0 <= q := by nlinarith only [hq, hN]
  have hr : 0 <= r := Nat.cast_nonneg _
  have hp0 : 0 <= p := div_nonneg ha0 (le_of_lt hDelta)
  have hpClear : delta * p = a := by dsimp only [p]; field_simp
  have hp : 1 <= p := by nlinarith only [hpClear, hDelta1, hp0, ha]
  have hc : 0 <= c := mul_nonneg (mul_nonneg (by norm_num) hp0) hq0
  have hEps : 0 <= eps :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hr) (pow_nonneg hp0 4)) (sq_nonneg q)
  have hComparison := stochastic_retained_covariance_comparison T S U hCard q a rho hq ha
    hRow hCol hNonneg hUpper hNorm hRho hSmall z hZ
  have hNew (i j : R) : abs (GammaNew i j) <= c := hComparison.2.2.2 i j
  have hDiff (i j : R) : abs (GammaNew i j - Gamma i.val j.val) <= eps := hComparison.2.2.1 i j
  have hOld (i j : Sum Iota Iota) : abs (Gamma i j) <= c := by
    have h := stochastic_block_covariance_entry_bound T q a rho hq ha
      hRow hCol hNonneg hUpper hRho hNorm i j
    change delta * norm (Gamma i j) <= (2 - rho) * (a * q) at h
    rw [Real.norm_eq_abs] at h
    have hSigned := mul_nonneg hRho0 (mul_nonneg ha0 hq0)
    have hClear : delta * (2 * p * q) = 2 * a * q := by rw [<- hpClear]; ring
    have hTwo : abs (Gamma i j) <= 2 * p * q := by
      nlinarith only [h, hSigned, hClear, hDelta]
    change abs (Gamma i j) <= 3 * p * q
    nlinarith only [hTwo, mul_nonneg hp0 hq0]
  have hRaw := covarianceCorrection_supported_difference_bound Gamma D GammaNew c eps hc hEps
    hOld hNew hDiff
  have hDCard : (D.card : Real) = 2 * r := by
    simp only [D, Finset.card_disjSum, hCard, Nat.cast_add, r]
    ring
  have hFullQ : (Fintype.card (Sum Iota Iota) : Real) * q = 2 := by
    simp only [Fintype.card_sum, Nat.cast_add]
    nlinarith only [hq]
  have hRCard : (R.card : Real) <= (Fintype.card (Sum Iota Iota) : Real) := by
    have h : (R.card : Real) <= ((Finset.univ : Finset (Sum Iota Iota)).card : Real) :=
      Nat.cast_le.mpr (Finset.card_le_card (Finset.subset_univ R))
    simpa only [Finset.card_univ] using h
  have hRQ : (R.card : Real) * q <= 2 := by
    nlinarith only [mul_le_mul_of_nonneg_right hRCard hq0, hFullQ]
  have hRQ0 : 0 <= (R.card : Real) * q := mul_nonneg (Nat.cast_nonneg _) hq0
  have hRQSquare : ((R.card : Real) * q) ^ 2 <= 4 := by
    nlinarith only [hRQ, hRQ0]
  have hLinear : 2 * (R.card : Real) * c * eps <= 38400 * r * p ^ 5 * q ^ 2 := by
    calc
      _ = (19200 * r * p ^ 5 * q ^ 2) * ((R.card : Real) * q) := by
        dsimp only [c, eps]
        ring
      _ <= (19200 * r * p ^ 5 * q ^ 2) * 2 :=
        mul_le_mul_of_nonneg_left hRQ
          (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hr) (pow_nonneg hp0 5)) (sq_nonneg q))
      _ = _ := by ring
  have hCubic : 3 * (R.card : Real) ^ 2 * c ^ 2 * eps <= 345600 * r * p ^ 6 * q ^ 2 := by
    calc
      _ = (86400 * r * p ^ 6 * q ^ 2) * (((R.card : Real) * q) ^ 2) := by
        dsimp only [c, eps]
        ring
      _ <= (86400 * r * p ^ 6 * q ^ 2) * 4 :=
        mul_le_mul_of_nonneg_left hRQSquare
          (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hr) (pow_nonneg hp0 6)) (sq_nonneg q))
      _ = _ := by ring
  have hDeletedDiag : (D.card : Real) * c ^ 2 = 18 * r * p ^ 2 * q ^ 2 := by
    rw [hDCard]
    dsimp only [c]
    ring
  have hDeletedPair : 2 * (D.card : Real) * (Fintype.card (Sum Iota Iota) : Real) * c ^ 3 =
      216 * r * p ^ 3 * q ^ 2 := by
    calc
      _ = (108 * r * p ^ 3 * q ^ 2) * ((Fintype.card (Sum Iota Iota) : Real) * q) := by
        rw [hDCard]
        dsimp only [c]
        ring
      _ = _ := by rw [hFullQ]; ring
  have hp23 : p ^ 2 <= p ^ 3 := by
    have h := mul_le_mul_of_nonneg_left hp (sq_nonneg p)
    nlinarith only [h]
  have hp34 : p ^ 3 <= p ^ 4 := by
    have h := mul_le_mul_of_nonneg_left hp (pow_nonneg hp0 3)
    nlinarith only [h]
  have hp46 : p ^ 4 <= p ^ 6 := by
    have hpSq : 1 <= p ^ 2 := by nlinarith only [hp, hp0]
    have h := mul_le_mul_of_nonneg_left hpSq (pow_nonneg hp0 4)
    nlinarith only [h]
  have hp56 : p ^ 5 <= p ^ 6 := by
    have h := mul_le_mul_of_nonneg_left hp (pow_nonneg hp0 5)
    nlinarith only [h]
  have hScale (k : Nat) (hk : p ^ k <= p ^ 6) :
      r * p ^ k * q ^ 2 <= r * p ^ 6 * q ^ 2 := by
    have h := mul_le_mul_of_nonneg_left hk (mul_nonneg hr (sq_nonneg q))
    nlinarith only [h]
  have hTwo := hScale 2 (le_trans hp23 (le_trans hp34 hp46))
  have hThree := hScale 3 (le_trans hp34 hp46)
  have hFive := hScale 5 hp56
  have hBase : 0 <= r * p ^ 6 * q ^ 2 :=
    mul_nonneg (mul_nonneg hr (pow_nonneg hp0 6)) (sq_nonneg q)
  rw [hDeletedDiag, hDeletedPair] at hRaw
  change abs (covarianceCorrection GammaNew - covarianceCorrection Gamma) <=
    400000 * r * p ^ 6 * q ^ 2
  nlinarith only [hRaw, hLinear, hCubic, hTwo, hThree, hFive, hBase]

end PrimeFactorOscillations

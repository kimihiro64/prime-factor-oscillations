/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianMinorLinearCompensation
import PrimeFactorOscillations.Helpers.HamiltonianMinorLogError
import PrimeFactorOscillations.Helpers.HamiltonianMinorLogIdentity
import PrimeFactorOscillations.Helpers.HamiltonianMinorPermanentUniform
import PrimeFactorOscillations.Helpers.HamiltonianRepairedDeterminantTransport
import PrimeFactorOscillations.Helpers.HamiltonianStochasticDeterminantCost
import PrimeFactorOscillations.Helpers.HamiltonianStochasticScalingCost

/-! # The complete actual signed logarithmic minor error

All independently proved scaling, determinant, rank and normalized
permanent errors are consumed on the same actual positive repair.
The signed first-order term is canceled exactly before the error bound.
-/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations

def hamiltonianMinorLogBudget (delta r a : Real) : Real :=
  200000 * r ^ 3 * (a / delta) ^ 3 +
  10000000 * r ^ 2 * (a / delta) ^ 6 +
  2000000 * r * (a / delta) ^ 6 + 2 * r * (r + 1) +
  4 * abs (hamiltonianPermanentUniformBudget delta) * (1 + a) ^ 24 +
  16 * abs (hamiltonianPermanentUniformBudget (delta / 2)) * (1 + 2 * a) ^ 24

variable {Iota : Type*} [Fintype Iota] [DecidableEq Iota] [Nonempty Iota]

theorem stochastic_actual_minor_log_budget
    (T : Matrix Iota Iota Real) (S U : Finset Iota) (hCard : S.card = U.card)
    (q a delta : Real) (hN : 4 <= Fintype.card Iota)
    (hq : (Fintype.card Iota : Real) * q = 1) (ha : 1 <= a)
    (hDelta : 0 < delta) (hDelta1 : delta <= 1)
    (hHalf : (U.card : Real) <= (Fintype.card Iota : Real) / 2)
    (hRow : forall i, Finset.univ.sum (fun j => T i j) = 1)
    (hCol : forall j, Finset.univ.sum (fun i => T i j) = 1)
    (hNonneg : forall i j, 0 <= T i j) (hUpper : forall i j, T i j <= a * q)
    (hNorm : norm (centeredKernel T q) <= 1 - delta)
    (hStrong : (U.card : Real) * (a / delta) ^ 3 * q <= 1 / 10000)
    (z : forall _i : (Compl.compl (S.disjSum U) : Finset (Sum Iota Iota)), Real)
    (hZ : norm z <= 20 * (U.card : Real) * a * q / delta)
    (hClose : norm (z - (fun i : (Compl.compl (S.disjSum U) : Finset (Sum Iota Iota)) =>
      (hamiltonianRepairKernel T q).mulVec (hamiltonianDeletedSupportDefect T S U) i.val)) <=
        5000 * (U.card : Real) ^ 2 * a ^ 3 * q ^ 2 / delta ^ 3)
    (hPos : forall i, 0 < 1 + z i)
    (hScaling : forall i, (1 + z i) * (hamiltonianRetainedKernel T S U).mulVec (1 + z) i = 1)
    (hOldBound : hamiltonianPermanentRelativeCorrectionBound T q a delta)
    (hNewBound : hamiltonianPermanentRelativeCorrectionBound
      (hamiltonianRepairedSquareKernel T S U hCard z)
        (q / (1 - (U.card : Real) * q)) (2 * a) (delta / 2))
    (hOldPositive : hamiltonianPermanentPositiveData T q)
    (hNewPositive : hamiltonianPermanentPositiveData
      (hamiltonianRepairedSquareKernel T S U hCard z) (q / (1 - (U.card : Real) * q))) :
    let u := hamiltonianDeletedSupportIndicator S U
    let K := hamiltonianRepairKernel T q
    let G := resolventCovariance (bipartiteLift (centeredKernel T q))
    let h := fun i => -G i i
    let v := fun i => (1 / 2 : Real) * h i - K.mulVec h i
    let alpha := (U.card : Real) * ((U.card : Real) - 1) * q +
      dotProduct u (G.mulVec u) + 2 * dotProduct v u
    0 < rectangularMinorPermanent T (Compl.compl S) (Compl.compl U) /\
    abs (2 * Real.log (rectangularMinorPermanent T (Compl.compl S) (Compl.compl U) /
      weightedPermutationSum T) - alpha) <=
        hamiltonianMinorLogBudget delta (U.card : Real) a * q ^ 2 := by
  let n : Real := Fintype.card Iota
  let r : Real := U.card
  let p := a / delta
  let J : Finset Iota := Compl.compl U
  let m : Real := Fintype.card J
  let R : Finset (Sum Iota Iota) := Compl.compl (S.disjSum U)
  let qNew := q / (1 - r * q)
  let TNew := hamiltonianRepairedSquareKernel T S U hCard z
  let u := hamiltonianDeletedSupportIndicator S U
  let ell := hamiltonianDeletedSupportDefect T S U
  let K := hamiltonianRepairKernel T q
  let G := resolventCovariance (bipartiteLift (centeredKernel T q))
  let h := fun i => -G i i
  let v := fun i => (1 / 2 : Real) * h i - K.mulVec h i
  let alpha := r * (r - 1) * q + dotProduct u (G.mulVec u) + 2 * dotProduct v u
  let scaling := Finset.univ.sum (fun i : R => Real.log (1 + z i))
  let overlap := hamiltonianDeletedOverlap T S U
  let quad := dotProduct ell (K.mulVec ell)
  let traceD := Finset.univ.sum (fun d : S.disjSum U => G d.val d.val)
  let linear := dotProduct h (K.mulVec ell)
  let H := (1 : Matrix (Sum Iota Iota) (Sum Iota Iota) Real) +
    bipartiteLift (centeredKernel T q)
  let HR := H.submatrix (fun i : R => i.val) (fun i : R => i.val)
  let E := hamiltonianScalingPerturbation (hamiltonianRetainedKernel T S U)
    (hamiltonianRetainedCrossMask S U) z q qNew
  let detLog := Real.log (Matrix.det (HR + E) / Matrix.det H)
  let rankLog := hamiltonianLogPermanentNormalizer (Fintype.card J) -
    hamiltonianLogPermanentNormalizer (Fintype.card Iota)
  let normOld := hamiltonianNormalizedPermanent T q
  let normNew := hamiltonianNormalizedPermanent TNew qNew
  let correctionLog := Real.log normNew - Real.log normOld
  let eOld := normOld - (1 + stochasticPermanentFirstCorrection T q)
  let eNew := normNew - (1 + stochasticPermanentFirstCorrection TNew qNew)
  let cOld := (1 + a) ^ 24 * abs (hamiltonianPermanentUniformBudget delta)
  let cNew := 4 * (1 + 2 * a) ^ 24 * abs (hamiltonianPermanentUniformBudget (delta / 2))
  let errS := scaling - (r - overlap) - quad / 2
  let errD := detLog + traceD + 2 * linear
  let errF := 2 * rankLog - (2 * r - r * q)
  have hN4 : (4 : Real) <= n := by
    change (4 : Real) <= (Fintype.card Iota : Real)
    exact_mod_cast hN
  have hN0 : 0 < n := by linarith only [hN4]
  have hNne : Not (n = 0) := ne_of_gt hN0
  have hq0 : 0 <= q := by nlinarith only [hq, hN0]
  have hr0 : 0 <= r := Nat.cast_nonneg _
  have ha0 : 0 <= a := le_trans (by norm_num) ha
  have hDne : Not (delta = 0) := ne_of_gt hDelta
  have hp0 : 0 <= p := div_nonneg ha0 (le_of_lt hDelta)
  have hpClear : delta * p = a := by dsimp only [p]; field_simp
  have hp : 1 <= p := by nlinarith only [hpClear, hDelta1, hp0, ha]
  have hGap : 1 - (1 - delta) = delta := by ring
  have hRho : 1 - delta < 1 := by linarith only [hDelta]
  have hqValue : q = 1 / n := by
    calc
      _ = (n * q) / n := by field_simp [hNne]
      _ = _ := by rw [hq]
  have hQSquare : q ^ 2 = 1 / n ^ 2 := by rw [hqValue, div_pow, one_pow]
  have hJNat : Fintype.card J = Fintype.card Iota - U.card := by
    simp only [J, Fintype.card_coe, Finset.card_compl]
  have hJReal : m = n - r := by
    dsimp only [m]
    rw [hJNat, Nat.cast_sub (Finset.card_le_univ U)]
  have hMHalf : n / 2 <= m := by rw [hJReal]; linarith only [hHalf]
  have hM0 : 0 < m := by linarith only [hMHalf, hN0]
  have hMne : Not (m = 0) := ne_of_gt hM0
  have hM1 : 1 <= Fintype.card J := by
    have h : (1 : Real) <= m := by linarith only [hMHalf, hN4]
    change (1 : Real) <= (Fintype.card J : Real) at h
    exact_mod_cast h
  have hInverseM : 1 / m ^ 2 <= 4 * q ^ 2 := by
    have hMQ := mul_le_mul_of_nonneg_right hMHalf hq0
    have hMQHalf : 1 / 2 <= m * q := by nlinarith only [hMQ, hq]
    have hSquare := mul_le_mul hMQHalf hMQHalf (by norm_num : (0 : Real) <= 1 / 2)
      (show 0 <= m * q from mul_nonneg (le_of_lt hM0) hq0)
    have hClear : (1 / m ^ 2) * m ^ 2 = 1 := by field_simp [hMne]
    apply le_of_mul_le_mul_right _ (sq_pos_of_pos hM0)
    rw [hClear]
    nlinarith only [hSquare]
  have hStrongRepair : r * (a / (1 - (1 - delta))) ^ 3 * q <= 1 / 10000 := by
    simpa only [hGap] using hStrong
  have hZRepair : norm z <= 20 * r * a * q / (1 - (1 - delta)) := by
    simpa only [hGap] using hZ
  have hCloseRepair : norm (z - (fun i : R => K.mulVec ell i.val)) <=
      5000 * r ^ 2 * a ^ 3 * q ^ 2 / (1 - (1 - delta)) ^ 3 := by
    simpa only [hGap] using hClose
  have hWeak : r * a ^ 2 * q / (1 - (1 - delta)) ^ 2 <= 1 / 1000 := by
    have hPP : p ^ 2 <= p ^ 3 := by
      have h := mul_le_mul_of_nonneg_left hp (sq_nonneg p)
      nlinarith only [h]
    have h := mul_le_mul_of_nonneg_left hPP (mul_nonneg hr0 hq0)
    have hEq : r * a ^ 2 * q / (1 - (1 - delta)) ^ 2 = r * p ^ 2 * q := by
      rw [hGap]
      dsimp only [p]
      field_simp
    rw [hEq]
    nlinarith only [h, hStrong]
  have hZCost : norm z <= 20 * r * (a / (1 - (1 - delta))) * q := by
    calc
      _ <= 20 * r * a * q / delta := hZ
      _ = _ := by rw [hGap]; ring
  have hCloseCost : norm (z - (fun i : R => K.mulVec ell i.val)) <=
      5000 * (a / (1 - (1 - delta))) * (r * (a / (1 - (1 - delta))) * q) ^ 2 := by
    calc
      _ <= 5000 * r ^ 2 * a ^ 3 * q ^ 2 / delta ^ 3 := hClose
      _ = _ := by rw [hGap]; field_simp [hDne]
  have hSRaw := stochastic_deleted_support_scaling_cost T S U hCard q a (1 - delta)
    hq ha hRow hCol hNonneg hUpper hNorm hRho hWeak z hZCost hCloseCost hScaling
  simp only [hGap] at hSRaw
  have hS : abs errS <= 100000 * r ^ 3 * p ^ 3 * q ^ 2 := by
    change abs errS <= 100000 * r * p * (r * p * q) ^ 2 at hSRaw
    calc
      _ <= _ := hSRaw
      _ = _ := by ring
  have hDRaw := (stochastic_local_log_determinant_cost T S U hCard q a (1 - delta)
    hq ha hRow hCol hNonneg hUpper hNorm hRho hStrongRepair z hZRepair hCloseRepair).2
  simp only [hGap] at hDRaw
  have hD : abs errD <= 10000000 * r ^ 2 * p ^ 6 * q ^ 2 := hDRaw
  have hFRaw := hamiltonian_log_permanent_normalizer_rank_shift
    (Fintype.card Iota) U.card hN hHalf
  have hF : abs errF <= 2 * r * (r + 1) * q ^ 2 := by
    change abs (2 * (hamiltonianLogPermanentNormalizer (Fintype.card J) -
      hamiltonianLogPermanentNormalizer (Fintype.card Iota)) - (2 * r - r * q)) <= _
    rw [hJNat, hqValue]
    simpa only [div_eq_mul_inv, div_pow, one_pow, mul_one, one_mul, inv_pow, n, r] using hFRaw
  have hOldApprox := hOldBound.1
  change abs eOld <= (1 + a) ^ 24 * hamiltonianPermanentUniformBudget delta / n ^ 2 at hOldApprox
  have hOldError : abs eOld <= cOld * q ^ 2 := by
    calc
      _ <= (1 + a) ^ 24 * hamiltonianPermanentUniformBudget delta / n ^ 2 := hOldApprox
      _ <= cOld / n ^ 2 := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (le_abs_self _) (pow_nonneg (by linarith only [ha]) 24)) (sq_nonneg n)
      _ = _ := by rw [hQSquare]; ring
  have hNewApprox := hNewBound.1
  change abs eNew <= (1 + 2 * a) ^ 24 * hamiltonianPermanentUniformBudget (delta / 2) / m ^ 2 at hNewApprox
  have hNewCoefficient : 0 <= (1 + 2 * a) ^ 24 *
      abs (hamiltonianPermanentUniformBudget (delta / 2)) :=
    mul_nonneg (pow_nonneg (by linarith only [ha]) 24) (abs_nonneg _)
  have hNewError : abs eNew <= cNew * q ^ 2 := by
    calc
      _ <= (1 + 2 * a) ^ 24 * hamiltonianPermanentUniformBudget (delta / 2) / m ^ 2 := hNewApprox
      _ <= (1 + 2 * a) ^ 24 * abs (hamiltonianPermanentUniformBudget (delta / 2)) / m ^ 2 :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left (le_abs_self _) (pow_nonneg (by linarith only [ha]) 24)) (sq_nonneg m)
      _ = ((1 + 2 * a) ^ 24 * abs (hamiltonianPermanentUniformBudget (delta / 2))) * (1 / m ^ 2) := by ring
      _ <= ((1 + 2 * a) ^ 24 * abs (hamiltonianPermanentUniformBudget (delta / 2))) * (4 * q ^ 2) :=
        mul_le_mul_of_nonneg_left hInverseM hNewCoefficient
      _ = _ := by dsimp only [cNew]; ring
  have hCorrection := stochastic_repaired_first_correction_comparison T S U hCard q a (1 - delta)
    hN hq ha hRow hCol hNonneg hUpper hNorm hRho hStrongRepair z hZRepair
  simp only [hGap] at hCorrection
  have hOldIdentity : 1 + stochasticPermanentFirstCorrection T q + eOld = normOld := by
    dsimp only [eOld]
    ring
  have hNewIdentity : 1 + stochasticPermanentFirstCorrection TNew qNew + eNew = normNew := by
    dsimp only [eNew]
    ring
  have hLogBound := hamiltonian_signed_correction_log_difference
    (stochasticPermanentFirstCorrection T q) (stochasticPermanentFirstCorrection TNew qNew)
    eOld eNew (500000 * r * p ^ 6 * q ^ 2) (cOld * q ^ 2) (cNew * q ^ 2)
    (by rw [hOldIdentity]; exact hOldPositive.1)
    (by rw [hNewIdentity]; exact hNewPositive.1) hCorrection hOldError hNewError
  rw [hOldIdentity, hNewIdentity] at hLogBound
  have hL : abs correctionLog <= 2 * (500000 * r * p ^ 6 + cNew + cOld) * q ^ 2 := by
    calc
      _ <= _ := hLogBound
      _ = _ := by ring
  have hLog := hamiltonian_actual_minor_log_identity T S U hCard z q qNew
    (le_trans (by norm_num) hN) hM1 hPos hOldPositive hNewPositive
  have hGram := stochastic_repaired_log_gram_ratio T S U hCard q a (1 - delta) hq ha
    hNonneg hUpper hNorm hRho hStrongRepair z hZRepair
  have hComp := stochastic_deleted_full_first_order_compensation T S U hCard q (1 - delta)
    hq hRow hCol hNorm hRho
  let target := 2 * Real.log (rectangularMinorPermanent T (Compl.compl S) (Compl.compl U) /
    weightedPermutationSum T) - alpha
  have hIdentity : target = (-2) * errS - errD + errF + 2 * correctionLog := by
    change 2 * Real.log (rectangularMinorPermanent T (Compl.compl S) (Compl.compl U) /
      weightedPermutationSum T) - alpha = _
    dsimp only [errS, errD, errF, correctionLog, scaling, overlap, quad, traceD, linear, rankLog,
      detLog, alpha, TNew, qNew, normOld, normNew]
    linarith only [hLog.2, hGram, hComp]
  have hAbs : abs target <= 2 * abs errS + abs errD + abs errF + 2 * abs correctionLog := by
    rw [hIdentity]
    have h1 := abs_add_le ((-2) * errS - errD + errF) (2 * correctionLog)
    have h2 := abs_add_le ((-2) * errS - errD) errF
    have h3 := abs_add_le ((-2) * errS) (-errD)
    simp only [abs_mul, show abs (-2 : Real) = 2 by norm_num, abs_neg] at h3
    simp only [abs_mul, show abs (2 : Real) = 2 by norm_num] at h1
    change abs ((-2) * errS - errD) <= 2 * abs errS + abs errD at h3
    linarith only [h1, h2, h3]
  refine And.intro hLog.1 ?_
  change abs target <= hamiltonianMinorLogBudget delta r a * q ^ 2
  calc
    _ <= 2 * abs errS + abs errD + abs errF + 2 * abs correctionLog := hAbs
    _ <= 2 * (100000 * r ^ 3 * p ^ 3 * q ^ 2) +
        10000000 * r ^ 2 * p ^ 6 * q ^ 2 + 2 * r * (r + 1) * q ^ 2 +
        2 * (2 * (500000 * r * p ^ 6 + cNew + cOld) * q ^ 2) :=
      add_le_add (add_le_add (add_le_add
        (mul_le_mul_of_nonneg_left hS (by norm_num)) hD) hF)
          (mul_le_mul_of_nonneg_left hL (by norm_num))
    _ = _ := by dsimp only [hamiltonianMinorLogBudget, p, cOld, cNew]; ring

end PrimeFactorOscillations

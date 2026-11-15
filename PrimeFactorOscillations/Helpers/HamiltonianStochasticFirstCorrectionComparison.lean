/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianCovarianceTraceStability
import PrimeFactorOscillations.Helpers.HamiltonianFirstCorrectionRankShift
import PrimeFactorOscillations.Helpers.HamiltonianPermanentCorrectionTrace
import PrimeFactorOscillations.Helpers.HamiltonianStochasticCorrectionComparison

/-! # Complete first-correction budget on the actual retained covariance

The actual determinant-derivative identity, signed covariance polynomial,
all removed-coordinate products and the exact rank shift are combined.
The repaired covariance is computed from the full scaling perturbation.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations

variable {Iota : Type*} [Fintype Iota] [DecidableEq Iota] [Nonempty Iota]

theorem stochastic_repaired_trace_correction_comparison
    (T : Matrix Iota Iota Real) (S U : Finset Iota) (hCard : S.card = U.card)
    (q a rho : Real) (hN : 4 <= Fintype.card Iota)
    (hq : (Fintype.card Iota : Real) * q = 1) (ha : 1 <= a)
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
    let HR := H.submatrix (fun i : R => i.val) (fun i : R => i.val)
    let qNew := q / (1 - (U.card : Real) * q)
    let E := hamiltonianScalingPerturbation (hamiltonianRetainedKernel T S U)
      (hamiltonianRetainedCrossMask S U) z q qNew
    let GammaNew := (HR + E - 1) * Ring.inverse (HR + E)
    abs (covarianceTraceCorrection GammaNew
      ((Fintype.card Iota : Real) - (U.card : Real)) - stochasticPermanentFirstCorrection T q) <=
        500000 * (U.card : Real) * (a / (1 - rho)) ^ 6 * q ^ 2 := by
  let delta := 1 - rho
  let r : Real := U.card
  let p := a / delta
  let n : Real := Fintype.card Iota
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
  let XOld := (Matrix.trace Gamma) ^ 2 + 2 * Matrix.trace (Gamma * Gamma)
  let XNew := (Matrix.trace GammaNew) ^ 2 + 2 * Matrix.trace (GammaNew * GammaNew)
  have hDelta : 0 < delta := sub_pos.mpr hRho
  have hDen : Not (delta = 0) := ne_of_gt hDelta
  have hRho0 : 0 <= rho := le_trans (norm_nonneg _) hNorm
  have hDelta1 : delta <= 1 := by dsimp only [delta]; linarith only [hRho0]
  have ha0 : 0 <= a := le_trans (by norm_num) ha
  have hNReal : 4 <= n := by
    change (4 : Real) <= (Fintype.card Iota : Real)
    exact_mod_cast hN
  have hN0 : 0 < n := by linarith only [hNReal]
  have hq0 : 0 <= q := by nlinarith only [hq, hN0]
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
  have hPsi : abs (covarianceCorrection GammaNew - covarianceCorrection Gamma) <=
      400000 * r * p ^ 6 * q ^ 2 :=
    stochastic_repaired_covariance_correction_comparison T S U hCard q a rho hq ha
      hRow hCol hNonneg hUpper hNorm hRho hSmall z hZ
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
  have hRQSquare : ((R.card : Real) * q) ^ 2 <= 4 := by nlinarith only [hRQ, hRQ0]
  have hp12 : p <= p ^ 2 := by
    have h := mul_le_mul_of_nonneg_left hp hp0
    nlinarith only [h]
  have hp23 : p ^ 2 <= p ^ 3 := by
    have h := mul_le_mul_of_nonneg_left hp (sq_nonneg p)
    nlinarith only [h]
  have hp34 : p ^ 3 <= p ^ 4 := by
    have h := mul_le_mul_of_nonneg_left hp (pow_nonneg hp0 3)
    nlinarith only [h]
  have hp45 : p ^ 4 <= p ^ 5 := by
    have h := mul_le_mul_of_nonneg_left hp (pow_nonneg hp0 4)
    nlinarith only [h]
  have hp56 : p ^ 5 <= p ^ 6 := by
    have h := mul_le_mul_of_nonneg_left hp (pow_nonneg hp0 5)
    nlinarith only [h]
  have hp14 : p <= p ^ 4 := le_trans hp12 (le_trans hp23 hp34)
  have hp25 : p ^ 2 <= p ^ 5 := le_trans hp23 (le_trans hp34 hp45)
  have hP14 := mul_le_mul_of_nonneg_left hp14 (mul_nonneg hr hq0)
  have hP25 := mul_le_mul_of_nonneg_left hp25 (mul_nonneg hr hq0)
  have hP25Sq := mul_le_mul_of_nonneg_left hp25 (mul_nonneg hr (sq_nonneg q))
  have hP56Sq := mul_le_mul_of_nonneg_left hp56 (mul_nonneg hr (sq_nonneg q))
  have hTraceRaw := hamiltonian_trace_supported_difference_bound Gamma D GammaNew c eps hOld hDiff
  have hSquareRaw := hamiltonian_trace_square_supported_difference_bound Gamma D GammaNew c eps
    hc hEps hOld hNew hDiff
  change abs (Matrix.trace GammaNew - Matrix.trace Gamma) <=
    (R.card : Real) * eps + (D.card : Real) * c at hTraceRaw
  change abs (Matrix.trace (GammaNew * GammaNew) - Matrix.trace (Gamma * Gamma)) <=
    2 * (R.card : Real) ^ 2 * c * eps +
      2 * (D.card : Real) * (Fintype.card (Sum Iota Iota) : Real) * c ^ 2 at hSquareRaw
  have hTraceLocal : (R.card : Real) * eps <= 6400 * r * p ^ 4 * q := by
    calc
      _ = (3200 * r * p ^ 4 * q) * ((R.card : Real) * q) := by dsimp only [eps]; ring
      _ <= (3200 * r * p ^ 4 * q) * 2 :=
        mul_le_mul_of_nonneg_left hRQ
          (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hr) (pow_nonneg hp0 4)) hq0)
      _ = _ := by ring
  have hTraceDeleted : (D.card : Real) * c = 6 * r * p * q := by
    rw [hDCard]
    dsimp only [c]
    ring
  have hTraceDifference : abs (Matrix.trace GammaNew - Matrix.trace Gamma) <= 6406 * r * p ^ 4 * q := by
    rw [hTraceDeleted] at hTraceRaw
    nlinarith only [hTraceRaw, hTraceLocal, hP14]
  have hSquareLocal : 2 * (R.card : Real) ^ 2 * c * eps <= 76800 * r * p ^ 5 * q := by
    calc
      _ = (19200 * r * p ^ 5 * q) * (((R.card : Real) * q) ^ 2) := by dsimp only [c, eps]; ring
      _ <= (19200 * r * p ^ 5 * q) * 4 :=
        mul_le_mul_of_nonneg_left hRQSquare
          (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hr) (pow_nonneg hp0 5)) hq0)
      _ = _ := by ring
  have hSquareDeleted : 2 * (D.card : Real) * (Fintype.card (Sum Iota Iota) : Real) * c ^ 2 =
      72 * r * p ^ 2 * q := by
    calc
      _ = (36 * r * p ^ 2 * q) * ((Fintype.card (Sum Iota Iota) : Real) * q) := by
        rw [hDCard]
        dsimp only [c]
        ring
      _ = _ := by rw [hFullQ]; ring
  have hSquareDifference : abs (Matrix.trace (GammaNew * GammaNew) - Matrix.trace (Gamma * Gamma)) <=
      76872 * r * p ^ 5 * q := by
    rw [hSquareDeleted] at hSquareRaw
    nlinarith only [hSquareRaw, hSquareLocal, hP25]
  have hTraceOld : abs (Matrix.trace Gamma) <= 6 * p := by
    calc
      _ <= (Fintype.card (Sum Iota Iota) : Real) * c := hamiltonian_trace_entry_bound Gamma c hOld
      _ = 3 * p * ((Fintype.card (Sum Iota Iota) : Real) * q) := by dsimp only [c]; ring
      _ = _ := by rw [hFullQ]; ring
  have hTraceNew : abs (Matrix.trace GammaNew) <= 6 * p := by
    calc
      _ <= (R.card : Real) * c := by
        simpa only [Fintype.card_coe] using hamiltonian_trace_entry_bound GammaNew c hNew
      _ = 3 * p * ((R.card : Real) * q) := by dsimp only [c]; ring
      _ <= 3 * p * 2 := mul_le_mul_of_nonneg_left hRQ (mul_nonneg (by norm_num) hp0)
      _ = _ := by ring
  have hTraceSum : abs (Matrix.trace GammaNew + Matrix.trace Gamma) <= 12 * p := by
    have h := abs_add_le (Matrix.trace GammaNew) (Matrix.trace Gamma)
    linarith only [h, hTraceOld, hTraceNew]
  have hSquaredTraceDifference : abs ((Matrix.trace GammaNew) ^ 2 - (Matrix.trace Gamma) ^ 2) <=
      76872 * r * p ^ 5 * q := by
    have hEq : (Matrix.trace GammaNew) ^ 2 - (Matrix.trace Gamma) ^ 2 =
        (Matrix.trace GammaNew - Matrix.trace Gamma) * (Matrix.trace GammaNew + Matrix.trace Gamma) := by ring
    rw [hEq, abs_mul]
    have h := mul_le_mul hTraceDifference hTraceSum (abs_nonneg _)
      (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0 : Real) <= 6406) hr) (pow_nonneg hp0 4)) hq0)
    nlinarith only [h]
  have hNumeratorDifference : abs (XNew - XOld) <= 230616 * r * p ^ 5 * q := by
    have hEq : XNew - XOld =
        ((Matrix.trace GammaNew) ^ 2 - (Matrix.trace Gamma) ^ 2) +
          2 * (Matrix.trace (GammaNew * GammaNew) - Matrix.trace (Gamma * Gamma)) := by
      dsimp only [XNew, XOld]
      ring
    rw [hEq]
    have h := abs_add_le ((Matrix.trace GammaNew) ^ 2 - (Matrix.trace Gamma) ^ 2)
      (2 * (Matrix.trace (GammaNew * GammaNew) - Matrix.trace (Gamma * Gamma)))
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : Real) <= 2)] at h
    linarith only [h, hSquaredTraceDifference, hSquareDifference]
  have hOldSquare : abs (Matrix.trace (Gamma * Gamma)) <= 36 * p ^ 2 := by
    have h := hamiltonian_trace_product_entry_bound Gamma Gamma c c hc hc hOld hOld
    have hEq : (Fintype.card (Sum Iota Iota) : Real) ^ 2 * c * c = 36 * p ^ 2 := by
      calc
        _ = 9 * p ^ 2 * (((Fintype.card (Sum Iota Iota) : Real) * q) ^ 2) := by dsimp only [c]; ring
        _ = _ := by rw [hFullQ]; ring
    rw [hEq] at h
    exact h
  have hTraceOldSquared : (Matrix.trace Gamma) ^ 2 <= 36 * p ^ 2 := by
    have h := mul_le_mul hTraceOld hTraceOld (abs_nonneg _) (mul_nonneg (by norm_num) hp0)
    rw [<- pow_two, sq_abs] at h
    nlinarith only [h]
  have hNumeratorOld : abs XOld <= 108 * p ^ 2 := by
    have h := abs_add_le ((Matrix.trace Gamma) ^ 2) (2 * Matrix.trace (Gamma * Gamma))
    rw [abs_of_nonneg (sq_nonneg (Matrix.trace Gamma)), abs_mul,
      abs_of_nonneg (by norm_num : (0 : Real) <= 2)] at h
    change abs ((Matrix.trace Gamma) ^ 2 + 2 * Matrix.trace (Gamma * Gamma)) <= _
    linarith only [h, hTraceOldSquared, hOldSquare]
  have hp3 : 1 <= p ^ 3 := le_trans hp (le_trans hp12 hp23)
  have hRQSmall : r * q <= 1 / 4 := by
    have h := mul_le_mul_of_nonneg_left hp3 (mul_nonneg hr hq0)
    have hStrong : r * p ^ 3 * q <= 1 / 10000 := hSmall
    nlinarith only [h, hStrong]
  have hNormalized := hamiltonian_normalized_correction_difference n r q XNew XOld
    (230616 * r * p ^ 5 * q) (108 * p ^ 2) hNReal hr hq hRQSmall
      (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hr) (pow_nonneg hp0 5)) hq0)
      (mul_nonneg (by norm_num) (sq_nonneg p)) hNumeratorDifference hNumeratorOld
  have hBase5 : 0 <= r * p ^ 5 * q ^ 2 :=
    mul_nonneg (mul_nonneg hr (pow_nonneg hp0 5)) (sq_nonneg q)
  have hFraction : abs (XNew / (8 * (n - r - 1)) - XOld / (8 * (n - 1))) <=
      60000 * r * p ^ 5 * q ^ 2 := by
    nlinarith only [hNormalized, hP25Sq, hBase5]
  have hN2 : 2 <= Fintype.card Iota := le_trans (by decide : 2 <= 4) hN
  rw [stochasticPermanentFirstCorrection_trace_formula T q rho hN2 hNorm hRho]
  change abs (covarianceTraceCorrection GammaNew (n - r) - covarianceTraceCorrection Gamma n) <=
    500000 * r * p ^ 6 * q ^ 2
  have hExact : covarianceTraceCorrection GammaNew (n - r) - covarianceTraceCorrection Gamma n =
      (XNew / (8 * (n - r - 1)) - XOld / (8 * (n - 1))) +
        (covarianceCorrection GammaNew - covarianceCorrection Gamma) := by
    unfold covarianceTraceCorrection
    dsimp only [XNew, XOld]
    ring
  rw [hExact]
  have hTriangle := abs_add_le (XNew / (8 * (n - r - 1)) - XOld / (8 * (n - 1)))
    (covarianceCorrection GammaNew - covarianceCorrection Gamma)
  have hBase6 : 0 <= r * p ^ 6 * q ^ 2 :=
    mul_nonneg (mul_nonneg hr (pow_nonneg hp0 6)) (sq_nonneg q)
  nlinarith only [hTriangle, hFraction, hPsi, hP56Sq, hBase6]

end PrimeFactorOscillations

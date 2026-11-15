/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianDeletedDeterminantCost
import PrimeFactorOscillations.Helpers.HamiltonianScalingDeterminantRemainder
import PrimeFactorOscillations.Helpers.HamiltonianStochasticScalingTrace

/-! # Complete actual local determinant cost with positive repair

The full signed deleted trace and K-ell compensation are retained.
All support, Schur, quadratic and centering errors are included.
The existence consumer derives the actual positive repair as well.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations

private theorem strongSmallnessToRepair
    (r a q rho : Real) (hr : 0 <= r) (hq : 0 <= q) (ha : 1 <= a)
    (hRho0 : 0 <= rho) (hRho : rho < 1)
    (hStrong : r * (a / (1 - rho)) ^ 3 * q <= 1 / 10000) :
    r * a ^ 2 * q / (1 - rho) ^ 2 <= 1 / 1000 := by
  let delta := 1 - rho
  let p := a / delta
  have hDelta : 0 < delta := sub_pos.mpr hRho
  have hDen : Not (delta = 0) := ne_of_gt hDelta
  have hDelta1 : delta <= 1 := by dsimp only [delta]; linarith only [hRho0]
  have ha0 : 0 <= a := le_trans (by norm_num) ha
  have hp0 : 0 <= p := div_nonneg ha0 (le_of_lt hDelta)
  have hpClear : delta * p = a := by dsimp only [p]; field_simp
  have hp : 1 <= p := by nlinarith only [hpClear, hDelta1, hp0, ha]
  have hPP : p ^ 2 <= p ^ 3 := by
    have h := mul_le_mul_of_nonneg_left hp (sq_nonneg p)
    nlinarith only [h]
  have hScaled : r * p ^ 2 * q <= r * p ^ 3 * q := by
    have h := mul_le_mul_of_nonneg_left hPP (mul_nonneg hr hq)
    nlinarith only [h]
  have hWeakEq : r * a ^ 2 * q / (1 - rho) ^ 2 = r * p ^ 2 * q := by
    dsimp only [p, delta]
    field_simp
  rw [hWeakEq]
  change r * p ^ 3 * q <= 1 / 10000 at hStrong
  linarith only [hScaled, hStrong]

variable {Iota : Type*} [Fintype Iota] [DecidableEq Iota] [Nonempty Iota]

theorem stochastic_local_log_determinant_cost
    (T : Matrix Iota Iota Real) (S U : Finset Iota) (hCard : S.card = U.card)
    (q a rho : Real) (hq : (Fintype.card Iota : Real) * q = 1) (ha : 1 <= a)
    (hRow : forall i, Finset.sum Finset.univ (fun j => T i j) = 1)
    (hCol : forall j, Finset.sum Finset.univ (fun i => T i j) = 1)
    (hNonneg : forall i j, 0 <= T i j) (hUpper : forall i j, T i j <= a * q)
    (hNorm : norm (centeredKernel T q) <= rho) (hRho : rho < 1)
    (hSmall : (U.card : Real) * (a / (1 - rho)) ^ 3 * q <= 1 / 10000)
    (z : forall _i : (Compl.compl (S.disjSum U) : Finset (Sum Iota Iota)), Real)
    (hZ : norm z <= 20 * (U.card : Real) * a * q / (1 - rho))
    (hClose : norm (z -
      (fun i : (Compl.compl (S.disjSum U) : Finset (Sum Iota Iota)) =>
        (hamiltonianRepairKernel T q).mulVec (hamiltonianDeletedSupportDefect T S U) i.val)) <=
      5000 * (U.card : Real) ^ 2 * a ^ 3 * q ^ 2 / (1 - rho) ^ 3) :
    let D := S.disjSum U
    let R : Finset (Sum Iota Iota) := Compl.compl D
    let Omega := bipartiteLift (centeredKernel T q)
    let H := (1 : Matrix (Sum Iota Iota) (Sum Iota Iota) Real) + Omega
    let Gamma := Omega * Ring.inverse H
    let GD := Gamma.submatrix (fun i : D => i.val) (fun i : D => i.val)
    let HR := H.submatrix (fun i : R => i.val) (fun i : R => i.val)
    let qNew := q / (1 - (U.card : Real) * q)
    let E := hamiltonianScalingPerturbation (hamiltonianRetainedKernel T S U)
      (hamiltonianRetainedCrossMask S U) z q qNew
    let k := (hamiltonianRepairKernel T q).mulVec (hamiltonianDeletedSupportDefect T S U)
    0 < Matrix.det (HR + E) / Matrix.det H /\
    abs (Real.log (Matrix.det (HR + E) / Matrix.det H) + Matrix.trace GD +
      2 * Finset.sum Finset.univ (fun i : Sum Iota Iota => (-Gamma i i) * k i)) <=
        10000000 * (U.card : Real) ^ 2 * (a / (1 - rho)) ^ 6 * q ^ 2 := by
  let delta := 1 - rho
  let r : Real := U.card
  let p := a / delta
  let D := S.disjSum U
  let R : Finset (Sum Iota Iota) := Compl.compl D
  let Omega := bipartiteLift (centeredKernel T q)
  let H := (1 : Matrix (Sum Iota Iota) (Sum Iota Iota) Real) + Omega
  let R0 := Ring.inverse H
  let Gamma := Omega * R0
  let GD := Gamma.submatrix (fun i : D => i.val) (fun i : D => i.val)
  let HR := H.submatrix (fun i : R => i.val) (fun i : R => i.val)
  let J := hamiltonianBoundaryKernel R0 D
  let qNew := q / (1 - r * q)
  let E := hamiltonianScalingPerturbation (hamiltonianRetainedKernel T S U)
    (hamiltonianRetainedCrossMask S U) z q qNew
  let k := (hamiltonianRepairKernel T q).mulVec (hamiltonianDeletedSupportDefect T S U)
  let w := Finset.sum Finset.univ (fun i : Sum Iota Iota => (-Gamma i i) * k i)
  let u := Matrix.det HR / Matrix.det H
  let v := Matrix.det (HR + E) / Matrix.det HR
  let f := Matrix.det (HR + E) / Matrix.det H
  let a0 := Real.log u + Matrix.trace GD
  let b0 := Real.log v - Matrix.trace (J * E)
  let c0 := Matrix.trace (J * E) + 2 * w
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
  have hWeak := strongSmallnessToRepair r a q rho hr hq0 ha hRho0 hRho hSmall
  have hDeleted := stochastic_deleted_principal_log_determinant T S U hCard q a rho hq ha
    hRow hCol hNonneg hUpper hNorm hRho hWeak
  have hScaling := stochastic_scaling_determinant_remainder T S U hCard q a rho hq ha
    hRow hCol hNonneg hUpper hNorm hRho hSmall z hZ
  have hTrace := stochastic_signed_scaling_trace T S U hCard q a rho hq ha
    hRow hCol hNonneg hUpper hNorm hRho hWeak z hZ hClose
  have hU : 0 < u := hDeleted.1
  have hV : 0 < v := hScaling.1
  have hDetH : Not (Matrix.det H = 0) := by
    intro h
    have hPos := hU
    dsimp only [u] at hPos
    norm_num [h] at hPos
  have hDetHR : Not (Matrix.det HR = 0) := by
    intro h
    have hPos := hU
    dsimp only [u] at hPos
    norm_num [h] at hPos
  have hFactor : f = v * u := by
    dsimp only [f, v, u]
    field_simp
  have hF : 0 < f := by rw [hFactor]; exact mul_pos hV hU
  have hLog : Real.log f = Real.log u + Real.log v := by
    rw [hFactor, Real.log_mul (ne_of_gt hV) (ne_of_gt hU)]
    ring
  have hFirstEq : 128 * (r * a * q / (1 - rho)) ^ 2 = 128 * r ^ 2 * p ^ 2 * q ^ 2 := by
    dsimp only [p, delta]
    ring
  have hFirst : abs a0 <= 128 * r ^ 2 * p ^ 2 * q ^ 2 := by
    have h := hDeleted.2
    change abs a0 <= 128 * (r * a * q / (1 - rho)) ^ 2 at h
    rw [hFirstEq] at h
    exact h
  have hSecond : abs b0 <= 2230272 * r ^ 2 * p ^ 6 * q ^ 2 := hScaling.2
  have hThird : abs c0 <= 60000 * r ^ 2 * p ^ 4 * q ^ 2 := hTrace
  have hpSq : 1 <= p ^ 2 := by nlinarith only [hp, hp0]
  have hp24 : p ^ 2 <= p ^ 4 := by
    have h := mul_le_mul_of_nonneg_left hpSq (sq_nonneg p)
    nlinarith only [h]
  have hp46 : p ^ 4 <= p ^ 6 := by
    have h := mul_le_mul_of_nonneg_left hpSq (pow_nonneg hp0 4)
    nlinarith only [h]
  have hp26 : p ^ 2 <= p ^ 6 := le_trans hp24 hp46
  have hLow2 : r ^ 2 * p ^ 2 * q ^ 2 <= r ^ 2 * p ^ 6 * q ^ 2 := by
    have h := mul_le_mul_of_nonneg_right hp26 (mul_nonneg (sq_nonneg r) (sq_nonneg q))
    nlinarith only [h]
  have hLow4 : r ^ 2 * p ^ 4 * q ^ 2 <= r ^ 2 * p ^ 6 * q ^ 2 := by
    have h := mul_le_mul_of_nonneg_right hp46 (mul_nonneg (sq_nonneg r) (sq_nonneg q))
    nlinarith only [h]
  have hBase : 0 <= r ^ 2 * p ^ 6 * q ^ 2 :=
    mul_nonneg (mul_nonneg (sq_nonneg r) (pow_nonneg hp0 6)) (sq_nonneg q)
  have hSum : Real.log f + Matrix.trace GD + 2 * w = a0 + b0 + c0 := by
    rw [hLog]
    dsimp only [a0, b0, c0]
    ring
  have hOne : abs (a0 + b0 + c0) <= abs (a0 + b0) + abs c0 := abs_add_le _ _
  have hTwo : abs (a0 + b0) <= abs a0 + abs b0 := abs_add_le _ _
  change 0 < f /\ abs (Real.log f + Matrix.trace GD + 2 * w) <=
    10000000 * r ^ 2 * p ^ 6 * q ^ 2
  refine And.intro hF ?_
  rw [hSum]
  nlinarith only [hOne, hTwo, hFirst, hSecond, hThird, hLow2, hLow4, hBase]

theorem stochastic_local_log_determinant_cost_exists
    (T : Matrix Iota Iota Real) (S U : Finset Iota) (hCard : S.card = U.card)
    (q a rho : Real) (hq : (Fintype.card Iota : Real) * q = 1) (ha : 1 <= a)
    (hRow : forall i, Finset.sum Finset.univ (fun j => T i j) = 1)
    (hCol : forall j, Finset.sum Finset.univ (fun i => T i j) = 1)
    (hNonneg : forall i j, 0 <= T i j) (hUpper : forall i j, T i j <= a * q)
    (hNorm : norm (centeredKernel T q) <= rho) (hRho : rho < 1)
    (hSmall : (U.card : Real) * (a / (1 - rho)) ^ 3 * q <= 1 / 10000) :
    let D := S.disjSum U
    let R : Finset (Sum Iota Iota) := Compl.compl D
    let Omega := bipartiteLift (centeredKernel T q)
    let H := (1 : Matrix (Sum Iota Iota) (Sum Iota Iota) Real) + Omega
    let Gamma := Omega * Ring.inverse H
    let GD := Gamma.submatrix (fun i : D => i.val) (fun i : D => i.val)
    let HR := H.submatrix (fun i : R => i.val) (fun i : R => i.val)
    let qNew := q / (1 - (U.card : Real) * q)
    let E := fun z : R -> Real => hamiltonianScalingPerturbation (hamiltonianRetainedKernel T S U)
      (hamiltonianRetainedCrossMask S U) z q qNew
    let k := (hamiltonianRepairKernel T q).mulVec (hamiltonianDeletedSupportDefect T S U)
    exists z : R -> Real,
      norm z <= 20 * (U.card : Real) * a * q / (1 - rho) /\
      norm (z - (fun i : R => k i.val)) <=
        5000 * (U.card : Real) ^ 2 * a ^ 3 * q ^ 2 / (1 - rho) ^ 3 /\
      (forall i : R, 0 < 1 + z i) /\
      (forall i : R, (1 + z i) * (hamiltonianRetainedKernel T S U).mulVec (1 + z) i = 1) /\
      0 < Matrix.det (HR + E z) / Matrix.det H /\
      abs (Real.log (Matrix.det (HR + E z) / Matrix.det H) + Matrix.trace GD +
        2 * Finset.sum Finset.univ (fun i : Sum Iota Iota => (-Gamma i i) * k i)) <=
          10000000 * (U.card : Real) ^ 2 * (a / (1 - rho)) ^ 6 * q ^ 2 := by
  have hRho0 : 0 <= rho := le_trans (norm_nonneg _) hNorm
  have hN : 0 < (Fintype.card Iota : Real) := Nat.cast_pos.mpr Fintype.card_pos
  have hq0 : 0 <= q := by nlinarith only [hq, hN]
  have hWeak := strongSmallnessToRepair (U.card : Real) a q rho
    (Nat.cast_nonneg _) hq0 ha hRho0 hRho hSmall
  have hRepair := stochastic_deleted_support_repair_exists T S U hCard q a rho hq ha
    hRow hCol hNonneg hUpper hNorm hRho hWeak
  let z := Classical.choose hRepair
  have hz := Classical.choose_spec hRepair
  have hCost := stochastic_local_log_determinant_cost T S U hCard q a rho hq ha
    hRow hCol hNonneg hUpper hNorm hRho hSmall z hz.1 hz.2.1
  exact Exists.intro z (And.intro hz.1 (And.intro hz.2.1
    (And.intro hz.2.2.1 (And.intro hz.2.2.2 hCost))))

end PrimeFactorOscillations

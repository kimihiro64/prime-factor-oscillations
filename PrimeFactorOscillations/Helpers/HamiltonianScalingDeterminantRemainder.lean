/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianCovarianceBoundaryInverse
import PrimeFactorOscillations.Helpers.HamiltonianLogDeterminantEntryBudget
import PrimeFactorOscillations.Helpers.HamiltonianScalingPerturbation

/-! # The actual scaling determinant remainder with signed trace retained

The full retained inverse and the complete scaling/centering perturbation
are used. The signed trace is untouched. All higher determinant
coefficients receive a uniform explicit two-power remainder.
-/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations

variable {Iota : Type*} [Fintype Iota] [DecidableEq Iota] [Nonempty Iota]

theorem stochastic_scaling_determinant_remainder
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
    let HR := H.submatrix (fun i : R => i.val) (fun i : R => i.val)
    let J := hamiltonianBoundaryKernel (Ring.inverse H) D
    let qNew := q / (1 - (U.card : Real) * q)
    let E := hamiltonianScalingPerturbation (hamiltonianRetainedKernel T S U)
      (hamiltonianRetainedCrossMask S U) z q qNew
    0 < Matrix.det (HR + E) / Matrix.det HR /\
    abs (Real.log (Matrix.det (HR + E) / Matrix.det HR) - Matrix.trace (J * E)) <=
      2230272 * (U.card : Real) ^ 2 * (a / (1 - rho)) ^ 6 * q ^ 2 := by
  let delta := 1 - rho
  let r : Real := U.card
  let p := a / delta
  let D := S.disjSum U
  let R : Finset (Sum Iota Iota) := Compl.compl D
  let Omega := bipartiteLift (centeredKernel T q)
  let H := (1 : Matrix (Sum Iota Iota) (Sum Iota Iota) Real) + Omega
  let HR := H.submatrix (fun i : R => i.val) (fun i : R => i.val)
  let J := hamiltonianBoundaryKernel (Ring.inverse H) D
  let qNew := q / (1 - r * q)
  let E := hamiltonianScalingPerturbation (hamiltonianRetainedKernel T S U)
    (hamiltonianRetainedCrossMask S U) z q qNew
  let e := 44 * r * p ^ 2 * q ^ 2
  let eps := 264 * r * p ^ 3 * q ^ 2
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
  have he : 0 <= e := by dsimp only [e]; positivity
  have hEps : 0 <= eps := by dsimp only [eps]; positivity
  have hStrong : r * p ^ 3 * q <= 1 / 10000 := hSmall
  have hPP : p ^ 2 <= p ^ 3 := by
    have h := mul_le_mul_of_nonneg_left hp (sq_nonneg p)
    nlinarith only [h]
  have hWeakToStrong : r * p ^ 2 * q <= r * p ^ 3 * q := by
    have h := mul_le_mul_of_nonneg_left hPP (mul_nonneg hr hq0)
    nlinarith only [h]
  have hWeakEq : r * a ^ 2 * q / (1 - rho) ^ 2 = r * p ^ 2 * q := by
    dsimp only [p, delta]
    field_simp
  have hWeak : r * a ^ 2 * q / (1 - rho) ^ 2 <= 1 / 1000 := by
    rw [hWeakEq]
    exact le_trans hWeakToStrong (le_trans hStrong (by norm_num))
  have hInverse := stochastic_retained_covariance_inverse_budgets T S U hCard q a rho hq ha
    hRow hCol hNonneg hUpper hNorm hRho hWeak
  have hActualInverse : HR * J = 1 := hInverse.1
  have hJRow (i : R) : Finset.sum Finset.univ (fun j => abs (J i j)) <= 6 * p :=
    hInverse.2.2 i
  have hPerturb := stochastic_scaling_centering_perturbation_entry T S U q a rho hq ha
    hNonneg hUpper hRho0 hRho hWeak z hZ
  have hEEntry (i j : R) : abs (E i j) <= e := hPerturb.2.2 i j
  have hProduct (i j : R) : abs ((J * E) i j) <= eps := by
    rw [Matrix.mul_apply]
    calc
      _ <= Finset.sum Finset.univ (fun k => abs (J i k * E k j)) :=
        Finset.abs_sum_le_sum_abs _ _
      _ = Finset.sum Finset.univ (fun k => abs (J i k) * abs (E k j)) := by
        simp only [abs_mul]
      _ <= Finset.sum Finset.univ (fun k => abs (J i k) * e) :=
        Finset.sum_le_sum (fun k _ => mul_le_mul_of_nonneg_left (hEEntry k j) (abs_nonneg _))
      _ = Finset.sum Finset.univ (fun k => abs (J i k)) * e := by rw [Finset.sum_mul]
      _ <= (6 * p) * e := mul_le_mul_of_nonneg_right (hJRow i) he
      _ = eps := by dsimp only [e, eps]; ring
  have hFullQ : (Fintype.card (Sum Iota Iota) : Real) * q = 2 := by
    simp only [Fintype.card_sum, Nat.cast_add]
    nlinarith only [hq]
  have hRCard : (R.card : Real) <= (Fintype.card (Sum Iota Iota) : Real) := by
    have h : (R.card : Real) <= ((Finset.univ : Finset (Sum Iota Iota)).card : Real) :=
      Nat.cast_le.mpr (Finset.card_le_card (Finset.subset_univ R))
    simpa only [Finset.card_univ] using h
  have hRQ : (R.card : Real) * q <= 2 := by
    nlinarith only [mul_le_mul_of_nonneg_right hRCard hq0, hFullQ]
  have hMass : (Fintype.card R : Real) * eps <= 528 * r * p ^ 3 * q := by
    calc
      _ = (264 * r * p ^ 3 * q) * ((R.card : Real) * q) := by
        simp only [Fintype.card_coe, eps]
        ring
      _ <= (264 * r * p ^ 3 * q) * 2 :=
        mul_le_mul_of_nonneg_left hRQ (by positivity)
      _ = _ := by ring
  have hSmallMass : (Fintype.card R : Real) * eps <= 1 / 8 := by
    nlinarith only [hMass, hStrong]
  have hLog := hamiltonian_relative_log_determinant_entry_remainder
    HR J E hActualInverse eps hEps hProduct hSmallMass
  have hSquare : ((Fintype.card R : Real) * eps) ^ 2 <= (528 * r * p ^ 3 * q) ^ 2 := by
    have h := mul_le_mul hMass hMass
      (mul_nonneg (Nat.cast_nonneg _) hEps) (by positivity)
    simpa only [pow_two] using h
  refine And.intro hLog.1 ?_
  calc
    _ <= 8 * ((Fintype.card R : Real) * eps) ^ 2 := hLog.2
    _ <= 8 * (528 * r * p ^ 3 * q) ^ 2 :=
      mul_le_mul_of_nonneg_left hSquare (by norm_num)
    _ = _ := by change _ = 2230272 * r ^ 2 * p ^ 6 * q ^ 2; ring

end PrimeFactorOscillations

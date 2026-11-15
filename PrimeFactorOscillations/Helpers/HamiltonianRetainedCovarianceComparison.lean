/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianCovariancePerturbation
import PrimeFactorOscillations.Helpers.HamiltonianScalingDeterminantRemainder

/-! # The actual repaired covariance retains a two-power local error

The inverse perturbation uses both product orders and the full signed
Schur inverse. No first permanent correction is discarded separately.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations

variable {Iota : Type*} [Fintype Iota] [DecidableEq Iota] [Nonempty Iota]

theorem stochastic_retained_covariance_comparison
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
    IsUnit (HR + E) /\
    (forall i : R, Finset.sum Finset.univ
      (fun j => abs (Ring.inverse (HR + E) i j)) <= 12 * (a / (1 - rho))) /\
    (forall i j : R, abs (GammaNew i j - Gamma i.val j.val) <=
      3200 * (U.card : Real) * (a / (1 - rho)) ^ 4 * q ^ 2) /\
    forall i j : R, abs (GammaNew i j) <= 3 * (a / (1 - rho)) * q := by
  let delta := 1 - rho
  let r : Real := U.card
  let p := a / delta
  let D := S.disjSum U
  let R : Finset (Sum Iota Iota) := Compl.compl D
  let rr := fun i : R => (i.val : Sum Iota Iota)
  let Omega := bipartiteLift (centeredKernel T q)
  let H := (1 : Matrix (Sum Iota Iota) (Sum Iota Iota) Real) + Omega
  let R0 := Ring.inverse H
  let Gamma := Omega * R0
  let HR := H.submatrix rr rr
  let J := hamiltonianBoundaryKernel R0 D
  let qNew := q / (1 - r * q)
  let E := hamiltonianScalingPerturbation (hamiltonianRetainedKernel T S U)
    (hamiltonianRetainedCrossMask S U) z q qNew
  let e := 44 * r * p ^ 2 * q ^ 2
  let eps := 264 * r * p ^ 3 * q ^ 2
  let GammaNew := (HR + E - 1) * Ring.inverse (HR + E)
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
    calc
      _ <= (6 * p) * e :=
        hamiltonian_matrix_product_entry_row_bound J E (6 * p) e he hJRow hEEntry i j
      _ = eps := by dsimp only [e, eps]; ring
  have hOmegaTranspose : Omega.transpose = Omega := by
    apply Matrix.ext
    intro i j
    cases i <;> cases j <;> rfl
  have hHTranspose : H.transpose = H := by
    simp only [H, Matrix.transpose_add, Matrix.transpose_one, hOmegaTranspose]
  have hHRTranspose : HR.transpose = HR := by
    apply Matrix.ext
    intro i j
    change H j.val i.val = H i.val j.val
    exact congrArg (fun A : Matrix (Sum Iota Iota) (Sum Iota Iota) Real => A i.val j.val)
      hHTranspose
  have hJLeft : J * HR = 1 := _root_.mul_eq_one_comm.mp hActualInverse
  have hJRightTranspose : HR * J.transpose = 1 := by
    simpa only [Matrix.transpose_mul, hHRTranspose, Matrix.transpose_one] using
      congrArg Matrix.transpose hJLeft
  have hJTranspose : J.transpose = J := by
    calc
      _ = (J * HR) * J.transpose := by rw [hJLeft, one_mul]
      _ = J * (HR * J.transpose) := mul_assoc _ _ _
      _ = J := by rw [hJRightTranspose, mul_one]
  have hTransposeProduct : (E * J).transpose = J * E.transpose := by
    rw [Matrix.transpose_mul, hJTranspose]
  have hETranspose (i j : R) : abs (E.transpose i j) <= e := hEEntry j i
  have hProductReverse (i j : R) : abs ((E * J) i j) <= eps := by
    calc
      _ = abs ((J * E.transpose) j i) :=
        congrArg abs (congrArg (fun A : Matrix R R Real => A j i) hTransposeProduct)
      _ <= (6 * p) * e :=
        hamiltonian_matrix_product_entry_row_bound J E.transpose (6 * p) e he
          hJRow hETranspose j i
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
        mul_le_mul_of_nonneg_left hRQ
          (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hr) (pow_nonneg hp0 3)) hq0)
      _ = _ := by ring
  have hSmallMass : (Fintype.card R : Real) * eps <= 1 / 2 := by
    nlinarith only [hMass, hStrong]
  have hInv := hamiltonian_actual_inverse_perturbation HR J E (6 * p) eps
    (mul_nonneg (by norm_num) hp0) hEps hActualInverse hJRow
      hProduct hProductReverse hSmallMass
  have hUnitH : IsUnit H := by
    have hOmegaNorm : norm Omega <= rho :=
      le_trans (bipartiteLift_l2_norm_le _) hNorm
    have hNeg : norm (-Omega) < 1 := by rw [norm_neg]; exact lt_of_le_of_lt hOmegaNorm hRho
    simpa only [sub_neg_eq_add] using isUnit_one_sub_of_norm_lt_one hNeg
  have hR0 : R0 = 1 - Gamma := hamiltonian_resolvent_one_sub Omega hUnitH
  have hOne : (1 : Matrix (Sum Iota Iota) (Sum Iota Iota) Real).submatrix rr rr = 1 := by
    apply Matrix.ext
    intro i j
    simp only [rr, Matrix.submatrix_apply, Matrix.one_apply, Subtype.ext_iff]
  have hOldSub : R0.submatrix rr rr =
      (1 : Matrix (Sum Iota Iota) (Sum Iota Iota) Real).submatrix rr rr -
        Gamma.submatrix rr rr := by
    rw [hR0]
    rfl
  have hOld : Gamma.submatrix rr rr = 1 - R0.submatrix rr rr := by
    apply eq_sub_iff_add_eq.mpr
    rw [hOldSub, hOne]
    abel
  have hNew : GammaNew = 1 - Ring.inverse (HR + E) := by
    dsimp only [GammaNew]
    rw [sub_mul, Ring.mul_inverse_cancel (HR + E) hInv.1, one_mul]
  have hDifference : GammaNew - Gamma.submatrix rr rr =
      -(Ring.inverse (HR + E) - R0.submatrix rr rr) := by
    rw [hNew, hOld]
    abel
  have hpSq : 1 <= p ^ 2 := by nlinarith only [hp, hp0]
  have hp24 : p ^ 2 <= p ^ 4 := by
    have h := mul_le_mul_of_nonneg_left hpSq (sq_nonneg p)
    nlinarith only [h]
  have hLow : 16 * r * p ^ 2 * q ^ 2 <= 16 * r * p ^ 4 * q ^ 2 := by
    have h := mul_le_mul_of_nonneg_left hp24
      (mul_nonneg (mul_nonneg (by norm_num : (0 : Real) <= 16) hr) (sq_nonneg q))
    nlinarith only [h]
  have hBase : 0 <= r * p ^ 4 * q ^ 2 :=
    mul_nonneg (mul_nonneg hr (pow_nonneg hp0 4)) (sq_nonneg q)
  have hError (i j : R) : abs (GammaNew i j - Gamma i.val j.val) <=
      3200 * r * p ^ 4 * q ^ 2 := by
    have hTri : abs ((Ring.inverse (HR + E) - R0.submatrix rr rr) i j) <=
        abs ((Ring.inverse (HR + E) - J) i j) + abs (J i j - R0 i.val j.val) := by
      have hEq : (Ring.inverse (HR + E) - R0.submatrix rr rr) i j =
          (Ring.inverse (HR + E) - J) i j + (J i j - R0 i.val j.val) := by
        simp only [Matrix.sub_apply, Matrix.submatrix_apply, rr]
        ring
      rw [hEq]
      exact abs_add_le _ _
    have hFirst : abs ((Ring.inverse (HR + E) - J) i j) <=
        3168 * r * p ^ 4 * q ^ 2 := by
      have h := hInv.2.2 i j
      have hEq : 2 * (6 * p) * eps = 3168 * r * p ^ 4 * q ^ 2 := by
        dsimp only [eps]
        ring
      rw [hEq] at h
      exact h
    have hSecond : abs (J i j - R0 i.val j.val) <= 16 * r * p ^ 2 * q ^ 2 :=
      hInverse.2.1 i j
    change abs ((GammaNew - Gamma.submatrix rr rr) i j) <= _
    rw [hDifference, Matrix.neg_apply, abs_neg]
    nlinarith only [hTri, hFirst, hSecond, hLow, hBase]
  have hGamma (i j : Sum Iota Iota) : abs (Gamma i j) <= 2 * p * q := by
    have h := stochastic_block_covariance_entry_bound T q a rho hq ha
      hRow hCol hNonneg hUpper hRho hNorm i j
    change delta * norm (Gamma i j) <= (2 - rho) * (a * q) at h
    rw [Real.norm_eq_abs] at h
    have hSigned := mul_nonneg hRho0 (mul_nonneg ha0 hq0)
    have hClear : delta * (2 * p * q) = 2 * a * q := by rw [<- hpClear]; ring
    nlinarith only [h, hSigned, hClear, hDelta]
  have hTiny : 3200 * r * p ^ 4 * q ^ 2 <= p * q := by
    calc
      _ = (3200 * p * q) * (r * p ^ 3 * q) := by ring
      _ <= (3200 * p * q) * (1 / 10000) :=
        mul_le_mul_of_nonneg_left hStrong
          (mul_nonneg (mul_nonneg (by norm_num : (0 : Real) <= 3200) hp0) hq0)
      _ <= _ := by nlinarith only [mul_nonneg hp0 hq0]
  change IsUnit (HR + E) /\
    (forall i : R, Finset.sum Finset.univ
      (fun j => abs (Ring.inverse (HR + E) i j)) <= 12 * p) /\
    (forall i j : R, abs (GammaNew i j - Gamma i.val j.val) <= 3200 * r * p ^ 4 * q ^ 2) /\
    forall i j : R, abs (GammaNew i j) <= 3 * p * q
  refine And.intro hInv.1 (And.intro ?_ (And.intro hError ?_))
  case refine_1 =>
    intro i
    have h := hInv.2.1 i
    nlinarith only [h]
  case refine_2 =>
    intro i j
    have hTri := abs_add_le (GammaNew i j - Gamma i.val j.val) (Gamma i.val j.val)
    rw [sub_add_cancel] at hTri
    nlinarith only [hTri, hError i j, hGamma i.val j.val, hTiny]

end PrimeFactorOscillations

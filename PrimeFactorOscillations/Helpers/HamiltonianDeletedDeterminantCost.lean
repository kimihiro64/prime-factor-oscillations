/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianBlockCovariance
import PrimeFactorOscillations.Helpers.HamiltonianLogDeterminantEntryBudget
import PrimeFactorOscillations.Helpers.HamiltonianPrincipalInverseDeterminant
import PrimeFactorOscillations.Helpers.HamiltonianRepairKernel

/-! # The actual deleted-covariance determinant cost

The independent row and column support is kept throughout. The trace is
signed; the small determinant's complete higher coefficients have an
explicit two-power remainder, including the empty-support case.
-/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations

variable {Iota : Type*} [Fintype Iota] [DecidableEq Iota] [Nonempty Iota]

theorem stochastic_deleted_covariance_log_determinant
    (T : Matrix Iota Iota Real) (S U : Finset Iota) (hCard : S.card = U.card)
    (q a rho : Real) (hq : (Fintype.card Iota : Real) * q = 1) (ha : 1 <= a)
    (hRow : forall i, Finset.sum Finset.univ (fun j => T i j) = 1)
    (hCol : forall j, Finset.sum Finset.univ (fun i => T i j) = 1)
    (hNonneg : forall i j, 0 <= T i j) (hUpper : forall i j, T i j <= a * q)
    (hNorm : norm (centeredKernel T q) <= rho) (hRho : rho < 1)
    (hSmall : (U.card : Real) * a ^ 2 * q / (1 - rho) ^ 2 <= 1 / 1000) :
    let D := S.disjSum U
    let Omega := bipartiteLift (centeredKernel T q)
    let Gamma := Omega * Ring.inverse (1 + Omega)
    let G := Gamma.submatrix (fun i : D => i.val) (fun i : D => i.val)
    0 < Matrix.det (1 - G) /\
    abs (Real.log (Matrix.det (1 - G)) + Matrix.trace G) <=
      128 * ((U.card : Real) * a * q / (1 - rho)) ^ 2 := by
  let delta := 1 - rho
  let r : Real := U.card
  let p := a / delta
  let t := r * p * q
  let D := S.disjSum U
  let Omega := bipartiteLift (centeredKernel T q)
  let Gamma := Omega * Ring.inverse (1 + Omega)
  let G := Gamma.submatrix (fun i : D => i.val) (fun i : D => i.val)
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
  have ht : 0 <= t := by dsimp only [t]; positivity
  have hPt : p * t <= 1 / 1000 := by
    have hEq : p * t = r * a ^ 2 * q / delta ^ 2 := by
      dsimp only [p, t]
      field_simp
    rw [hEq]
    exact hSmall
  have htSmall : t <= 1 / 1000 := by
    have hMul := mul_le_mul_of_nonneg_right hp ht
    nlinarith only [hMul, hPt]
  have hCardD : (D.card : Real) = 2 * r := by
    simp only [D, Finset.card_disjSum, hCard, Nat.cast_add, r]
    ring
  have hEntry (i j : D) : abs (G i j) <= 2 * p * q := by
    have h := stochastic_block_covariance_entry_bound T q a rho hq ha
      hRow hCol hNonneg hUpper hRho hNorm i.val j.val
    change delta * norm (G i j) <= (2 - rho) * (a * q) at h
    rw [Real.norm_eq_abs] at h
    have hAq : 0 <= a * q := mul_nonneg ha0 hq0
    have hSigned := mul_nonneg hRho0 hAq
    have hClear : delta * (2 * p * q) = 2 * a * q := by rw [<- hpClear]; ring
    nlinarith only [h, hSigned, hClear, hDelta]
  have hBudget : (Fintype.card D : Real) * (2 * p * q) <= 1 / 8 := by
    simp only [Fintype.card_coe]
    rw [hCardD]
    change 2 * r * (2 * p * q) <= 1 / 8
    dsimp only [t] at htSmall
    nlinarith only [htSmall]
  have h := hamiltonian_log_determinant_trace_entry_remainder (-G)
    (2 * p * q) (by positivity)
    (fun i j => by simpa only [Matrix.neg_apply, abs_neg] using hEntry i j) hBudget
  have hError : 8 * ((Fintype.card D : Real) * (2 * p * q)) ^ 2 =
      128 * (r * a * q / (1 - rho)) ^ 2 := by
    simp only [Fintype.card_coe]
    rw [hCardD]
    dsimp only [p, delta]
    ring
  rw [hError] at h
  simpa only [sub_eq_add_neg, Matrix.trace_neg, sub_neg_eq_add, neg_neg] using h


theorem stochastic_deleted_principal_log_determinant
    (T : Matrix Iota Iota Real) (S U : Finset Iota) (hCard : S.card = U.card)
    (q a rho : Real) (hq : (Fintype.card Iota : Real) * q = 1) (ha : 1 <= a)
    (hRow : forall i, Finset.sum Finset.univ (fun j => T i j) = 1)
    (hCol : forall j, Finset.sum Finset.univ (fun i => T i j) = 1)
    (hNonneg : forall i j, 0 <= T i j) (hUpper : forall i j, T i j <= a * q)
    (hNorm : norm (centeredKernel T q) <= rho) (hRho : rho < 1)
    (hSmall : (U.card : Real) * a ^ 2 * q / (1 - rho) ^ 2 <= 1 / 1000) :
    let D := S.disjSum U
    let R : Finset (Sum Iota Iota) := Compl.compl D
    let Omega := bipartiteLift (centeredKernel T q)
    let H := (1 : Matrix (Sum Iota Iota) (Sum Iota Iota) Real) + Omega
    let Gamma := Omega * Ring.inverse H
    let G := Gamma.submatrix (fun i : D => i.val) (fun i : D => i.val)
    let HR := H.submatrix (fun i : R => i.val) (fun i : R => i.val)
    0 < Matrix.det HR / Matrix.det H /\
    abs (Real.log (Matrix.det HR / Matrix.det H) + Matrix.trace G) <=
      128 * ((U.card : Real) * a * q / (1 - rho)) ^ 2 := by
  let D := S.disjSum U
  let R : Finset (Sum Iota Iota) := Compl.compl D
  let Omega := bipartiteLift (centeredKernel T q)
  let H := (1 : Matrix (Sum Iota Iota) (Sum Iota Iota) Real) + Omega
  let K := Ring.inverse H
  let Gamma := Omega * K
  let G := Gamma.submatrix (fun i : D => i.val) (fun i : D => i.val)
  let rr := fun i : R => (i.val : Sum Iota Iota)
  let rd := fun i : D => (i.val : Sum Iota Iota)
  have hDeleted := stochastic_deleted_covariance_log_determinant T S U hCard q a rho hq ha
    hRow hCol hNonneg hUpper hNorm hRho hSmall
  change 0 < Matrix.det (1 - G) /\
    abs (Real.log (Matrix.det (1 - G)) + Matrix.trace G) <=
      128 * ((U.card : Real) * a * q / (1 - rho)) ^ 2 at hDeleted
  have hUnit : IsUnit H := by
    have hOmegaNorm : norm Omega <= rho :=
      le_trans (bipartiteLift_l2_norm_le _) hNorm
    have hNeg : norm (-Omega) < 1 := by
      rw [norm_neg]
      exact lt_of_le_of_lt hOmegaNorm hRho
    simpa only [sub_neg_eq_add] using isUnit_one_sub_of_norm_lt_one hNeg
  have hInverse : H * K = 1 := Ring.mul_inverse_cancel _ hUnit
  have hKernel : K = 1 - Gamma := by
    have h := hamiltonianRepairKernel_covariance T q rho hNorm hRho
    change K - hamiltonianRepairProjection q =
      (1 - Gamma) - hamiltonianRepairProjection q at h
    have hAdd := congrArg (fun A => A + hamiltonianRepairProjection q) h
    simpa only [sub_add_cancel] using hAdd
  have hDeletedKernel : K.submatrix rd rd = 1 - G := by
    rw [hKernel]
    apply Matrix.ext
    intro i j
    change (1 : Matrix (Sum Iota Iota) (Sum Iota Iota) Real) i.val j.val -
      Gamma i.val j.val = (1 : Matrix D D Real) i j - Gamma i.val j.val
    simp only [Matrix.one_apply, Subtype.ext_iff]
  have hDeletedUnit : IsUnit (K.submatrix rd rd) := by
    apply (Matrix.isUnit_iff_isUnit_det (K.submatrix rd rd)).mpr
    apply isUnit_iff_ne_zero.mpr
    rw [hDeletedKernel]
    exact ne_of_gt hDeleted.1
  have hJacobi := hamiltonian_principal_inverse_complement_determinant
    H K D hInverse hDeletedUnit
  change 0 < Matrix.det (H.submatrix rr rr) / Matrix.det H /\
    abs (Real.log (Matrix.det (H.submatrix rr rr) / Matrix.det H) + Matrix.trace G) <=
      128 * ((U.card : Real) * a * q / (1 - rho)) ^ 2
  rw [hJacobi, hDeletedKernel]
  exact hDeleted

end PrimeFactorOscillations

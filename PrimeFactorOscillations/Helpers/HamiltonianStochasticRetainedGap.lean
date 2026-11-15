/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianRetainedOperatorBounds
import PrimeFactorOscillations.Helpers.HamiltonianScalingDeterminantRemainder

/-! # The actual retained scaling and rank-centering perturbation preserves a gap

The complete perturbation, including the quadratic and reference shift,
is retained. Coordinate compression is a contraction. Only the explicit
perturbation receives an entrywise norm estimate.
-/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations

variable {Iota : Type*} [Fintype Iota] [DecidableEq Iota] [Nonempty Iota]

theorem stochastic_retained_scaling_gap
    (T : Matrix Iota Iota Real) (S U : Finset Iota)
    (q a rho : Real) (hq : (Fintype.card Iota : Real) * q = 1) (ha : 1 <= a)
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
    norm E <= (1 - rho) / 100 /\
    norm (HR + E - 1) <= 1 - (1 - rho) / 2 := by
  let delta := 1 - rho
  let r : Real := U.card
  let p := a / delta
  let D := S.disjSum U
  let R : Finset (Sum Iota Iota) := Compl.compl D
  let rr := fun i : R => (i.val : Sum Iota Iota)
  let Omega := bipartiteLift (centeredKernel T q)
  let OmegaR := Omega.submatrix rr rr
  let H := (1 : Matrix (Sum Iota Iota) (Sum Iota Iota) Real) + Omega
  let HR := H.submatrix rr rr
  let qNew := q / (1 - r * q)
  let E := hamiltonianScalingPerturbation (hamiltonianRetainedKernel T S U)
    (hamiltonianRetainedCrossMask S U) z q qNew
  let e := 44 * r * p ^ 2 * q ^ 2
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
  have he : 0 <= e :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hr) (sq_nonneg p)) (sq_nonneg q)
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
  have hPerturb := stochastic_scaling_centering_perturbation_entry T S U q a rho hq ha
    hNonneg hUpper hRho0 hRho hWeak z hZ
  have hEntry (i j : R) : abs (E i j) <= e := hPerturb.2.2 i j
  have hFullQ : (Fintype.card (Sum Iota Iota) : Real) * q = 2 := by
    simp only [Fintype.card_sum, Nat.cast_add]
    nlinarith only [hq]
  have hRCard : (R.card : Real) <= (Fintype.card (Sum Iota Iota) : Real) := by
    have h : (R.card : Real) <= ((Finset.univ : Finset (Sum Iota Iota)).card : Real) :=
      Nat.cast_le.mpr (Finset.card_le_card (Finset.subset_univ R))
    simpa only [Finset.card_univ] using h
  have hRQ : (R.card : Real) * q <= 2 := by
    nlinarith only [mul_le_mul_of_nonneg_right hRCard hq0, hFullQ]
  have hNormE : norm E <= 88 * r * p ^ 2 * q := by
    calc
      _ <= (R.card : Real) * e := by
        simpa only [Fintype.card_coe] using hamiltonian_l2_entry_budget E e he hEntry
      _ = (44 * r * p ^ 2 * q) * ((R.card : Real) * q) := by dsimp only [e]; ring
      _ <= (44 * r * p ^ 2 * q) * 2 :=
        mul_le_mul_of_nonneg_left hRQ
          (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hr) (sq_nonneg p)) hq0)
      _ = _ := by ring
  have hA1 : 1 <= delta * p := by rw [hpClear]; exact ha
  have hGrow := mul_le_mul_of_nonneg_right hA1
    (mul_nonneg (mul_nonneg hr (sq_nonneg p)) hq0)
  have hScaled := mul_le_mul_of_nonneg_left hStrong
    (mul_nonneg (by norm_num : (0 : Real) <= 88) (le_of_lt hDelta))
  have hSmallE : norm E <= delta / 100 := by
    nlinarith only [hNormE, hGrow, hScaled, hDelta]
  have hOmegaNorm : norm Omega <= rho := le_trans (bipartiteLift_l2_norm_le _) hNorm
  have hRestriction : norm OmegaR <= rho := le_trans
    (hamiltonian_l2_injective_submatrix_le Omega rr Subtype.val_injective) hOmegaNorm
  have hOne : (1 : Matrix (Sum Iota Iota) (Sum Iota Iota) Real).submatrix rr rr = 1 := by
    apply Matrix.ext
    intro i j
    simp only [rr, Matrix.submatrix_apply, Matrix.one_apply, Subtype.ext_iff]
  have hHR : HR = (1 : Matrix (Sum Iota Iota) (Sum Iota Iota) Real).submatrix rr rr + OmegaR := by
    rfl
  have hDifference : HR + E - 1 = OmegaR + E := by
    rw [hHR, hOne]
    abel
  refine And.intro hSmallE ?_
  rw [hDifference]
  calc
    _ <= norm OmegaR + norm E := norm_add_le _ _
    _ <= rho + delta / 100 := add_le_add hRestriction hSmallE
    _ <= 1 - (1 - rho) / 2 := by dsimp only [delta]; linarith only [hRho]

end PrimeFactorOscillations

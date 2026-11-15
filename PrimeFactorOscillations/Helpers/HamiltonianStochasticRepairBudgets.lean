/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianBoundaryBudgets
import PrimeFactorOscillations.Helpers.HamiltonianDeletedSupportDefect

/-! # Actual stochastic budgets for the nonlinear deleted-support repair

All four budgets are derived from the actual stochastic matrix and its
spectral gap. The leading K ell is retained; only the explicit boundary
and removed-source errors receive absolute estimates.
-/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations

variable {Iota : Type*} [Fintype Iota] [DecidableEq Iota] [Nonempty Iota]

theorem stochastic_boundary_repair_budgets
    (T : Matrix Iota Iota Real) (S U : Finset Iota) (hCard : S.card = U.card)
    (q a rho : Real) (hq : (Fintype.card Iota : Real) * q = 1) (ha : 1 <= a)
    (hRow : forall i, Finset.sum Finset.univ (fun j => T i j) = 1)
    (hCol : forall j, Finset.sum Finset.univ (fun i => T i j) = 1)
    (hNonneg : forall i j, 0 <= T i j) (hUpper : forall i j, T i j <= a * q)
    (hNorm : norm (centeredKernel T q) <= rho) (hRho : rho < 1)
    (hSmall : (U.card : Real) * a ^ 2 * q / (1 - rho) ^ 2 <= 1 / 1000) :
    let p := a / (1 - rho)
    let t := (U.card : Real) * p * q
    let D := S.disjSum U
    let R : Finset (Sum Iota Iota) := Compl.compl D
    let K := hamiltonianRepairKernel T q
    let G := hamiltonianBoundaryKernel K D
    let ell := hamiltonianDeletedSupportDefect T S U
    (forall i : R, Finset.sum Finset.univ (fun j => abs (G i j)) <= 10 * p) /\
      norm (fun i : R => ell i.val) <= t /\
      norm (G.mulVec (fun i : R => ell i.val)) <= 10 * t /\
      norm (G.mulVec (fun i : R => ell i.val) -
        (fun i : R => K.mulVec ell i.val)) <= 136 * t ^ 2 := by
  let delta := 1 - rho
  let r : Real := U.card
  let p := a / delta
  let t := r * p * q
  let u := p * t
  let c := 4 * p * q
  let E := 64 * u * q
  let D := S.disjSum U
  let R : Finset (Sum Iota Iota) := Compl.compl D
  let K := hamiltonianRepairKernel T q
  let G := hamiltonianBoundaryKernel K D
  let ell := hamiltonianDeletedSupportDefect T S U
  change (forall i : R, Finset.sum Finset.univ (fun j => abs (G i j)) <= 10 * p) /\
    norm (fun i : R => ell i.val) <= t /\
    norm (G.mulVec (fun i : R => ell i.val)) <= 10 * t /\
    norm (G.mulVec (fun i : R => ell i.val) -
      (fun i : R => K.mulVec ell i.val)) <= 136 * t ^ 2
  have hDelta : 0 < delta := sub_pos.mpr hRho
  have hDen : Not (delta = 0) := ne_of_gt hDelta
  have hRho0 : 0 <= rho := le_trans (norm_nonneg _) hNorm
  have hDelta1 : delta <= 1 := by dsimp only [delta]; linarith only [hRho0]
  have hA0 : 0 <= a := le_trans (by norm_num) ha
  have hN : 0 < (Fintype.card Iota : Real) := Nat.cast_pos.mpr Fintype.card_pos
  have hq0 : 0 <= q := by nlinarith only [hq, hN]
  have hr : 0 <= r := Nat.cast_nonneg _
  have hp0 : 0 <= p := div_nonneg hA0 (le_of_lt hDelta)
  have hpDelta : delta * p = a := by dsimp only [p]; field_simp
  have hp : 1 <= p := by nlinarith only [hpDelta, hDelta1, hp0, ha]
  have ht : 0 <= t := by dsimp only [t]; positivity
  have hu0 : 0 <= u := mul_nonneg hp0 ht
  have hc : 0 <= c := by dsimp only [c]; positivity
  have hE : 0 <= E := by dsimp only [E]; positivity
  have hUeq : u = r * a ^ 2 * q / delta ^ 2 := by
    dsimp only [u, t, p]
    field_simp
  have hu : u <= 1 / 1000 := by rw [hUeq]; exact hSmall
  have htu : t <= u := by dsimp only [u]; nlinarith only [hp, ht]
  have htSmall : t <= 1 / 1000 := le_trans htu hu
  have hAr : r * a * q = delta * t := by
    calc
      _ = r * (delta * p) * q := by rw [hpDelta]
      _ = _ := by dsimp only [t]; ring
  have hD : (D.card : Real) = 2 * r := by
    simp only [D, Finset.card_disjSum, hCard, Nat.cast_add, r]
    ring
  have hSmallD : (D.card : Real) * (4 * a * q) <= (1 - rho) / 2 := by
    rw [hD]
    have hScaled := mul_le_mul_of_nonneg_left htSmall (le_of_lt hDelta)
    change 2 * r * (4 * a * q) <= delta / 2
    nlinarith only [hAr, hScaled, hDelta]
  have hFrac : 4 * a * q / (1 - rho) = c := by
    change 4 * a * q / delta = 4 * (a / delta) * q
    ring
  have hEeq : 2 * (D.card : Real) * (4 * a * q / (1 - rho)) ^ 2 = E := by
    rw [hFrac, hD]
    dsimp only [E, c, u, t]
    ring
  have hError (i j : R) : abs (G i j - K i.val j.val) <= E :=
    le_trans (stochastic_boundary_kernel_entry_error T D q a rho hq ha
      hRow hCol hNonneg hUpper hNorm hRho hSmallD i j) (le_of_eq hEeq)
  have hOff (i j : Sum Iota Iota) (hne : Not (i = j)) : abs (K i j) <= c := by
    have h := stochastic_repair_kernel_entry T q a rho hq ha
      hRow hCol hNonneg hUpper hNorm hRho i j
    simp only [Matrix.sub_apply, Matrix.one_apply, if_neg hne, sub_zero] at h
    have hClear : delta * c = 4 * a * q := by
      calc
        _ = 4 * (delta * p) * q := by dsimp only [c]; ring
        _ = _ := by rw [hpDelta]
    change delta * abs (K i j) <= 4 * a * q at h
    nlinarith only [h, hClear, hDelta]
  have hCross (i : R) (d : D) : abs (K i.val d.val) <= c := by
    apply hOff
    intro heq
    have hd : Membership.mem D i.val := by rw [heq]; exact d.property
    exact (Finset.mem_compl.mp i.property) hd
  have hKRow (i : Sum Iota Iota) :
      Finset.sum Finset.univ (fun j => abs (K i j)) <= 1 + 8 * p := by
    have h := stochastic_repair_kernel_row T q a rho hq ha
      hRow hCol hNonneg hUpper hNorm hRho i
    change delta * Finset.sum Finset.univ (fun j => abs (K i j)) <= delta + 8 * a at h
    have hClear : delta * (1 + 8 * p) = delta + 8 * a := by
      nlinarith only [hpDelta]
    nlinarith only [h, hClear, hDelta]
  have hCardQ : (Fintype.card (Sum Iota Iota) : Real) * q = 2 := by
    simp only [Fintype.card_sum, Nat.cast_add]
    nlinarith only [hq]
  have hRCard : (R.card : Real) <= (Fintype.card (Sum Iota Iota) : Real) := by
    have h : (R.card : Real) <= ((Finset.univ : Finset (Sum Iota Iota)).card : Real) :=
      Nat.cast_le.mpr (Finset.card_le_card (Finset.subset_univ R))
    simpa only [Finset.card_univ] using h
  have hRQ : (R.card : Real) * q <= 2 := by
    nlinarith only [mul_le_mul_of_nonneg_right hRCard hq0, hCardQ]
  have hRowError : (R.card : Real) * E <= 128 * u := by
    calc
      _ = (64 * u) * ((R.card : Real) * q) := by dsimp only [E]; ring
      _ <= (64 * u) * 2 := mul_le_mul_of_nonneg_left hRQ (by positivity)
      _ = _ := by ring
  have hGRow (i : R) : Finset.sum Finset.univ (fun j => abs (G i j)) <= 10 * p := by
    have h := hamiltonianBoundaryKernel_row_bound K D E (1 + 8 * p) hKRow hError i
    change Finset.sum Finset.univ (fun j => abs (G i j)) <= 1 + 8 * p + (R.card : Real) * E at h
    linarith only [h, hRowError, hu, hp]
  have hEll (i : Sum Iota Iota) : abs (ell i) <= t := by
    have hn := hamiltonianDeletedSupportDefect_nonnegative T S U hNonneg i
    have h := hamiltonianDeletedSupportDefect_entry T S U hCard q a hUpper i
    change ell i <= r * a * q at h
    rw [abs_of_nonneg hn]
    nlinarith only [h, hAr, mul_le_mul_of_nonneg_right hDelta1 ht]
  have hMass : Finset.sum Finset.univ (fun i => abs (ell i)) <= 2 * r := by
    have h := hamiltonianDeletedSupportDefect_abs_mass T S U hRow hCol hNonneg
    simp only [hCard] at h
    change Finset.sum Finset.univ (fun i => abs (ell i)) = r + r at h
    linarith only [h]
  have hDeleted : Finset.sum Finset.univ (fun d : D => abs (ell d.val)) <= 2 * r * t := by
    calc
      _ <= Finset.sum Finset.univ (fun _ : D => t) :=
        Finset.sum_le_sum (fun d _ => hEll d.val)
      _ = (D.card : Real) * t := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul]
      _ = _ := by rw [hD]
  have hSourceError (i : R) :
      abs (G.mulVec (fun j : R => ell j.val) i - K.mulVec ell i.val) <= 136 * t ^ 2 := by
    have h := hamiltonianBoundaryKernel_source_error K D ell E c (2 * r) (2 * r * t)
      hE hc hError hCross hMass hDeleted i
    have hPoly : E * (2 * r) + c * (2 * r * t) = 136 * t ^ 2 := by
      dsimp only [E, c, u, t]
      ring
    exact le_trans h (le_of_eq hPoly)
  have hKSource (i : R) : abs (K.mulVec ell i.val) <= 9 * t := by
    have h := stochastic_deleted_support_linear_repair T S U hCard q a rho hq ha
      hRow hCol hNonneg hUpper hNorm hRho i.val
    change delta * abs (K.mulVec ell i.val) <= 9 * r * a * q at h
    nlinarith only [h, hAr, hDelta]
  have hGSource (i : R) : abs (G.mulVec (fun j : R => ell j.val) i) <= 10 * t := by
    have h := abs_add_le
      (G.mulVec (fun j : R => ell j.val) i - K.mulVec ell i.val) (K.mulVec ell i.val)
    rw [sub_add_cancel] at h
    have hSquare := mul_le_mul_of_nonneg_right htSmall ht
    nlinarith only [h, hSourceError i, hKSource i, hSquare, ht]
  refine And.intro hGRow (And.intro ?_ (And.intro ?_ ?_))
  case refine_1 =>
    apply (pi_norm_le_iff_of_nonneg ht).mpr
    intro i
    rw [Real.norm_eq_abs]
    exact hEll i.val
  case refine_2 =>
    apply (pi_norm_le_iff_of_nonneg (mul_nonneg (by norm_num) ht)).mpr
    intro i
    rw [Real.norm_eq_abs]
    exact hGSource i
  case refine_3 =>
    apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
    intro i
    rw [Real.norm_eq_abs]
    exact hSourceError i

end PrimeFactorOscillations

/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianScalingCostRemainder
import PrimeFactorOscillations.Helpers.HamiltonianStochasticRepair

/-! # The actual signed stochastic scaling cost with a two-power error

The complete overlap and ell-transpose-K-ell main terms remain signed.
The explicit remainder is derived from the proved positive repair and
the full finite quadratic identity, including all removed coordinates.
-/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations

variable {Iota : Type*} [Fintype Iota] [DecidableEq Iota]

def hamiltonianRetainedKernel (T : Matrix Iota Iota Real) (S U : Finset Iota) :
    Matrix (Compl.compl (S.disjSum U) : Finset (Sum Iota Iota))
      (Compl.compl (S.disjSum U) : Finset (Sum Iota Iota)) Real :=
  (bipartiteLift T).submatrix
    (fun i : (Compl.compl (S.disjSum U) : Finset (Sum Iota Iota)) => i.val)
    (fun i : (Compl.compl (S.disjSum U) : Finset (Sum Iota Iota)) => i.val)

variable [Nonempty Iota]

theorem stochastic_deleted_support_scaling_cost
    (T : Matrix Iota Iota Real) (S U : Finset Iota) (hCard : S.card = U.card)
    (q a rho : Real) (hq : (Fintype.card Iota : Real) * q = 1) (ha : 1 <= a)
    (hRow : forall i, Finset.sum Finset.univ (fun j => T i j) = 1)
    (hCol : forall j, Finset.sum Finset.univ (fun i => T i j) = 1)
    (hNonneg : forall i j, 0 <= T i j) (hUpper : forall i j, T i j <= a * q)
    (hNorm : norm (centeredKernel T q) <= rho) (hRho : rho < 1)
    (hSmall : (U.card : Real) * a ^ 2 * q / (1 - rho) ^ 2 <= 1 / 1000)
    (z : forall _i : (Compl.compl (S.disjSum U) : Finset (Sum Iota Iota)), Real)
    (hZ : norm z <= 20 * (U.card : Real) * (a / (1 - rho)) * q)
    (hClose : norm (z -
      (fun i : (Compl.compl (S.disjSum U) : Finset (Sum Iota Iota)) =>
        (hamiltonianRepairKernel T q).mulVec (hamiltonianDeletedSupportDefect T S U) i.val)) <=
      5000 * (a / (1 - rho)) * ((U.card : Real) * (a / (1 - rho)) * q) ^ 2)
    (hScaling : forall i : (Compl.compl (S.disjSum U) : Finset (Sum Iota Iota)),
      (1 + z i) * (hamiltonianRetainedKernel T S U).mulVec (1 + z) i = 1) :
    abs (Finset.sum Finset.univ (fun i => Real.log (1 + z i)) -
      ((U.card : Real) - hamiltonianDeletedOverlap T S U) -
        Finset.sum Finset.univ (fun i : Sum Iota Iota =>
          hamiltonianDeletedSupportDefect T S U i *
            (hamiltonianRepairKernel T q).mulVec
              (hamiltonianDeletedSupportDefect T S U) i) / 2) <=
      100000 * (U.card : Real) * (a / (1 - rho)) *
        ((U.card : Real) * (a / (1 - rho)) * q) ^ 2 := by
  let delta := 1 - rho
  let r : Real := U.card
  let p := a / delta
  let t := r * p * q
  let D := S.disjSum U
  let R : Finset (Sum Iota Iota) := Compl.compl D
  let M : Real := R.card
  let K := hamiltonianRepairKernel T q
  let ell := hamiltonianDeletedSupportDefect T S U
  let ellR := fun i : R => ell i.val
  let k := K.mulVec ell
  let PR := hamiltonianRetainedKernel T S U
  let logCost := Finset.sum Finset.univ (fun i : R => Real.log (1 + z i))
  let retainedCost := Finset.sum Finset.univ (fun i : R => ell i.val * z i)
  let fullCost := Finset.sum Finset.univ (fun i : Sum Iota Iota => ell i * k i)
  change abs (logCost - (r - hamiltonianDeletedOverlap T S U) - fullCost / 2) <=
    100000 * r * p * t ^ 2
  change norm z <= 20 * r * p * q at hZ
  change norm (z - (fun i : R => k i.val)) <= 5000 * p * t ^ 2 at hClose
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
      field_simp <;> ring
    rw [hEq]
    exact hSmall
  have htSmall : t <= 1 / 1000 := by
    have h := mul_le_mul_of_nonneg_right hp ht
    change 1 * t <= p * t at h
    nlinarith only [h, hPt]
  have hZNorm : norm z <= 20 * t := by dsimp only [t]; nlinarith only [hZ]
  have hRadius : 0 <= 20 * t := by positivity
  have hHalf : 20 * t <= 1 / 2 := by linarith only [htSmall]
  have hZPoint (i : R) : abs (z i) <= 20 * t := by
    have h := (pi_norm_le_iff_of_nonneg hRadius).mp hZNorm i
    simpa only [Real.norm_eq_abs] using h
  have hAr : r * a * q = delta * t := by
    calc
      _ = r * (delta * p) * q := by rw [hpClear]
      _ = _ := by dsimp only [t]; ring
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
  have hRetMass : Finset.sum Finset.univ (fun i : R => abs (ellR i)) <= 2 * r :=
    le_trans (hamiltonian_retained_sum_le (fun i => abs (ell i)) D (fun _ => abs_nonneg _)) hMass
  have hDCard : (D.card : Real) = 2 * r := by
    simp only [D, Finset.card_disjSum, hCard, Nat.cast_add, r]
    ring
  have hDeleted : Finset.sum Finset.univ (fun i : D => abs (ell i.val)) <= 2 * r * t := by
    calc
      _ <= Finset.sum Finset.univ (fun _ : D => t) :=
        Finset.sum_le_sum (fun d _ => hEll d.val)
      _ = (D.card : Real) * t := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul]
      _ = _ := by rw [hDCard]
  have hK (i : Sum Iota Iota) : abs (k i) <= 9 * t := by
    have h := stochastic_deleted_support_linear_repair T S U hCard q a rho hq ha
      hRow hCol hNonneg hUpper hNorm hRho i
    change delta * abs (k i) <= 9 * r * a * q at h
    nlinarith only [h, hAr, hDelta]
  have hClosePoint (i : R) : abs (z i - k i.val) <= 5000 * p * t ^ 2 := by
    have h := (pi_norm_le_iff_of_nonneg (by positivity)).mp hClose i
    simpa only [Real.norm_eq_abs, Pi.sub_apply] using h
  have hLinear := hamiltonian_retained_linear_cost_error D ell k z
    (5000 * p * t ^ 2) (9 * t) (2 * r) (2 * r * t) (by positivity) (by positivity)
    hClosePoint (fun d => hK d.val) hMass hDeleted
  change abs (retainedCost - fullCost) <=
    (2 * r) * (5000 * p * t ^ 2) + (2 * r * t) * (9 * t) at hLinear
  have hFullSym (i j : Sum Iota Iota) : bipartiteLift T i j = bipartiteLift T j i := by
    cases i <;> cases j <;> rfl
  have hSym (i j : R) : PR i j = PR j i := hFullSym i.val j.val
  have hDegree (i : R) : PR.mulVec 1 i = 1 - ellR i :=
    hamiltonian_retained_row_defect T S U hRow hCol i
  have hNonnegFull (i j : Sum Iota Iota) : 0 <= bipartiteLift T i j := by
    cases i <;> cases j <;>
      simp [bipartiteLift, Matrix.fromBlocks, Matrix.transpose_apply, hNonneg]
  have hP (i : R) : Finset.sum Finset.univ (fun j => abs (PR i j)) <= 1 := by
    calc
      _ = Finset.sum Finset.univ (fun j => PR i j) :=
        Finset.sum_congr rfl (fun j _ => abs_of_nonneg (hNonnegFull i.val j.val))
      _ = PR.mulVec 1 i := by simp only [Matrix.mulVec, dotProduct, Pi.one_apply, mul_one]
      _ = 1 - ellR i := hDegree i
      _ <= 1 := by
        have h := hamiltonianDeletedSupportDefect_nonnegative T S U hNonneg i.val
        change 0 <= ellR i at h
        linarith only [h]
  have hCost := hamiltonian_scaling_cost_remainder PR hSym ellR z hDegree hScaling
    (20 * t) (2 * r) hRadius hHalf hZPoint hP hRetMass
  have hHalfMass : Finset.sum Finset.univ ellR / 2 =
      r - hamiltonianDeletedOverlap T S U := by
    have h := hamiltonianDeletedSupportDefect_retained_mass T S U hCard hRow hCol
    change Finset.sum Finset.univ ellR = 2 * (r - hamiltonianDeletedOverlap T S U) at h
    linarith only [h]
  rw [hHalfMass] at hCost
  simp only [Fintype.card_coe] at hCost
  change abs (logCost - (r - hamiltonianDeletedOverlap T S U) - retainedCost / 2) <=
    (2 * r) * (20 * t) ^ 2 / 2 + 5 * M * (20 * t) ^ 3 / 2 at hCost
  have hCardQ : (Fintype.card (Sum Iota Iota) : Real) * q = 2 := by
    simp only [Fintype.card_sum, Nat.cast_add]
    nlinarith only [hq]
  have hRCard : (R.card : Real) <= (Fintype.card (Sum Iota Iota) : Real) := by
    have h : (R.card : Real) <= ((Finset.univ : Finset (Sum Iota Iota)).card : Real) :=
      Nat.cast_le.mpr (Finset.card_le_card (Finset.subset_univ R))
    simpa only [Finset.card_univ] using h
  have hMQ : M * q <= 2 := by
    nlinarith only [mul_le_mul_of_nonneg_right hRCard hq0, hCardQ]
  have hMT : M * t <= 2 * r * p := by
    calc
      _ = (M * q) * (r * p) := by dsimp only [t]; ring
      _ <= 2 * (r * p) := mul_le_mul_of_nonneg_right hMQ (mul_nonneg hr hp0)
      _ = _ := by ring
  have hMTCube := mul_le_mul_of_nonneg_right hMT (sq_nonneg t)
  have hLower := mul_le_mul_of_nonneg_right hp (mul_nonneg hr (sq_nonneg t))
  have hPositiveTerm : 0 <= r * p * t ^ 2 := mul_nonneg (mul_nonneg hr hp0) (sq_nonneg t)
  have hDiv : abs ((retainedCost - fullCost) / 2) <=
      ((2 * r) * (5000 * p * t ^ 2) + (2 * r * t) * (9 * t)) / 2 := by
    rw [abs_div]
    norm_num
    linarith only [hLinear]
  have hTriangle :
      abs (logCost - (r - hamiltonianDeletedOverlap T S U) - fullCost / 2) <=
      abs (logCost - (r - hamiltonianDeletedOverlap T S U) - retainedCost / 2) +
        abs ((retainedCost - fullCost) / 2) := by
    have hEq : logCost - (r - hamiltonianDeletedOverlap T S U) - fullCost / 2 =
        (logCost - (r - hamiltonianDeletedOverlap T S U) - retainedCost / 2) +
          (retainedCost - fullCost) / 2 := by ring
    rw [hEq]
    exact abs_add_le _ _
  nlinarith only [hTriangle, hCost, hDiv, hMTCube, hLower, hPositiveTerm]


theorem stochastic_deleted_support_scaling_cost_exists
    (T : Matrix Iota Iota Real) (S U : Finset Iota) (hCard : S.card = U.card)
    (q a rho : Real) (hq : (Fintype.card Iota : Real) * q = 1) (ha : 1 <= a)
    (hRow : forall i, Finset.sum Finset.univ (fun j => T i j) = 1)
    (hCol : forall j, Finset.sum Finset.univ (fun i => T i j) = 1)
    (hNonneg : forall i j, 0 <= T i j) (hUpper : forall i j, T i j <= a * q)
    (hNorm : norm (centeredKernel T q) <= rho) (hRho : rho < 1)
    (hSmall : (U.card : Real) * a ^ 2 * q / (1 - rho) ^ 2 <= 1 / 1000) :
    let R : Finset (Sum Iota Iota) := Compl.compl (S.disjSum U)
    let K := hamiltonianRepairKernel T q
    let ell := hamiltonianDeletedSupportDefect T S U
    exists z : R -> Real,
      norm z <= 20 * (U.card : Real) * a * q / (1 - rho) /\
      norm (z - (fun i : R => K.mulVec ell i.val)) <=
        5000 * (U.card : Real) ^ 2 * a ^ 3 * q ^ 2 / (1 - rho) ^ 3 /\
      (forall i : R, 0 < 1 + z i) /\
      (forall i : R, (1 + z i) *
        (hamiltonianRetainedKernel T S U).mulVec (1 + z) i = 1) /\
      abs (Finset.sum Finset.univ (fun i : R => Real.log (1 + z i)) -
        ((U.card : Real) - hamiltonianDeletedOverlap T S U) -
          Finset.sum Finset.univ (fun i : Sum Iota Iota => ell i * K.mulVec ell i) / 2) <=
        100000 * (U.card : Real) ^ 3 * a ^ 3 * q ^ 2 / (1 - rho) ^ 3 := by
  have hRepair := stochastic_deleted_support_repair_exists T S U hCard q a rho hq ha
    hRow hCol hNonneg hUpper hNorm hRho hSmall
  let z := Classical.choose hRepair
  have hz := Classical.choose_spec hRepair
  have hDen : Not ((1 - rho) = 0) := ne_of_gt (sub_pos.mpr hRho)
  have hRadius :
      20 * (U.card : Real) * a * q / (1 - rho) =
        20 * (U.card : Real) * (a / (1 - rho)) * q := by
    field_simp <;> ring
  have hError :
      5000 * (U.card : Real) ^ 2 * a ^ 3 * q ^ 2 / (1 - rho) ^ 3 =
        5000 * (a / (1 - rho)) *
          ((U.card : Real) * (a / (1 - rho)) * q) ^ 2 := by
    field_simp <;> ring
  have hCostError :
      100000 * (U.card : Real) * (a / (1 - rho)) *
        ((U.card : Real) * (a / (1 - rho)) * q) ^ 2 =
          100000 * (U.card : Real) ^ 3 * a ^ 3 * q ^ 2 / (1 - rho) ^ 3 := by
    field_simp <;> ring
  have hZ : norm z <= 20 * (U.card : Real) * (a / (1 - rho)) * q := by
    rw [<- hRadius]
    exact hz.1
  have hClose : norm (z -
      (fun i : (Compl.compl (S.disjSum U) : Finset (Sum Iota Iota)) =>
        (hamiltonianRepairKernel T q).mulVec (hamiltonianDeletedSupportDefect T S U) i.val)) <=
      5000 * (a / (1 - rho)) * ((U.card : Real) * (a / (1 - rho)) * q) ^ 2 := by
    rw [<- hError]
    exact hz.2.1
  have hScaling : forall i : (Compl.compl (S.disjSum U) : Finset (Sum Iota Iota)),
      (1 + z i) * (hamiltonianRetainedKernel T S U).mulVec (1 + z) i = 1 :=
    hz.2.2.2
  have hCost := stochastic_deleted_support_scaling_cost T S U hCard q a rho hq ha
    hRow hCol hNonneg hUpper hNorm hRho hSmall z hZ hClose hScaling
  rw [hCostError] at hCost
  exact Exists.intro z
    (And.intro hz.1 (And.intro hz.2.1
      (And.intro hz.2.2.1 (And.intro hScaling hCost))))

end PrimeFactorOscillations

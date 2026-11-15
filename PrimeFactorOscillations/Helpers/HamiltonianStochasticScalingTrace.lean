/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianScalingTraceBudget
import PrimeFactorOscillations.Helpers.HamiltonianScalingTraceCancellation

/-! # Full actual signed scaling trace with every support correction

All four support/Schur/quadratic/centering errors are estimated together.
The signed main trace is evaluated exactly, then the existing retained
linear comparison transfers its displacement to the actual K-ell source.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations

variable {Iota : Type*} [Fintype Iota] [DecidableEq Iota] [Nonempty Iota]

theorem stochastic_signed_scaling_trace
    (T : Matrix Iota Iota Real) (S U : Finset Iota) (hCard : S.card = U.card)
    (q a rho : Real) (hq : (Fintype.card Iota : Real) * q = 1) (ha : 1 <= a)
    (hRow : forall i, Finset.sum Finset.univ (fun j => T i j) = 1)
    (hCol : forall j, Finset.sum Finset.univ (fun i => T i j) = 1)
    (hNonneg : forall i j, 0 <= T i j) (hUpper : forall i j, T i j <= a * q)
    (hNorm : norm (centeredKernel T q) <= rho) (hRho : rho < 1)
    (hSmall : (U.card : Real) * a ^ 2 * q / (1 - rho) ^ 2 <= 1 / 1000)
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
    let R0 := Ring.inverse H
    let Gamma := Omega * R0
    let J := hamiltonianBoundaryKernel R0 D
    let qNew := q / (1 - (U.card : Real) * q)
    let E := hamiltonianScalingPerturbation (hamiltonianRetainedKernel T S U)
      (hamiltonianRetainedCrossMask S U) z q qNew
    let k := (hamiltonianRepairKernel T q).mulVec (hamiltonianDeletedSupportDefect T S U)
    abs (Matrix.trace (J * E) +
      2 * Finset.sum Finset.univ (fun i : Sum Iota Iota => (-Gamma i i) * k i)) <=
        60000 * (U.card : Real) ^ 2 * (a / (1 - rho)) ^ 4 * q ^ 2 := by
  let delta := 1 - rho
  let r : Real := U.card
  let p := a / delta
  let t := r * p * q
  let c := 2 * p * q
  let b := 20 * t
  let v := a * q
  let eJ := 16 * r * p ^ 2 * q ^ 2
  let eE := 44 * r * p ^ 2 * q ^ 2
  let D := S.disjSum U
  let R : Finset (Sum Iota Iota) := Compl.compl D
  let P := bipartiteLift T
  let C := bipartiteLift (fun _ _ : Iota => (1 : Real))
  let Omega := bipartiteLift (centeredKernel T q)
  let H := (1 : Matrix (Sum Iota Iota) (Sum Iota Iota) Real) + Omega
  let R0 := Ring.inverse H
  let Gamma := Omega * R0
  let J := hamiltonianBoundaryKernel R0 D
  let qNew := q / (1 - r * q)
  let E := hamiltonianScalingPerturbation (hamiltonianRetainedKernel T S U)
    (hamiltonianRetainedCrossMask S U) z q qNew
  let x := hamiltonianZeroExtend D z
  let X := Matrix.diagonal x * P + P * Matrix.diagonal x
  let w := fun i : Sum Iota Iota => -Gamma i i
  let k := (hamiltonianRepairKernel T q).mulVec (hamiltonianDeletedSupportDefect T S U)
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
  have hc : 0 <= c := by dsimp only [c]; positivity
  have hb : 0 <= b := by dsimp only [b]; positivity
  have hv : 0 <= v := mul_nonneg ha0 hq0
  have heJ : 0 <= eJ := by dsimp only [eJ]; positivity
  have heE : 0 <= eE := by dsimp only [eE]; positivity
  have hPt : p * t <= 1 / 1000 := by
    have hEq : p * t = r * a ^ 2 * q / delta ^ 2 := by dsimp only [p, t]; field_simp
    rw [hEq]
    exact hSmall
  have htSmall : t <= 1 / 1000 := by
    have hMul := mul_le_mul_of_nonneg_right hp ht
    nlinarith only [hMul, hPt]
  have hAP : a <= p := by
    have h := mul_le_mul_of_nonneg_right hDelta1 hp0
    nlinarith only [h, hpClear]
  have hDCard : (D.card : Real) = 2 * r := by
    simp only [D, Finset.card_disjSum, hCard, Nat.cast_add, r]
    ring
  have hFullQ : (Fintype.card (Sum Iota Iota) : Real) * q = 2 := by
    simp only [Fintype.card_sum, Nat.cast_add]
    nlinarith only [hq]
  have hFullC : (Fintype.card (Sum Iota Iota) : Real) * c = 4 * p := by
    dsimp only [c]
    nlinarith only [congrArg (fun y : Real => y * (2 * p)) hFullQ]
  have hGamma (i j : Sum Iota Iota) : abs (Gamma i j) <= c := by
    have h := stochastic_block_covariance_entry_bound T q a rho hq ha
      hRow hCol hNonneg hUpper hRho hNorm i j
    change delta * norm (Gamma i j) <= (2 - rho) * (a * q) at h
    rw [Real.norm_eq_abs] at h
    have hSigned := mul_nonneg hRho0 hv
    have hClear : delta * c = 2 * a * q := by dsimp only [c]; rw [<- hpClear]; ring
    nlinarith only [h, hSigned, hClear, hDelta]
  have hUnit : IsUnit H := by
    have hOmegaNorm : norm Omega <= rho :=
      le_trans (bipartiteLift_l2_norm_le _) hNorm
    have hNeg : norm (-Omega) < 1 := by rw [norm_neg]; exact lt_of_le_of_lt hOmegaNorm hRho
    simpa only [sub_neg_eq_add] using isUnit_one_sub_of_norm_lt_one hNeg
  have hR0 : R0 = 1 - Gamma := hamiltonian_resolvent_one_sub Omega hUnit
  have hFullTrace := stochastic_full_scaling_trace_cancellation T q rho hq hRow hCol hNorm hRho
  have hCenter : Matrix.trace (R0 * C) = 0 := hFullTrace.2.2.2.2.1
  have hPN (i j : Sum Iota Iota) : 0 <= P i j := by
    cases i <;> cases j <;>
      simp [P, bipartiteLift, Matrix.fromBlocks, Matrix.transpose, hNonneg]
  have hPRows (i : Sum Iota Iota) : Finset.sum Finset.univ (fun j => P i j) = 1 := by
    cases i with
    | inl i => simpa [P, bipartiteLift, Matrix.fromBlocks, Fintype.sum_sum_type] using hRow i
    | inr i => simpa [P, bipartiteLift, Matrix.fromBlocks, Matrix.transpose,
        Fintype.sum_sum_type] using hCol i
  have hPSym (i j : Sum Iota Iota) : P i j = P j i := by cases i <;> cases j <;> rfl
  have hPCols (j : Sum Iota Iota) : Finset.sum Finset.univ (fun i => P i j) = 1 := by
    calc
      _ = Finset.sum Finset.univ (fun i => P j i) :=
        Finset.sum_congr rfl (fun i _ => hPSym i j)
      _ = _ := hPRows j
  have hPEntry (i j : Sum Iota Iota) : abs (P i j) <= v := by
    cases i <;> cases j <;>
      simp [P, v, bipartiteLift, Matrix.fromBlocks, Matrix.transpose,
        abs_of_nonneg, hNonneg, hUpper, hv]
  have hCEntry (i j : Sum Iota Iota) : abs (C i j) <= 1 := by
    cases i <;> cases j <;> norm_num [C, bipartiteLift, Matrix.fromBlocks, Matrix.transpose]
  have hRadius : 20 * r * a * q / (1 - rho) = b := by dsimp only [b, t, p, delta]; ring
  have hZNorm : norm z <= b := by rw [hRadius] at hZ; exact hZ
  have hZPoint (i : R) : abs (z i) <= b := by
    have h := (pi_norm_le_iff_of_nonneg hb).mp hZNorm i
    simpa only [Real.norm_eq_abs] using h
  have hInverse := stochastic_retained_covariance_inverse_budgets T S U hCard q a rho hq ha
    hRow hCol hNonneg hUpper hNorm hRho hSmall
  have hJEntry (i j : R) : abs (J i j - R0 i.val j.val) <= eJ := hInverse.2.1 i j
  have hPerturb := stochastic_scaling_centering_perturbation_entry T S U q a rho hq ha
    hNonneg hUpper hRho0 hRho hSmall z hZ
  have hEEntry (i j : R) : abs (E i j) <= eE := hPerturb.2.2 i j
  have hRaw := hamiltonian_scaling_trace_budget R0 Gamma P C D z J q qNew
    c b v eJ eE hc hb hv heJ heE hR0 hCenter hGamma
    (hamiltonian_bipartite_diagonal_zero T)
    (hamiltonian_bipartite_diagonal_zero (fun _ _ : Iota => (1 : Real)))
    hCEntry hPN hPRows hPCols hPEntry hZPoint hJEntry hEEntry
  change abs (Matrix.trace (J * E) - Matrix.trace (R0 * X)) <=
    (R.card : Real) ^ 2 * eJ * eE + (R.card : Real) ^ 2 * c * b ^ 2 * v +
      abs (q - qNew) * (2 * (D.card : Real) * (Fintype.card (Sum Iota Iota) : Real) * c) +
      2 * (D.card : Real) * c * b at hRaw
  have hRCard : (R.card : Real) <= (Fintype.card (Sum Iota Iota) : Real) := by
    have h : (R.card : Real) <= ((Finset.univ : Finset (Sum Iota Iota)).card : Real) :=
      Nat.cast_le.mpr (Finset.card_le_card (Finset.subset_univ R))
    simpa only [Finset.card_univ] using h
  have hRQ : (R.card : Real) * q <= 2 := by
    nlinarith only [mul_le_mul_of_nonneg_right hRCard hq0, hFullQ]
  have hRQSquare : (R.card : Real) ^ 2 * q ^ 2 <= 4 := by
    have h := mul_le_mul hRQ hRQ
      (mul_nonneg (Nat.cast_nonneg _) hq0) (by norm_num)
    nlinarith only [h]
  have hSchur : (R.card : Real) ^ 2 * eJ * eE <= 2816 * r ^ 2 * p ^ 4 * q ^ 2 := by
    calc
      _ = (704 * r ^ 2 * p ^ 4 * q ^ 2) * ((R.card : Real) ^ 2 * q ^ 2) := by
        dsimp only [eJ, eE]; ring
      _ <= (704 * r ^ 2 * p ^ 4 * q ^ 2) * 4 :=
        mul_le_mul_of_nonneg_left hRQSquare
          (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg r))
            (pow_nonneg hp0 4)) (sq_nonneg q))
      _ = _ := by ring
  have hQuadratic : (R.card : Real) ^ 2 * c * b ^ 2 * v <=
      3200 * r ^ 2 * p ^ 4 * q ^ 2 := by
    calc
      _ = (800 * p * a * t ^ 2) * ((R.card : Real) ^ 2 * q ^ 2) := by
        dsimp only [c, b, v]; ring
      _ <= (800 * p * a * t ^ 2) * 4 :=
        mul_le_mul_of_nonneg_left hRQSquare
          (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hp0) ha0) (sq_nonneg t))
      _ = (3200 * p * t ^ 2) * a := by ring
      _ <= (3200 * p * t ^ 2) * p :=
        mul_le_mul_of_nonneg_left hAP
          (mul_nonneg (mul_nonneg (by norm_num) hp0) (sq_nonneg t))
      _ = _ := by dsimp only [t]; ring
  have hrq : r * q <= 1 / 2 := by
    have hMul := mul_le_mul_of_nonneg_right hp (mul_nonneg hr hq0)
    dsimp only [t] at htSmall
    nlinarith only [hMul, htSmall]
  have hRef := hamiltonian_rank_shift_reference (Fintype.card Iota) r q hq hr hq0 hrq
  have hCenterFactor : 2 * (D.card : Real) * (Fintype.card (Sum Iota Iota) : Real) * c =
      16 * r * p := by
    calc
      _ = 2 * (D.card : Real) * ((Fintype.card (Sum Iota Iota) : Real) * c) := by ring
      _ = _ := by rw [hDCard, hFullC]; ring
  have hCenterError :
      abs (q - qNew) * (2 * (D.card : Real) * (Fintype.card (Sum Iota Iota) : Real) * c) <=
        32 * r ^ 2 * p * q ^ 2 := by
    rw [hCenterFactor]
    have h := mul_le_mul_of_nonneg_right hRef.2.2
      (mul_nonneg (mul_nonneg (by norm_num : (0 : Real) <= 16) hr) hp0)
    nlinarith only [h]
  have hRemovedEq : 2 * (D.card : Real) * c * b = 160 * r ^ 2 * p ^ 2 * q ^ 2 := by
    rw [hDCard]
    dsimp only [c, b, t]
    ring
  have hpSq : 1 <= p ^ 2 := by nlinarith only [hp, hp0]
  have hp24 : p ^ 2 <= p ^ 4 := by
    have h := mul_le_mul_of_nonneg_left hpSq (sq_nonneg p)
    nlinarith only [h]
  have hp12 : p <= p ^ 2 := by
    have h := mul_le_mul_of_nonneg_left hp hp0
    nlinarith only [h]
  have hp14 : p <= p ^ 4 := le_trans hp12 hp24
  have hLow2 : r ^ 2 * p ^ 2 * q ^ 2 <= r ^ 2 * p ^ 4 * q ^ 2 := by
    have h := mul_le_mul_of_nonneg_right hp24 (mul_nonneg (sq_nonneg r) (sq_nonneg q))
    nlinarith only [h]
  have hLow1 : r ^ 2 * p * q ^ 2 <= r ^ 2 * p ^ 4 * q ^ 2 := by
    have h := mul_le_mul_of_nonneg_right hp14 (mul_nonneg (sq_nonneg r) (sq_nonneg q))
    nlinarith only [h]
  have hBase : 0 <= r ^ 2 * p ^ 4 * q ^ 2 :=
    mul_nonneg (mul_nonneg (sq_nonneg r) (pow_nonneg hp0 4)) (sq_nonneg q)
  have hBudget : abs (Matrix.trace (J * E) - Matrix.trace (R0 * X)) <=
      6500 * r ^ 2 * p ^ 4 * q ^ 2 := by
    rw [hRemovedEq] at hRaw
    nlinarith only [hRaw, hSchur, hQuadratic, hCenterError, hLow2, hLow1, hBase]
  have hWeightEntry (i : Sum Iota Iota) : abs (w i) <= c := by
    dsimp only [w]
    rw [abs_neg]
    exact hGamma i i
  have hWeightMass : Finset.sum Finset.univ (fun i => abs (w i)) <= 4 * p := by
    calc
      _ <= Finset.sum Finset.univ (fun _ : Sum Iota Iota => c) :=
        Finset.sum_le_sum (fun i _ => hWeightEntry i)
      _ = (Fintype.card (Sum Iota Iota) : Real) * c := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ = _ := hFullC
  have hWeightDeleted : Finset.sum Finset.univ (fun i : D => abs (w i.val)) <=
      4 * r * p * q := by
    calc
      _ <= Finset.sum Finset.univ (fun _ : D => c) :=
        Finset.sum_le_sum (fun i _ => hWeightEntry i.val)
      _ = (D.card : Real) * c := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul]
      _ = _ := by rw [hDCard]; dsimp only [c]; ring
  have hAr : r * a * q = delta * t := by
    calc
      _ = r * (delta * p) * q := by rw [hpClear]
      _ = _ := by dsimp only [t]; ring
  have hK (i : Sum Iota Iota) : abs (k i) <= 9 * t := by
    have h := stochastic_deleted_support_linear_repair T S U hCard q a rho hq ha
      hRow hCol hNonneg hUpper hNorm hRho i
    change delta * abs (k i) <= 9 * r * a * q at h
    nlinarith only [h, hAr, hDelta]
  have hErrorEq : 5000 * r ^ 2 * a ^ 3 * q ^ 2 / (1 - rho) ^ 3 = 5000 * p * t ^ 2 := by
    dsimp only [p, t, delta]
    field_simp
  have hCloseNorm : norm (z - (fun i : R => k i.val)) <= 5000 * p * t ^ 2 := by
    rw [hErrorEq] at hClose
    exact hClose
  have hClosePoint (i : R) : abs (z i - k i.val) <= 5000 * p * t ^ 2 := by
    have h := (pi_norm_le_iff_of_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) hp0) (sq_nonneg t))).mp hCloseNorm i
    simpa only [Real.norm_eq_abs, Pi.sub_apply] using h
  have hWeight := hamiltonian_retained_linear_cost_error D w k z
    (5000 * p * t ^ 2) (9 * t) (4 * p) (4 * r * p * q)
    (mul_nonneg (mul_nonneg (by norm_num) hp0) (sq_nonneg t))
    (mul_nonneg (by norm_num) ht) hClosePoint (fun i => hK i.val)
    hWeightMass hWeightDeleted
  have hZero := hamiltonianZeroExtend_weighted_sum D z w
  rw [<- hZero] at hWeight
  change abs (Finset.sum Finset.univ (fun i => w i * x i) -
    Finset.sum Finset.univ (fun i => w i * k i)) <=
      (4 * p) * (5000 * p * t ^ 2) + (4 * r * p * q) * (9 * t) at hWeight
  have hTwiceEq :
      2 * ((4 * p) * (5000 * p * t ^ 2) + (4 * r * p * q) * (9 * t)) =
        40000 * r ^ 2 * p ^ 4 * q ^ 2 + 72 * r ^ 2 * p ^ 2 * q ^ 2 := by
    dsimp only [t]
    ring
  have hTwoWeight : abs (2 * (Finset.sum Finset.univ (fun i => w i * k i) -
      Finset.sum Finset.univ (fun i => w i * x i))) <=
        40072 * r ^ 2 * p ^ 4 * q ^ 2 := by
    rw [abs_mul, abs_sub_comm, abs_of_nonneg (by norm_num : (0 : Real) <= 2)]
    have h := mul_le_mul_of_nonneg_left hWeight (by norm_num : (0 : Real) <= 2)
    rw [hTwiceEq] at h
    nlinarith only [h, hLow2]
  have hTraceMain : Matrix.trace (R0 * X) =
      -2 * Finset.sum Finset.univ (fun i => w i * x i) := by
    have h := hFullTrace.2.2.2.2.2 x
    change Matrix.trace (R0 * X) =
      2 * Finset.sum Finset.univ (fun i => Gamma i i * x i) at h
    have hSign : Finset.sum Finset.univ (fun i => w i * x i) =
        -Finset.sum Finset.univ (fun i => Gamma i i * x i) := by
      simp only [w, neg_mul, Finset.sum_neg_distrib]
    nlinarith only [h, hSign]
  change abs (Matrix.trace (J * E) +
    2 * Finset.sum Finset.univ (fun i => w i * k i)) <= 60000 * r ^ 2 * p ^ 4 * q ^ 2
  have hFinalEq : Matrix.trace (J * E) + 2 * Finset.sum Finset.univ (fun i => w i * k i) =
      (Matrix.trace (J * E) - Matrix.trace (R0 * X)) +
        2 * (Finset.sum Finset.univ (fun i => w i * k i) -
          Finset.sum Finset.univ (fun i => w i * x i)) := by
    rw [hTraceMain]
    ring
  rw [hFinalEq]
  have hTriangle := abs_add_le (Matrix.trace (J * E) - Matrix.trace (R0 * X))
    (2 * (Finset.sum Finset.univ (fun i => w i * k i) -
      Finset.sum Finset.univ (fun i => w i * x i)))
  nlinarith only [hTriangle, hBudget, hTwoWeight, hBase]

end PrimeFactorOscillations

/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianRepairedSquareGap
import PrimeFactorOscillations.Helpers.HamiltonianStochasticRepair

/-! # One actual repair witness with every uniform permanent hypothesis

The same positive physical scaling is retained for the determinant,
scaling cost, covariance comparison and smaller square permanent.
-/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations

variable {Iota : Type*} [Fintype Iota] [DecidableEq Iota] [Nonempty Iota]

theorem stochastic_repaired_square_exists
    (T : Matrix Iota Iota Real) (S U : Finset Iota) (hCard : S.card = U.card)
    (q a rho : Real) (hN : 4 <= Fintype.card Iota)
    (hq : (Fintype.card Iota : Real) * q = 1) (ha : 1 <= a)
    (hRow : forall i, Finset.univ.sum (fun j => T i j) = 1)
    (hCol : forall j, Finset.univ.sum (fun i => T i j) = 1)
    (hNonneg : forall i j, 0 <= T i j) (hUpper : forall i j, T i j <= a * q)
    (hNorm : norm (centeredKernel T q) <= rho) (hRho : rho < 1)
    (hSmall : (U.card : Real) * (a / (1 - rho)) ^ 3 * q <= 1 / 10000) :
    let R : Finset (Sum Iota Iota) := Compl.compl (S.disjSum U)
    let J : Finset Iota := Compl.compl U
    let qNew := q / (1 - (U.card : Real) * q)
    2 <= Fintype.card J /\
    (Fintype.card J : Real) * qNew = 1 /\
    exists z : R -> Real,
      norm z <= 20 * (U.card : Real) * a * q / (1 - rho) /\
      norm (z - (fun i : R =>
        (hamiltonianRepairKernel T q).mulVec (hamiltonianDeletedSupportDefect T S U) i.val)) <=
        5000 * (U.card : Real) ^ 2 * a ^ 3 * q ^ 2 / (1 - rho) ^ 3 /\
      (forall i : R, 0 < 1 + z i) /\
      (forall i : R, (1 + z i) * (hamiltonianRetainedKernel T S U).mulVec (1 + z) i = 1) /\
      (forall i j, 0 <= hamiltonianRepairedSquareKernel T S U hCard z i j) /\
      ((forall i, Finset.univ.sum (fun j =>
        hamiltonianRepairedSquareKernel T S U hCard z i j) = 1) /\
        (forall j, Finset.univ.sum (fun i =>
          hamiltonianRepairedSquareKernel T S U hCard z i j) = 1)) /\
      (forall i j, hamiltonianRepairedSquareKernel T S U hCard z i j <= 2 * a * qNew) /\
      norm (centeredKernel (hamiltonianRepairedSquareKernel T S U hCard z) qNew) <=
        1 - (1 - rho) / 2 := by
  let n : Real := Fintype.card Iota
  let r : Real := U.card
  let delta := 1 - rho
  let p := a / delta
  let R : Finset (Sum Iota Iota) := Compl.compl (S.disjSum U)
  let J : Finset Iota := Compl.compl U
  let qNew := q / (1 - r * q)
  have hDelta : 0 < delta := sub_pos.mpr hRho
  have hDelta0 : Not (delta = 0) := ne_of_gt hDelta
  have hRho0 : 0 <= rho := le_trans (norm_nonneg _) hNorm
  have hDelta1 : delta <= 1 := by dsimp only [delta]; linarith only [hRho0]
  have ha0 : 0 <= a := le_trans (by norm_num) ha
  have hn : 0 < n := Nat.cast_pos.mpr Fintype.card_pos
  have hqPos : 0 < q := by nlinarith only [hq, hn]
  have hq0 : 0 <= q := le_of_lt hqPos
  have hr : 0 <= r := Nat.cast_nonneg _
  have hp0 : 0 <= p := div_nonneg ha0 (le_of_lt hDelta)
  have hpClear : delta * p = a := by dsimp only [p]; field_simp
  have hp : 1 <= p := by nlinarith only [hpClear, hDelta1, hp0, ha]
  have hP2 : p <= p ^ 2 := by nlinarith only [hp]
  have hP3 : p ^ 2 <= p ^ 3 := by
    have h := mul_le_mul_of_nonneg_left hp (sq_nonneg p)
    nlinarith only [h]
  have hPQ : r * p * q <= 1 / 10000 := by
    have h := mul_le_mul_of_nonneg_left (le_trans hP2 hP3) (mul_nonneg hr hq0)
    nlinarith only [h, hSmall]
  have hRQ : r * q <= 1 / 10000 := by
    have h := mul_le_mul_of_nonneg_left hp (mul_nonneg hr hq0)
    nlinarith only [h, hPQ]
  have hWeakEq : r * a ^ 2 * q / (1 - rho) ^ 2 = r * p ^ 2 * q := by
    dsimp only [p, delta]
    field_simp
  have hWeak : r * a ^ 2 * q / (1 - rho) ^ 2 <= 1 / 1000 := by
    rw [hWeakEq]
    have h := mul_le_mul_of_nonneg_left hP3 (mul_nonneg hr hq0)
    nlinarith only [h, hSmall]
  have hDenPos : 0 < 1 - r * q := by linarith only [hRQ]
  have hDen : Not (1 - r * q = 0) := ne_of_gt hDenPos
  have hShift : q <= qNew := by
    have hClear : (1 - r * q) * qNew = q := by
      dsimp only [qNew]
      rw [<- mul_div_assoc, mul_comm (1 - r * q) q, mul_div_assoc, div_self hDen, mul_one]
    have hNewPos : 0 <= qNew := div_nonneg hq0 (le_of_lt hDenPos)
    have hPos := mul_nonneg (mul_nonneg hr hq0) hNewPos
    nlinarith only [hClear, hPos]
  have hRank := hamiltonian_rank_shift_reference (Fintype.card Iota) r q hq hr hq0
    (le_trans hRQ (by norm_num))
  have hUle : U.card <= Fintype.card Iota := Finset.card_le_univ U
  have hJ : (Fintype.card J : Real) = n - r := by
    simp only [J, Fintype.card_coe, Finset.card_compl, Nat.cast_sub hUle, n, r]
  have hHalf : r <= n / 2 := by
    by_contra h
    have hProduct := mul_pos (sub_pos.mpr (lt_of_not_ge h)) hqPos
    nlinarith only [hProduct, hq, hRQ]
  have hn4 : (4 : Real) <= n := by
    change (4 : Real) <= (Fintype.card Iota : Real)
    exact_mod_cast hN
  have hJ2Real : (2 : Real) <= (Fintype.card J : Real) := by
    rw [hJ]
    linarith only [hHalf, hn4]
  have hJ2 : 2 <= Fintype.card J := by exact_mod_cast hJ2Real
  have hJq : (Fintype.card J : Real) * qNew = 1 := by
    rw [hJ]
    exact hRank.2.1
  have hRepair := stochastic_deleted_support_repair_exists T S U hCard q a rho hq ha
    hRow hCol hNonneg hUpper hNorm hRho hWeak
  let z := Classical.choose hRepair
  have hz := Classical.choose_spec hRepair
  have hRadius : 20 * r * a * q / (1 - rho) = 20 * (r * p * q) := by
    dsimp only [p, delta]
    ring
  have hZSmall : norm z <= 1 / 50 := by
    have hZ := hz.1
    change norm z <= 20 * r * a * q / (1 - rho) at hZ
    rw [hRadius] at hZ
    linarith only [hZ, hPQ]
  have hPoint (i : R) : abs (z i) <= 1 / 50 := by
    have h := (pi_norm_le_iff_of_nonneg (by norm_num : (0 : Real) <= 1 / 50)).mp hZSmall i
    simpa only [Real.norm_eq_abs] using h
  have hPhysical : forall i : R,
      (1 + z i) * (hamiltonianRetainedKernel T S U).mulVec (1 + z) i = 1 := hz.2.2.2
  have hPos : forall i : R, 0 <= 1 + z i := fun i => le_of_lt (hz.2.2.1 i)
  refine And.intro hJ2 (And.intro hJq (Exists.intro z ?_))
  refine And.intro hz.1 (And.intro hz.2.1 (And.intro hz.2.2.1 (And.intro hPhysical ?_)))
  refine And.intro (hamiltonian_repaired_square_nonnegative T S U hCard z hNonneg hPos) ?_
  refine And.intro (hamiltonian_repaired_square_stochastic T S U hCard z hPhysical) ?_
  exact And.intro
    (hamiltonian_repaired_square_entry_bound T S U hCard z a q qNew ha0 hq0 hShift
      hNonneg hUpper hPoint)
    (stochastic_repaired_square_gap T S U hCard q a rho hq ha hNonneg hUpper hNorm hRho
      hSmall z hz.1)

end PrimeFactorOscillations

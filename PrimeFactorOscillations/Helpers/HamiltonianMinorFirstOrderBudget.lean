/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianMinorQuadraticCompensation

/-! # Magnitude of the retained signed minor correction

This estimate is used only for the exponential remainder. The actual
signed correction remains in the minor and occupancy formulas.
-/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations

variable {Iota : Type*} [Fintype Iota] [DecidableEq Iota]

def hamiltonianMinorFirstOrder (T : Matrix Iota Iota Real)
    (S U : Finset Iota) (q : Real) : Real :=
  let u := hamiltonianDeletedSupportIndicator S U
  let K := hamiltonianRepairKernel T q
  let G := resolventCovariance (bipartiteLift (centeredKernel T q))
  let h := fun i => -G i i
  let v := fun i => (1 / 2 : Real) * h i - K.mulVec h i
  (U.card : Real) * ((U.card : Real) - 1) * q +
    dotProduct u (G.mulVec u) + 2 * dotProduct v u

variable [Nonempty Iota]

theorem stochastic_minor_first_order_budget
    (T : Matrix Iota Iota Real) (S U : Finset Iota) (hCard : S.card = U.card)
    (q a delta : Real) (hq : (Fintype.card Iota : Real) * q = 1) (ha : 1 <= a)
    (hDelta : 0 < delta) (hDelta1 : delta <= 1)
    (hRow : forall i, Finset.univ.sum (fun j => T i j) = 1)
    (hCol : forall j, Finset.univ.sum (fun i => T i j) = 1)
    (hNonneg : forall i j, 0 <= T i j) (hUpper : forall i j, T i j <= a * q)
    (hNorm : norm (centeredKernel T q) <= 1 - delta) :
    abs (hamiltonianMinorFirstOrder T S U q) <=
      100 * (1 + (U.card : Real)) ^ 2 * (a / delta) ^ 2 * q := by
  let r : Real := U.card
  let p := a / delta
  let D := S.disjSum U
  let u := hamiltonianDeletedSupportIndicator S U
  let K := hamiltonianRepairKernel T q
  let G := resolventCovariance (bipartiteLift (centeredKernel T q))
  let h := fun i => -G i i
  let v := fun i => (1 / 2 : Real) * h i - K.mulVec h i
  have hr0 : 0 <= r := Nat.cast_nonneg _
  have hn : 0 < (Fintype.card Iota : Real) := Nat.cast_pos.mpr Fintype.card_pos
  have hq0 : 0 <= q := by nlinarith only [hq, hn]
  have ha0 : 0 <= a := le_trans (by norm_num) ha
  have hp0 : 0 <= p := div_nonneg ha0 (le_of_lt hDelta)
  have hpClear : delta * p = a := by dsimp only [p]; field_simp
  have hp : 1 <= p := by nlinarith only [hpClear, hDelta1, hp0, ha]
  have hGap : 1 - (1 - delta) = delta := by ring
  have hRho : 1 - delta < 1 := by linarith only [hDelta]
  have hDCard : (Fintype.card D : Real) = 2 * r := by
    simp only [D, Fintype.card_coe, Finset.card_disjSum, hCard, Nat.cast_add, r]
    ring
  have hPQ0 : 0 <= p * q := mul_nonneg hp0 hq0
  have hP2Q0 : 0 <= p ^ 2 * q := mul_nonneg (sq_nonneg p) hq0
  have hPQ : p * q <= p ^ 2 * q := by
    have h := mul_le_mul_of_nonneg_right hp hPQ0
    nlinarith only [h]
  have hG (i j : Sum Iota Iota) : abs (G i j) <= 2 * p * q := by
    have h := stochastic_block_covariance_entry_bound T q a (1 - delta) hq ha
      hRow hCol hNonneg hUpper hRho hNorm i j
    change (1 - (1 - delta)) * norm (G i j) <= (2 - (1 - delta)) * (a * q) at h
    rw [hGap, Real.norm_eq_abs] at h
    have hCoeff : 2 - (1 - delta) <= 2 := by linarith only [hDelta1]
    have hScaled := mul_le_mul_of_nonneg_right hCoeff (mul_nonneg ha0 hq0)
    apply le_of_mul_le_mul_left _ hDelta
    calc
      _ <= (2 - (1 - delta)) * (a * q) := h
      _ <= 2 * (a * q) := hScaled
      _ = delta * (2 * p * q) := by
        calc
          _ = 2 * (delta * p) * q := by rw [hpClear]; ring
          _ = _ := by ring
  have hDiag (i : Sum Iota Iota) : abs (h i) <= 2 * p * q := by
    simpa only [h, abs_neg] using hG i i
  have hRowK (i : Sum Iota Iota) :
      Finset.univ.sum (fun j => abs (K i j)) <= 1 + 8 * p := by
    have h := stochastic_repair_kernel_row T q a (1 - delta) hq ha
      hRow hCol hNonneg hUpper hNorm hRho i
    rw [hGap] at h
    apply le_of_mul_le_mul_left _ hDelta
    nlinarith only [h, hpClear]
  have hKh (i : Sum Iota Iota) : abs (K.mulVec h i) <= 18 * p ^ 2 * q := by
    calc
      _ <= Finset.univ.sum (fun j => abs (K i j * h j)) := Finset.abs_sum_le_sum_abs _ _
      _ = Finset.univ.sum (fun j => abs (K i j) * abs (h j)) := by simp only [abs_mul]
      _ <= Finset.univ.sum (fun j => abs (K i j) * (2 * p * q)) :=
        Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (hDiag j) (abs_nonneg _))
      _ = (Finset.univ.sum (fun j => abs (K i j))) * (2 * p * q) := by rw [Finset.sum_mul]
      _ <= (1 + 8 * p) * (2 * p * q) :=
        mul_le_mul_of_nonneg_right (hRowK i) (by nlinarith only [hPQ0])
      _ <= _ := by nlinarith only [hPQ]
  have hV (i : Sum Iota Iota) : abs (v i) <= 19 * p ^ 2 * q := by
    have hAbs := norm_sub_le ((1 / 2 : Real) * h i) (K.mulVec h i)
    simp only [Real.norm_eq_abs, abs_mul, show abs (1 / 2 : Real) = 1 / 2 by norm_num] at hAbs
    change abs ((1 / 2 : Real) * h i - K.mulVec h i) <= _
    nlinarith only [hAbs, hDiag i, hKh i, hPQ]
  have hGu (i : Sum Iota Iota) :
      G.mulVec u i = Finset.univ.sum (fun d : D => G i d.val) := by
    change dotProduct (fun j => G i j) u = _
    rw [dotProduct_comm, hamiltonian_deleted_indicator_dot_sum]
  have hGuBudget (i : Sum Iota Iota) : abs (G.mulVec u i) <= 4 * r * p * q := by
    rw [hGu]
    calc
      _ <= Finset.univ.sum (fun d : D => abs (G i d.val)) := Finset.abs_sum_le_sum_abs _ _
      _ <= Finset.univ.sum (fun _d : D => 2 * p * q) :=
        Finset.sum_le_sum (fun d _ => hG i d.val)
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hDCard]; ring
  have hQuad : abs (dotProduct u (G.mulVec u)) <= 8 * r ^ 2 * p * q := by
    rw [hamiltonian_deleted_indicator_dot_sum]
    calc
      _ <= Finset.univ.sum (fun d : D => abs (G.mulVec u d.val)) := Finset.abs_sum_le_sum_abs _ _
      _ <= Finset.univ.sum (fun _d : D => 4 * r * p * q) :=
        Finset.sum_le_sum (fun d _ => hGuBudget d.val)
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hDCard]; ring
  have hLinear : abs (dotProduct v u) <= 38 * r * p ^ 2 * q := by
    rw [dotProduct_comm, hamiltonian_deleted_indicator_dot_sum]
    calc
      _ <= Finset.univ.sum (fun d : D => abs (v d.val)) := Finset.abs_sum_le_sum_abs _ _
      _ <= Finset.univ.sum (fun _d : D => 19 * p ^ 2 * q) :=
        Finset.sum_le_sum (fun d _ => hV d.val)
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hDCard]; ring
  have hRank : abs (r * (r - 1) * q) <= r * (r + 1) * q := by
    have h := norm_sub_le r (1 : Real)
    simp only [Real.norm_eq_abs, abs_of_nonneg hr0, abs_one] at h
    rw [abs_mul, abs_mul, abs_of_nonneg hr0, abs_of_nonneg hq0]
    have hMul := mul_le_mul_of_nonneg_left h hr0
    exact mul_le_mul_of_nonneg_right hMul hq0
  have hRP2 := mul_le_mul_of_nonneg_left hPQ (mul_nonneg (by norm_num : (0 : Real) <= 8) (sq_nonneg r))
  have hP2 : 1 <= p ^ 2 := by nlinarith only [hp]
  have hRankP := mul_le_mul_of_nonneg_left hP2
    (mul_nonneg (mul_nonneg hr0 (by linarith only [hr0] : 0 <= r + 1)) hq0)
  have hRest0 : 0 <= (91 * r ^ 2 + 123 * r + 100) * (p ^ 2 * q) :=
    mul_nonneg (by nlinarith only [hr0, sq_nonneg r]) hP2Q0
  change abs (r * (r - 1) * q + dotProduct u (G.mulVec u) + 2 * dotProduct v u) <= _
  calc
    _ <= abs (r * (r - 1) * q) + abs (dotProduct u (G.mulVec u)) +
        2 * abs (dotProduct v u) := by
      have h1 := abs_add_le (r * (r - 1) * q + dotProduct u (G.mulVec u)) (2 * dotProduct v u)
      have h2 := abs_add_le (r * (r - 1) * q) (dotProduct u (G.mulVec u))
      simp only [abs_mul, show abs (2 : Real) = 2 by norm_num] at h1
      linarith only [h1, h2]
    _ <= r * (r + 1) * q + 8 * r ^ 2 * p * q + 76 * r * p ^ 2 * q := by
      nlinarith only [hRank, hQuad, hLinear]
    _ <= 100 * (1 + r) ^ 2 * p ^ 2 * q := by
      nlinarith only [hRP2, hRankP, hRest0]

end PrimeFactorOscillations

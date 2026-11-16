/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianSchurBudget

/-! # Positive doubly stochastic completion of a nearly stochastic matrix

This is an auxiliary inverse reference. The final scaling acts on the
original matrix; the rank-one completion is never used as a support claim.
All defects and their common total are retained exactly.
-/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations

variable {Iota : Type*} [Fintype Iota] [DecidableEq Iota]

def hamiltonianRowDeficit (T : Matrix Iota Iota Real) (c : Real) (i : Iota) : Real :=
  c - Finset.univ.sum (fun j => T i j)

def hamiltonianColumnDeficit (T : Matrix Iota Iota Real) (c : Real) (j : Iota) : Real :=
  c - Finset.univ.sum (fun i => T i j)

def hamiltonianDeficitMass (T : Matrix Iota Iota Real) (c : Real) : Real :=
  Finset.univ.sum (hamiltonianRowDeficit T c)

def hamiltonianStochasticCompletion (T : Matrix Iota Iota Real) (c : Real) :
    Matrix Iota Iota Real :=
  fun i j => T i j / c +
    hamiltonianRowDeficit T c i * hamiltonianColumnDeficit T c j /
      (c * hamiltonianDeficitMass T c)

theorem hamiltonian_deficit_mass_balance (T : Matrix Iota Iota Real) (c : Real) :
    Finset.univ.sum (hamiltonianColumnDeficit T c) = hamiltonianDeficitMass T c := by
  unfold hamiltonianDeficitMass hamiltonianRowDeficit hamiltonianColumnDeficit
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_comm]

theorem hamiltonian_stochastic_completion_row (T : Matrix Iota Iota Real) (c : Real)
    (hc : Not (c = 0)) (hMass : Not (hamiltonianDeficitMass T c = 0)) (i : Iota) :
    Finset.univ.sum (fun j => hamiltonianStochasticCompletion T c i j) = 1 := by
  unfold hamiltonianStochasticCompletion
  rw [Finset.sum_add_distrib, <- Finset.sum_div, <- Finset.sum_div,
    <- Finset.mul_sum, hamiltonian_deficit_mass_balance]
  unfold hamiltonianRowDeficit
  field_simp
  ring

theorem hamiltonian_stochastic_completion_col (T : Matrix Iota Iota Real) (c : Real)
    (hc : Not (c = 0)) (hMass : Not (hamiltonianDeficitMass T c = 0)) (j : Iota) :
    Finset.univ.sum (fun i => hamiltonianStochasticCompletion T c i j) = 1 := by
  unfold hamiltonianStochasticCompletion
  rw [Finset.sum_add_distrib, <- Finset.sum_div, <- Finset.sum_div,
    <- Finset.sum_mul]
  change Finset.univ.sum (fun i => T i j) / c +
    hamiltonianDeficitMass T c * hamiltonianColumnDeficit T c j /
      (c * hamiltonianDeficitMass T c) = 1
  unfold hamiltonianColumnDeficit
  field_simp
  ring

theorem hamiltonian_stochastic_completion_nonnegative (T : Matrix Iota Iota Real) (c : Real)
    (hc : 0 <= c) (hMass : 0 <= hamiltonianDeficitMass T c)
    (hT : forall i j, 0 <= T i j)
    (hRow : forall i, 0 <= hamiltonianRowDeficit T c i)
    (hCol : forall j, 0 <= hamiltonianColumnDeficit T c j)
    (i j : Iota) :
    0 <= hamiltonianStochasticCompletion T c i j := by
  exact add_nonneg (div_nonneg (hT i j) hc)
    (div_nonneg (mul_nonneg (hRow i) (hCol j)) (mul_nonneg hc hMass))

theorem hamiltonian_completion_deficit_bounds (T : Matrix Iota Iota Real) (eps : Real)
    (hRow : forall i, abs (Finset.univ.sum (fun j => T i j) - 1) <= eps)
    (hCol : forall j, abs (Finset.univ.sum (fun i => T i j) - 1) <= eps) :
    (forall i, And (eps <= hamiltonianRowDeficit T (1 + 2 * eps) i)
      (hamiltonianRowDeficit T (1 + 2 * eps) i <= 3 * eps)) /\
    (forall j, And (eps <= hamiltonianColumnDeficit T (1 + 2 * eps) j)
      (hamiltonianColumnDeficit T (1 + 2 * eps) j <= 3 * eps)) := by
  constructor
  . intro i
    have h := abs_le.mp (hRow i)
    unfold hamiltonianRowDeficit
    constructor <;> linarith only [h.1, h.2]
  . intro j
    have h := abs_le.mp (hCol j)
    unfold hamiltonianColumnDeficit
    constructor <;> linarith only [h.1, h.2]

variable [Nonempty Iota]

theorem hamiltonian_completion_mass_bounds (T : Matrix Iota Iota Real) (eps : Real)
    (hRow : forall i, abs (Finset.univ.sum (fun j => T i j) - 1) <= eps) :
    (Fintype.card Iota : Real) * eps <= hamiltonianDeficitMass T (1 + 2 * eps) := by
  calc
    _ = Finset.univ.sum (fun _ : Iota => eps) := by simp
    _ <= _ := by
      apply Finset.sum_le_sum
      intro i hi
      have h := (abs_le.mp (hRow i)).2
      change eps <= 1 + 2 * eps - Finset.univ.sum (fun j => T i j)
      linarith only [h]

theorem hamiltonian_positive_stochastic_completion (T : Matrix Iota Iota Real) (eps : Real)
    (hEps : 0 < eps)
    (hT : forall i j, 0 <= T i j)
    (hRow : forall i, abs (Finset.univ.sum (fun j => T i j) - 1) <= eps)
    (hCol : forall j, abs (Finset.univ.sum (fun i => T i j) - 1) <= eps) :
    let U := hamiltonianStochasticCompletion T (1 + 2 * eps)
    (forall i j, 0 <= U i j) /\
      (forall i, Finset.univ.sum (fun j => U i j) = 1) /\
      (forall j, Finset.univ.sum (fun i => U i j) = 1) := by
  have hc : 0 < 1 + 2 * eps := by linarith only [hEps]
  have hMass : 0 < hamiltonianDeficitMass T (1 + 2 * eps) := by
    have hCard : 0 < (Fintype.card Iota : Real) := Nat.cast_pos.mpr Fintype.card_pos
    exact (mul_pos hCard hEps).trans_le (hamiltonian_completion_mass_bounds T eps hRow)
  have hDef := hamiltonian_completion_deficit_bounds T eps hRow hCol
  exact And.intro
    (hamiltonian_stochastic_completion_nonnegative T _ hc.le hMass.le hT
      (fun i => hEps.le.trans (hDef.1 i).1) (fun j => hEps.le.trans (hDef.2 j).1))
    (And.intro
      (hamiltonian_stochastic_completion_row T _ (ne_of_gt hc) (ne_of_gt hMass))
      (hamiltonian_stochastic_completion_col T _ (ne_of_gt hc) (ne_of_gt hMass)))


theorem hamiltonian_stochastic_completion_transpose (T : Matrix Iota Iota Real) (c : Real) :
    (hamiltonianStochasticCompletion T c).transpose =
      hamiltonianStochasticCompletion T.transpose c := by
  have hMass : hamiltonianDeficitMass T.transpose c = hamiltonianDeficitMass T c := by
    change Finset.univ.sum (hamiltonianColumnDeficit T c) = _
    exact hamiltonian_deficit_mass_balance T c
  ext i j
  simp only [hamiltonianStochasticCompletion, Matrix.transpose_apply, hMass]
  unfold hamiltonianRowDeficit hamiltonianColumnDeficit
  simp only [Matrix.transpose_apply]
  ring

theorem hamiltonian_stochastic_completion_entry_bound
    (T : Matrix Iota Iota Real) (eps A : Real)
    (hEps : 0 < eps)
    (hRow : forall i, abs (Finset.univ.sum (fun j => T i j) - 1) <= eps)
    (hCol : forall j, abs (Finset.univ.sum (fun i => T i j) - 1) <= eps)
    (hUpper : forall i j, T i j <= A / (Fintype.card Iota : Real))
    (i j : Iota) :
    hamiltonianStochasticCompletion T (1 + 2 * eps) i j <=
      (A + 9 * eps) / ((1 + 2 * eps) * (Fintype.card Iota : Real)) := by
  let c := 1 + 2 * eps
  let m : Real := Fintype.card Iota
  let tau := hamiltonianDeficitMass T c
  have hc : 0 < c := by dsimp only [c]; linarith only [hEps]
  have hm : 0 < m := Nat.cast_pos.mpr Fintype.card_pos
  have hDef := hamiltonian_completion_deficit_bounds T eps hRow hCol
  have hTauLower : m * eps <= tau := hamiltonian_completion_mass_bounds T eps hRow
  have hTau : 0 < tau := (mul_pos hm hEps).trans_le hTauLower
  have hNumerator : hamiltonianRowDeficit T c i * hamiltonianColumnDeficit T c j <=
      (3 * eps) * (3 * eps) :=
    mul_le_mul (hDef.1 i).2 (hDef.2 j).2
      (hEps.le.trans (hDef.2 j).1) (by positivity)
  have hFill : hamiltonianRowDeficit T c i * hamiltonianColumnDeficit T c j / tau <=
      9 * eps / m := by
    calc
      _ <= ((3 * eps) * (3 * eps)) / tau :=
        div_le_div_of_nonneg_right hNumerator hTau.le
      _ <= ((3 * eps) * (3 * eps)) / (m * eps) :=
        div_le_div_of_nonneg_left (by positivity) (mul_pos hm hEps) hTauLower
      _ = _ := by field_simp; ring
  have hCompare := div_le_div_of_nonneg_right
    (add_le_add (hUpper i j) hFill) hc.le
  change hamiltonianStochasticCompletion T c i j <= (A + 9 * eps) / (c * m)
  calc
    _ = (T i j +
        hamiltonianRowDeficit T c i * hamiltonianColumnDeficit T c j / tau) / c := by
      unfold hamiltonianStochasticCompletion
      dsimp only [tau]
      ring
    _ <= (A / m + 9 * eps / m) / c := hCompare
    _ = _ := by ring

theorem hamiltonian_stochastic_completion_row_error
    (T : Matrix Iota Iota Real) (eps : Real)
    (hEps : 0 < eps) (hEpsSmall : eps <= 1 / 2)
    (hT : forall i j, 0 <= T i j)
    (hRow : forall i, abs (Finset.univ.sum (fun j => T i j) - 1) <= eps)
    (hCol : forall j, abs (Finset.univ.sum (fun i => T i j) - 1) <= eps)
    (i : Iota) :
    Finset.univ.sum (fun j => abs
      (T i j - hamiltonianStochasticCompletion T (1 + 2 * eps) i j)) <= 6 * eps := by
  let c := 1 + 2 * eps
  let tau := hamiltonianDeficitMass T c
  let dr := hamiltonianRowDeficit T c i
  have hc : 0 < c := by dsimp only [c]; linarith only [hEps]
  have hc1 : 1 <= c := by dsimp only [c]; linarith only [hEps]
  have hDef := hamiltonian_completion_deficit_bounds T eps hRow hCol
  have hDr : 0 <= dr := hEps.le.trans (hDef.1 i).1
  have hTau : 0 < tau := by
    have hCard : 0 < (Fintype.card Iota : Real) := Nat.cast_pos.mpr Fintype.card_pos
    exact (mul_pos hCard hEps).trans_le (hamiltonian_completion_mass_bounds T eps hRow)
  have hPoint (j : Iota) :
      abs (T i j - hamiltonianStochasticCompletion T c i j) <=
        (2 * eps / c) * T i j + dr * hamiltonianColumnDeficit T c j / (c * tau) := by
    have hId : T i j - hamiltonianStochasticCompletion T c i j =
        (2 * eps / c) * T i j - dr * hamiltonianColumnDeficit T c j / (c * tau) := by
      unfold hamiltonianStochasticCompletion
      dsimp only [dr, tau]
      field_simp
      dsimp only [c]
      ring
    rw [hId]
    have hFirst : 0 <= (2 * eps / c) * T i j :=
      mul_nonneg (div_nonneg (by positivity) hc.le) (hT i j)
    have hSecond : 0 <= dr * hamiltonianColumnDeficit T c j / (c * tau) :=
      div_nonneg (mul_nonneg hDr (hEps.le.trans (hDef.2 j).1)) (mul_pos hc hTau).le
    simpa only [Real.norm_eq_abs, abs_of_nonneg hFirst, abs_of_nonneg hSecond] using
      norm_sub_le ((2 * eps / c) * T i j)
        (dr * hamiltonianColumnDeficit T c j / (c * tau))
  have hFill : Finset.univ.sum
      (fun j => dr * hamiltonianColumnDeficit T c j / (c * tau)) = dr / c := by
    rw [<- Finset.sum_div, <- Finset.mul_sum, hamiltonian_deficit_mass_balance]
    change dr * tau / (c * tau) = dr / c
    field_simp
  have hFirstScale : 2 * eps / c <= 2 * eps := by
    simpa only [div_one] using div_le_div_of_nonneg_left (by positivity : 0 <= 2 * eps)
      zero_lt_one hc1
  have hDrScale : dr / c <= dr := by
    simpa only [div_one] using div_le_div_of_nonneg_left hDr zero_lt_one hc1
  have hDegree : 0 <= Finset.univ.sum (fun j => T i j) :=
    Finset.sum_nonneg (fun j _ => hT i j)
  have hFirst : (2 * eps / c) * Finset.univ.sum (fun j => T i j) <=
      2 * eps * (1 + eps) :=
    mul_le_mul hFirstScale (by linarith only [(abs_le.mp (hRow i)).2]) hDegree (by positivity)
  calc
    _ <= Finset.univ.sum (fun j =>
        (2 * eps / c) * T i j + dr * hamiltonianColumnDeficit T c j / (c * tau)) :=
      Finset.sum_le_sum (fun j _ => hPoint j)
    _ = (2 * eps / c) * Finset.univ.sum (fun j => T i j) + dr / c := by
      rw [Finset.sum_add_distrib, <- Finset.mul_sum, hFill]
    _ <= 2 * eps * (1 + eps) + 3 * eps :=
      add_le_add hFirst (hDrScale.trans (hDef.1 i).2)
    _ <= 6 * eps := by nlinarith only [hEps, hEpsSmall]

theorem hamiltonian_stochastic_completion_col_error
    (T : Matrix Iota Iota Real) (eps : Real)
    (hEps : 0 < eps) (hEpsSmall : eps <= 1 / 2)
    (hT : forall i j, 0 <= T i j)
    (hRow : forall i, abs (Finset.univ.sum (fun j => T i j) - 1) <= eps)
    (hCol : forall j, abs (Finset.univ.sum (fun i => T i j) - 1) <= eps)
    (j : Iota) :
    Finset.univ.sum (fun i => abs
      (T i j - hamiltonianStochasticCompletion T (1 + 2 * eps) i j)) <= 6 * eps := by
  have h := hamiltonian_stochastic_completion_row_error T.transpose eps hEps hEpsSmall
    (fun i j => hT j i) hCol hRow j
  rw [<- hamiltonian_stochastic_completion_transpose] at h
  exact h


theorem hamiltonian_stochastic_completion_operator_error
    (T : Matrix Iota Iota Real) (eps : Real)
    (hEps : 0 < eps) (hEpsSmall : eps <= 1 / 2)
    (hT : forall i j, 0 <= T i j)
    (hRow : forall i, abs (Finset.univ.sum (fun j => T i j) - 1) <= eps)
    (hCol : forall j, abs (Finset.univ.sum (fun i => T i j) - 1) <= eps) :
    norm (T - hamiltonianStochasticCompletion T (1 + 2 * eps)) <= 6 * eps := by
  apply hamiltonian_l2_row_column_budget _ (6 * eps) (by positivity)
  . intro i
    simpa only [Matrix.sub_apply, Real.norm_eq_abs] using
      hamiltonian_stochastic_completion_row_error T eps hEps hEpsSmall hT hRow hCol i
  . intro j
    simpa only [Matrix.sub_apply, Real.norm_eq_abs] using
      hamiltonian_stochastic_completion_col_error T eps hEps hEpsSmall hT hRow hCol j

theorem hamiltonian_stochastic_completion_centered_gap
    (T : Matrix Iota Iota Real) (eps q rho : Real)
    (hEps : 0 < eps) (hEpsSmall : eps <= 1 / 2)
    (hT : forall i j, 0 <= T i j)
    (hRow : forall i, abs (Finset.univ.sum (fun j => T i j) - 1) <= eps)
    (hCol : forall j, abs (Finset.univ.sum (fun i => T i j) - 1) <= eps)
    (hNorm : norm (centeredKernel T q) <= rho) :
    norm (centeredKernel (hamiltonianStochasticCompletion T (1 + 2 * eps)) q) <=
      rho + 6 * eps := by
  have hError := hamiltonian_stochastic_completion_operator_error T eps hEps hEpsSmall hT hRow hCol
  have hId : centeredKernel (hamiltonianStochasticCompletion T (1 + 2 * eps)) q =
      centeredKernel T q -
        (T - hamiltonianStochasticCompletion T (1 + 2 * eps)) := by
    unfold centeredKernel
    abel
  rw [hId]
  exact (norm_sub_le _ _).trans (add_le_add hNorm hError)

end PrimeFactorOscillations

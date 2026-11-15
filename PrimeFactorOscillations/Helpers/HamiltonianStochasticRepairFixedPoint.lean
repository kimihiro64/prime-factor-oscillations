/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianNonlinearRepair
import PrimeFactorOscillations.Helpers.HamiltonianStochasticRepairBudgets

/-! # The nonlinear fixed point for every actual deleted stochastic block

All contraction budgets are discharged from stochasticity, the entry
bound and the centered spectral gap. The conclusion retains the actual
Schur kernel and the full nonlinear compensation. The parity residual
is removed by the separate exact boundary/conservation consumer.
-/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations

variable {Iota : Type*} [Fintype Iota] [DecidableEq Iota] [Nonempty Iota]

theorem stochastic_deleted_support_fixed_point
    (T : Matrix Iota Iota Real) (S U : Finset Iota) (hCard : S.card = U.card)
    (q a rho : Real) (hq : (Fintype.card Iota : Real) * q = 1) (ha : 1 <= a)
    (hRow : forall i, Finset.sum Finset.univ (fun j => T i j) = 1)
    (hCol : forall j, Finset.sum Finset.univ (fun i => T i j) = 1)
    (hNonneg : forall i j, 0 <= T i j) (hUpper : forall i j, T i j <= a * q)
    (hNorm : norm (centeredKernel T q) <= rho) (hRho : rho < 1)
    (hSmall : (U.card : Real) * a ^ 2 * q / (1 - rho) ^ 2 <= 1 / 1000) :
    let D := S.disjSum U
    let R : Finset (Sum Iota Iota) := Compl.compl D
    let K := hamiltonianRepairKernel T q
    let G := hamiltonianBoundaryKernel K D
    let ell := hamiltonianDeletedSupportDefect T S U
    let PR := (bipartiteLift T).submatrix (fun i : R => i.val) (fun i : R => i.val)
    exists z : R -> Real,
      norm z <= 20 * (U.card : Real) * a * q / (1 - rho) /\
      hamiltonianNonlinearRepairMap PR G (fun i : R => ell i.val) z = z /\
      norm (z - (fun i : R => K.mulVec ell i.val)) <=
        5000 * (U.card : Real) ^ 2 * a ^ 3 * q ^ 2 / (1 - rho) ^ 3 := by
  let delta := 1 - rho
  let r : Real := U.card
  let p := a / delta
  let t := r * p * q
  let D := S.disjSum U
  let R : Finset (Sum Iota Iota) := Compl.compl D
  let K := hamiltonianRepairKernel T q
  let G := hamiltonianBoundaryKernel K D
  let ell := hamiltonianDeletedSupportDefect T S U
  let ellR := fun i : R => ell i.val
  let PR := (bipartiteLift T).submatrix (fun i : R => i.val) (fun i : R => i.val)
  have hBudgets := stochastic_boundary_repair_budgets T S U hCard q a rho hq ha
    hRow hCol hNonneg hUpper hNorm hRho hSmall
  change (forall i : R, Finset.sum Finset.univ (fun j => abs (G i j)) <= 10 * p) /\
    norm ellR <= t /\ norm (G.mulVec ellR) <= 10 * t /\
      norm (G.mulVec ellR - (fun i : R => K.mulVec ell i.val)) <= 136 * t ^ 2 at hBudgets
  have hDelta : 0 < delta := sub_pos.mpr hRho
  have hDen : Not (delta = 0) := ne_of_gt hDelta
  have hRho0 : 0 <= rho := le_trans (norm_nonneg _) hNorm
  have hDelta1 : delta <= 1 := by dsimp only [delta]; linarith only [hRho0]
  have ha0 : 0 <= a := le_trans (by norm_num) ha
  have hN : 0 < (Fintype.card Iota : Real) := Nat.cast_pos.mpr Fintype.card_pos
  have hq0 : 0 <= q := by nlinarith only [hq, hN]
  have hp0 : 0 <= p := div_nonneg ha0 (le_of_lt hDelta)
  have hpClear : delta * p = a := by dsimp only [p]; field_simp
  have hp : 1 <= p := by nlinarith only [hpClear, hDelta1, hp0, ha]
  have ht : 0 <= t := by dsimp only [t, r]; positivity
  have hPt : p * t <= 1 / 1000 := by
    have hEq : p * t = r * a ^ 2 * q / delta ^ 2 := by
      dsimp only [t, p]
      field_simp <;> ring
    rw [hEq]
    exact hSmall
  have hPN (i j : Sum Iota Iota) : 0 <= bipartiteLift T i j := by
    cases i <;> cases j <;>
      simp [bipartiteLift, Matrix.fromBlocks, Matrix.transpose_apply, hNonneg]
  have hPRowAll (i : Sum Iota Iota) :
      Finset.sum Finset.univ (fun j => abs (bipartiteLift T i j)) = 1 := by
    have hAbs (j : Sum Iota Iota) : abs (bipartiteLift T i j) = bipartiteLift T i j :=
      abs_of_nonneg (hPN i j)
    simp only [hAbs]
    cases i with
    | inl i =>
      simpa [bipartiteLift, Matrix.fromBlocks, Fintype.sum_sum_type] using hRow i
    | inr j =>
      simpa [bipartiteLift, Matrix.fromBlocks, Matrix.transpose_apply,
        Fintype.sum_sum_type] using hCol j
  have hPRow (i : R) : Finset.sum Finset.univ (fun j => abs (PR i j)) <= 1 := by
    have h := hamiltonian_retained_sum_le (fun j => abs (bipartiteLift T i.val j)) D
      (fun _ => abs_nonneg _)
    rw [hPRowAll i.val] at h
    exact h
  have hBall : 10 * t + (10 * p) * (t * (20 * t) + (20 * t) ^ 2) <= 20 * t := by
    have hSave := mul_le_mul_of_nonneg_right hPt (mul_nonneg (by norm_num : 0 <= (4200 : Real)) ht)
    nlinarith only [hSave, ht]
  have hLip : (10 * p) * (t + 2 * (20 * t)) <= 1 / 2 := by
    nlinarith only [hPt]
  have hFix := hamiltonian_nonlinear_repair_fixed_point PR G ellR
    (10 * p) t (20 * t) (10 * t) (by positivity) ht (by positivity)
    hPRow hBudgets.1 hBudgets.2.1 hBudgets.2.2.1 hBall hLip
  let z := Classical.choose hFix
  have hz := Classical.choose_spec hFix
  have hRad : 20 * t = 20 * r * a * q / (1 - rho) := by
    dsimp only [t, p, delta]
    ring
  have hRaw : 5000 * p * t ^ 2 =
      5000 * r ^ 2 * a ^ 3 * q ^ 2 / (1 - rho) ^ 3 := by
    change 5000 * p * t ^ 2 = 5000 * r ^ 2 * a ^ 3 * q ^ 2 / delta ^ 3
    dsimp only [p, t]
    field_simp <;> ring
  have hCompare : norm (z - (fun i : R => K.mulVec ell i.val)) <= 5000 * p * t ^ 2 := by
    have hTriangle : norm (z - (fun i : R => K.mulVec ell i.val)) <=
        norm (z - G.mulVec ellR) +
          norm (G.mulVec ellR - (fun i : R => K.mulVec ell i.val)) := by
      calc
        _ = norm ((z - G.mulVec ellR) +
            (G.mulVec ellR - (fun i : R => K.mulVec ell i.val))) := by
          congr 1
          abel
        _ <= _ := norm_add_le _ _
    have hFloor := mul_le_mul_of_nonneg_right hp (sq_nonneg t)
    have hZ := hz.2.2
    have hE := hBudgets.2.2.2
    nlinarith only [hTriangle, hZ, hE, hFloor, sq_nonneg t]
  refine Exists.intro z (And.intro ?_ (And.intro hz.2.1 ?_))
  case refine_1 => exact le_trans hz.1 (le_of_eq hRad)
  case refine_2 => exact le_trans hCompare (le_of_eq hRaw)

end PrimeFactorOscillations

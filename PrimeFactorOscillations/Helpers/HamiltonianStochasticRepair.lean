/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianRetainedScalingConservation
import PrimeFactorOscillations.Helpers.HamiltonianScalingResidualEquation
import PrimeFactorOscillations.Helpers.HamiltonianStochasticRepairFixedPoint

/-! # Full positive stochastic repair with a two-power local expansion

The fixed point is upgraded to every physical scaling equation using
the exact Schur parity residual and full signed conservation. All four
bounds and the compensation are discharged for the actual matrix.
-/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations

variable {Iota : Type*} [Fintype Iota] [DecidableEq Iota] [Nonempty Iota]

theorem stochastic_deleted_support_repair_exists
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
    let ell := hamiltonianDeletedSupportDefect T S U
    let PR := (bipartiteLift T).submatrix (fun i : R => i.val) (fun i : R => i.val)
    exists z : R -> Real,
      norm z <= 20 * (U.card : Real) * a * q / (1 - rho) /\
      norm (z - (fun i : R => K.mulVec ell i.val)) <=
        5000 * (U.card : Real) ^ 2 * a ^ 3 * q ^ 2 / (1 - rho) ^ 3 /\
      (forall i : R, 0 < 1 + z i) /\
      forall i : R, (1 + z i) * PR.mulVec (1 + z) i = 1 := by
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
  have hFix := stochastic_deleted_support_fixed_point T S U hCard q a rho hq ha
    hRow hCol hNonneg hUpper hNorm hRho hSmall
  let z := Classical.choose hFix
  have hz := Classical.choose_spec hFix
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
      dsimp only [t, p]
      field_simp <;> ring
    rw [hEq]
    exact hSmall
  have htSmall : t <= 1 / 1000 := by
    have htu : t <= p * t := by nlinarith only [hp, ht]
    exact le_trans htu hPt
  have hAr : r * a * q = delta * t := by
    calc
      _ = r * (delta * p) * q := by rw [hpClear]
      _ = _ := by dsimp only [t]; ring
  have hDCard : (D.card : Real) = 2 * r := by
    simp only [D, Finset.card_disjSum, hCard, Nat.cast_add, r]
    ring
  have hSmallD : (D.card : Real) * (4 * a * q) <= (1 - rho) / 2 := by
    rw [hDCard]
    have hScaled := mul_le_mul_of_nonneg_left htSmall (le_of_lt hDelta)
    change 2 * r * (4 * a * q) <= delta / 2
    nlinarith only [hAr, hScaled, hDelta]
  have hFullCardQ : (Fintype.card (Sum Iota Iota) : Real) * q = 2 := by
    simp only [Fintype.card_sum, Nat.cast_add]
    nlinarith only [hq]
  have hCardPart :
      (Fintype.card (Sum Iota Iota) : Real) = (D.card : Real) + (R.card : Real) := by
    have h := hamiltonian_sum_support_partition (fun _ : Sum Iota Iota => (1 : Real)) D
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul,
      mul_one] using h
  rw [hDCard] at hCardPart
  have hPartQ := congrArg (fun v : Real => v * q) hCardPart
  have hrq : r * q <= 1 / 1000 := by
    have hMul := mul_le_mul_of_nonneg_right hp (mul_nonneg hr hq0)
    have hLe : r * q <= t := by dsimp only [t]; nlinarith only [hMul]
    exact le_trans hLe htSmall
  have hPositive : 0 < R.card := by
    have hReal : 0 < (R.card : Real) := by
      by_contra h
      have hMul := mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt h) hq0
      nlinarith only [hPartQ, hFullCardQ, hrq, hMul]
    exact Nat.cast_pos.mp hReal
  have hRadius : 20 * r * a * q / (1 - rho) = 20 * t := by
    dsimp only [t, p, delta]
    ring
  have hZSmall : norm z <= 1 / 50 := by
    have hZ := hz.1
    change norm z <= 20 * r * a * q / (1 - rho) at hZ
    rw [hRadius] at hZ
    nlinarith only [hZ, htSmall]
  have hPos (i : R) : 0 < 1 + z i := by
    have hPoint := (pi_norm_le_iff_of_nonneg (by norm_num : 0 <= (1 / 50 : Real))).mp hZSmall i
    rw [Real.norm_eq_abs] at hPoint
    have hLower := (abs_le.mp hPoint).1
    linarith only [hLower]
  let w := ellR + hamiltonianRepairNonlinear PR ellR z
  have hMap : G.mulVec w = z := hz.2.1
  have hResponse := stochastic_boundary_inverse_residual T D q a rho hq ha
    hRow hCol hNonneg hUpper hNorm hRho hSmallD w
  let c := Classical.choose hResponse
  have hc := Classical.choose_spec hResponse
  have hH : (((1 : Matrix (Sum Iota Iota) (Sum Iota Iota) Real) + bipartiteLift T).submatrix
      (fun i : R => i.val) (fun i : R => i.val)) = 1 + PR := by
    apply Matrix.ext
    intro i j
    change (1 : Matrix (Sum Iota Iota) (Sum Iota Iota) Real) i.val j.val +
        bipartiteLift T i.val j.val =
      (1 : Matrix R R Real) i j + bipartiteLift T i.val j.val
    simp only [Matrix.one_apply, Subtype.ext_iff]
  change forall i : R, (((1 : Matrix (Sum Iota Iota) (Sum Iota Iota) Real) +
    bipartiteLift T).submatrix (fun i : R => i.val) (fun i : R => i.val)).mulVec
      (G.mulVec w) i = w i - hamiltonianParitySign i.val * c at hc
  rw [hMap, hH] at hc
  have hDegree (i : R) : PR.mulVec 1 i = 1 - ellR i :=
    hamiltonian_retained_row_defect T S U hRow hCol i
  have hResidual (i : R) :
      (1 + z i) * PR.mulVec (1 + z) i - 1 = hamiltonianParitySign i.val * (-c) := by
    calc
      _ = ((1 : Matrix R R Real) + PR).mulVec z i - w i :=
        hamiltonian_nonlinear_scaling_residual PR ellR z hDegree i
      _ = (w i - hamiltonianParitySign i.val * c) - w i := by rw [hc i]
      _ = _ := by ring
  have hRows := (hamiltonian_retained_scaling_parity_zero T S U hCard hPositive
    (1 + z) (-c) hResidual).2
  exact Exists.intro z (And.intro hz.1 (And.intro hz.2.2 (And.intro hPos hRows)))

end PrimeFactorOscillations

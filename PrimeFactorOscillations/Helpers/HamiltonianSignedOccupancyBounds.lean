/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianRootOccupancyBounds

/-! # Uniform bounds for the full signed coordinate moments

The actual determinant-root identities are evaluated before taking
coefficient bounds. Both ordered cross products and the full parity
compensation are included, with no unsigned minor-mass factor.
-/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations

variable {Iota : Type*} [Fintype Iota] [DecidableEq Iota] [Nonempty Iota]

theorem stochastic_signed_coordinate_occupancy_bound
    (T : Matrix Iota Iota Real) (q a rho : Real)
    (hq : (Fintype.card Iota : Real) * q = 1) (ha : 1 <= a)
    (hRow : forall i, Finset.univ.sum (fun j => T i j) = 1)
    (hCol : forall j, Finset.univ.sum (fun i => T i j) = 1)
    (hNonneg : forall i j, 0 <= T i j) (hUpper : forall i j, T i j <= a * q)
    (hNorm : norm (centeredKernel T q) <= rho) (hRho : rho < 1) (i : Sum Iota Iota) :
    (1 - rho) * abs (hamiltonianCoordinateMinorMoment (bipartiteLift T) i) <=
      5 * abs (Matrix.det ((1 : Matrix Iota Iota Real) -
        (centeredKernel T q).transpose * centeredKernel T q)) * a * q := by
  let g := 1 - rho
  let G := resolventCovariance (bipartiteLift (centeredKernel T q))
  let A0 := (1 : Matrix (Sum Iota Iota) (Sum Iota Iota) Real) -
    Ring.inverse (hamiltonianParityRegularizedKernel T q 0)
  let d := Matrix.det ((1 : Matrix Iota Iota Real) -
    (centeredKernel T q).transpose * centeredKernel T q)
  have hBounds := stochastic_root_occupancy_coefficient_bounds T q a rho hq ha
    hRow hCol hNonneg hUpper hNorm hRho
  have hg : 0 < g := sub_pos.mpr hRho
  have hg1 : g <= 1 := by
    have hRho0 := le_trans (norm_nonneg _) hNorm
    dsimp only [g]
    linarith only [hRho0]
  have ha0 : 0 <= a := le_trans (by norm_num) ha
  have hCard : 0 < (Fintype.card Iota : Real) := Nat.cast_pos.mpr Fintype.card_pos
  have hq0 : 0 <= q := by nlinarith only [hq, hCard]
  have haq : 0 <= a * q := mul_nonneg ha0 hq0
  have hCoeff : g * abs (3 / 2 + Matrix.trace G) <= 3 / 2 + 4 * a := by
    have hTriangle := mul_le_mul_of_nonneg_left
      (abs_add_le (3 / 2 : Real) (Matrix.trace G)) (le_of_lt hg)
    norm_num only [abs_of_pos (by norm_num : (0 : Real) < 3 / 2)] at hTriangle
    have hTrace : g * abs (Matrix.trace G) <= 4 * a := hBounds.2.2.2
    nlinarith only [hTriangle, hTrace, hg1]
  let S := hamiltonianParityProjection (Iota := Iota) q
  have hPi := hamiltonian_parity_projection_abs_entry q hq0 i i
  have hProduct := mul_le_mul hCoeff hPi (abs_nonneg (S i i))
    (by nlinarith only [ha] : 0 <= (3 / 2 : Real) + 4 * a)
  have hA0 : g * abs (A0 i i) <= (9 / 4 : Real) * a * q := hBounds.2.1 i i
  have hBracket :
      g * abs (A0 i i + (3 / 2 + Matrix.trace G) * S i i) <= 5 * a * q := by
    have hTriangle := mul_le_mul_of_nonneg_left
      (abs_add_le (A0 i i) ((3 / 2 + Matrix.trace G) * S i i)) (le_of_lt hg)
    rw [abs_mul] at hTriangle
    have hqa : q <= a * q := by simpa only [one_mul] using mul_le_mul_of_nonneg_right ha hq0
    nlinarith only [hTriangle, hA0, hProduct, hqa]
  have hMoment := stochastic_coordinate_minor_moment_root T q rho hq hRow hCol hNorm hRho i
  change hamiltonianCoordinateMinorMoment (bipartiteLift T) i =
    d * (A0 i i + (3 / 2 + Matrix.trace G) * S i i) at hMoment
  change g * abs (hamiltonianCoordinateMinorMoment (bipartiteLift T) i) <= 5 * abs d * a * q
  rw [hMoment, abs_mul]
  calc
    _ = abs d * (g * abs (A0 i i + (3 / 2 + Matrix.trace G) * S i i)) := by ring
    _ <= abs d * (5 * a * q) := mul_le_mul_of_nonneg_left hBracket (abs_nonneg d)
    _ = _ := by ring

theorem stochastic_signed_coordinate_pair_occupancy_bound
    (T : Matrix Iota Iota Real) (q a rho : Real)
    (hq : (Fintype.card Iota : Real) * q = 1) (ha : 1 <= a)
    (hRow : forall i, Finset.univ.sum (fun j => T i j) = 1)
    (hCol : forall j, Finset.univ.sum (fun i => T i j) = 1)
    (hNonneg : forall i j, 0 <= T i j) (hUpper : forall i j, T i j <= a * q)
    (hNorm : norm (centeredKernel T q) <= rho) (hRho : rho < 1) (i j : Sum Iota Iota) (hIJ : Not (i = j)) :
    (1 - rho) ^ 2 * abs (hamiltonianCoordinatePairMinorMoment (bipartiteLift T) i j) <=
      50 * abs (Matrix.det ((1 : Matrix Iota Iota Real) -
        (centeredKernel T q).transpose * centeredKernel T q)) * a ^ 2 * q ^ 2 := by
  let g := 1 - rho
  let G := resolventCovariance (bipartiteLift (centeredKernel T q))
  let A0 := (1 : Matrix (Sum Iota Iota) (Sum Iota Iota) Real) -
    Ring.inverse (hamiltonianParityRegularizedKernel T q 0)
  let d := Matrix.det ((1 : Matrix Iota Iota Real) -
    (centeredKernel T q).transpose * centeredKernel T q)
  have hBounds := stochastic_root_occupancy_coefficient_bounds T q a rho hq ha
    hRow hCol hNonneg hUpper hNorm hRho
  have hg : 0 < g := sub_pos.mpr hRho
  have hg1 : g <= 1 := by
    have hRho0 := le_trans (norm_nonneg _) hNorm
    dsimp only [g]
    linarith only [hRho0]
  have ha0 : 0 <= a := le_trans (by norm_num) ha
  have hCard : 0 < (Fintype.card Iota : Real) := Nat.cast_pos.mpr Fintype.card_pos
  have hq0 : 0 <= q := by nlinarith only [hq, hCard]
  have haq : 0 <= a * q := mul_nonneg ha0 hq0
  have hCoeff : g * abs (3 / 2 + Matrix.trace G) <= 3 / 2 + 4 * a := by
    have hTriangle := mul_le_mul_of_nonneg_left
      (abs_add_le (3 / 2 : Real) (Matrix.trace G)) (le_of_lt hg)
    norm_num only [abs_of_pos (by norm_num : (0 : Real) < 3 / 2)] at hTriangle
    have hTrace : g * abs (Matrix.trace G) <= 4 * a := hBounds.2.2.2
    nlinarith only [hTriangle, hTrace, hg1]
  let A1 := (hamiltonianRepairKernel T q) ^ 2 -
    hamiltonianRepairKernel T q + hamiltonianParityProjection q
  let V := A0 i i * A0 j j - A0 i j * A0 j i
  let C0 := hamiltonianParityCrossForm q A0 i j
  let C1 := hamiltonianParityCrossForm q A1 i j
  have hCnonneg : 0 <= (9 / 4 : Real) * a * q := by nlinarith only [haq]
  have hA0 (k l : Sum Iota Iota) :
      g * abs (A0 k l) <= (9 / 4 : Real) * a * q := hBounds.2.1 k l
  have hA1 (k l : Sum Iota Iota) :
      g ^ 2 * abs (A1 k l) <= 4 * a * q := hBounds.2.2.1 k l
  have hV : g ^ 2 * abs V <= (81 / 8 : Real) * a ^ 2 * q ^ 2 := by
    have h := hamiltonian_two_coordinate_determinant_entry_bound A0 g
      ((9 / 4 : Real) * a * q) (le_of_lt hg) hCnonneg hA0 i j
    change g ^ 2 * abs V <= _ at h
    nlinarith only [h]
  have hC0 : g * abs C0 <= (9 / 2 : Real) * a * q ^ 2 := by
    have h := hamiltonian_parity_cross_form_entry_bound A0 q g
      ((9 / 4 : Real) * a * q) hq0 (le_of_lt hg) hCnonneg hA0 i j
    change g * abs C0 <= _ at h
    nlinarith only [h]
  have hC1 : g ^ 2 * abs C1 <= 8 * a * q ^ 2 := by
    have h := hamiltonian_parity_cross_form_entry_bound A1 q (g ^ 2)
      (4 * a * q) hq0 (sq_nonneg g) (by nlinarith only [haq]) hA1 i j
    change g ^ 2 * abs C1 <= _ at h
    nlinarith only [h]
  have hProduct := mul_le_mul hCoeff hC0
    (mul_nonneg (le_of_lt hg) (abs_nonneg C0))
    (by nlinarith only [ha] : 0 <= (3 / 2 : Real) + 4 * a)
  have hAA : a * q ^ 2 <= a ^ 2 * q ^ 2 := by
    have h := mul_le_mul_of_nonneg_left ha ha0
    have hSquare : a <= a ^ 2 := by nlinarith only [h]
    exact mul_le_mul_of_nonneg_right hSquare (sq_nonneg q)
  have hBracket :
      g ^ 2 * abs (V - C1 + (3 / 2 + Matrix.trace G) * C0) <= 50 * a ^ 2 * q ^ 2 := by
    have h1 := mul_le_mul_of_nonneg_left (hamiltonian_abs_sub_bound V C1) (sq_nonneg g)
    have h2 := mul_le_mul_of_nonneg_left
      (abs_add_le (V - C1) ((3 / 2 + Matrix.trace G) * C0)) (sq_nonneg g)
    rw [abs_mul] at h2
    have hNonneg : 0 <= a ^ 2 * q ^ 2 := mul_nonneg (sq_nonneg a) (sq_nonneg q)
    nlinarith only [h1, h2, hV, hC0, hC1, hProduct, hAA, hNonneg]
  have hMoment := stochastic_coordinate_pair_minor_moment_root T q rho hq hRow hCol hNorm hRho i j hIJ
  change hamiltonianCoordinatePairMinorMoment (bipartiteLift T) i j =
    d * (V - C1 + (3 / 2 + Matrix.trace G) * C0) at hMoment
  change g ^ 2 * abs (hamiltonianCoordinatePairMinorMoment (bipartiteLift T) i j) <=
    50 * abs d * a ^ 2 * q ^ 2
  rw [hMoment, abs_mul]
  calc
    _ = abs d * (g ^ 2 * abs (V - C1 + (3 / 2 + Matrix.trace G) * C0)) := by ring
    _ <= abs d * (50 * a ^ 2 * q ^ 2) := mul_le_mul_of_nonneg_left hBracket (abs_nonneg d)
    _ = _ := by ring

end PrimeFactorOscillations

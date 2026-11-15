/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianOccupancyEntryBounds
import PrimeFactorOscillations.Helpers.HamiltonianRootOccupancyMoments

/-! # Uniform coefficients of the actual signed root moments

All coefficient estimates are applied after the exact root formulas.
The squared covariance uses stochastic coordinate energy, and the
constant and parity contributions remain in the derivative bound.
-/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations

variable {Iota : Type*} [Fintype Iota] [DecidableEq Iota] [Nonempty Iota]

theorem hamiltonian_abs_sub_bound (x y : Real) :
    abs (x - y) <= abs x + abs y := by
  simpa only [sub_eq_add_neg, abs_neg] using abs_add_le x (-y)

theorem hamiltonian_parity_projection_abs_entry (q : Real) (hq : 0 <= q)
    (i j : Sum Iota Iota) :
    abs (hamiltonianParityProjection q i j) <= q / 2 := by
  apply abs_le.mpr
  constructor <;> cases i <;> cases j <;>
    dsimp only [hamiltonianParityProjection, hamiltonianParitySign] <;> nlinarith only [hq]

theorem hamiltonian_two_coordinate_determinant_entry_bound
    (H : Matrix Iota Iota Real) (g c : Real) (hg : 0 <= g) (hc : 0 <= c)
    (hEntry : forall i j, g * abs (H i j) <= c) (a b : Iota) :
    g ^ 2 * abs (H a a * H b b - H a b * H b a) <= 2 * c ^ 2 := by
  have hFirst := mul_le_mul (hEntry a a) (hEntry b b)
    (mul_nonneg hg (abs_nonneg _)) hc
  have hSecond := mul_le_mul (hEntry a b) (hEntry b a)
    (mul_nonneg hg (abs_nonneg _)) hc
  have hTriangle := mul_le_mul_of_nonneg_left
    (hamiltonian_abs_sub_bound (H a a * H b b) (H a b * H b a)) (sq_nonneg g)
  rw [abs_mul, abs_mul] at hTriangle
  nlinarith only [hFirst, hSecond, hTriangle]

theorem hamiltonian_parity_cross_form_entry_bound
    (H : Matrix (Sum Iota Iota) (Sum Iota Iota) Real)
    (q g c : Real) (hq : 0 <= q) (hg : 0 <= g) (hc : 0 <= c)
    (hEntry : forall i j, g * abs (H i j) <= c) (a b : Sum Iota Iota) :
    g * abs (hamiltonianParityCrossForm q H a b) <= 2 * q * c := by
  let S := hamiltonianParityProjection (Iota := Iota) q
  have hProduct (i j k l : Sum Iota Iota) :
      g * abs (S i j * H k l) <= q / 2 * c := by
    calc
      _ = abs (S i j) * (g * abs (H k l)) := by rw [abs_mul]; ring
      _ <= _ := mul_le_mul (hamiltonian_parity_projection_abs_entry q hq i j)
        (hEntry k l) (mul_nonneg hg (abs_nonneg _)) (div_nonneg hq (by norm_num))
  have h1 := mul_le_mul_of_nonneg_left
    (abs_add_le (S a a * H b b) (S b b * H a a)) hg
  have h2 := mul_le_mul_of_nonneg_left
    (hamiltonian_abs_sub_bound (S a a * H b b + S b b * H a a) (S a b * H b a)) hg
  have h3 := mul_le_mul_of_nonneg_left
    (hamiltonian_abs_sub_bound (S a a * H b b + S b b * H a a - S a b * H b a)
      (S b a * H a b)) hg
  change g * abs (S a a * H b b + S b b * H a a - S a b * H b a -
    S b a * H a b) <= 2 * q * c
  nlinarith only [h1, h2, h3, hProduct a a b b, hProduct b b a a,
    hProduct a b b a, hProduct b a a b]

theorem stochastic_root_occupancy_coefficient_bounds
    (T : Matrix Iota Iota Real) (q a rho : Real)
    (hq : (Fintype.card Iota : Real) * q = 1) (ha : 1 <= a)
    (hRow : forall i, Finset.univ.sum (fun j => T i j) = 1)
    (hCol : forall j, Finset.univ.sum (fun i => T i j) = 1)
    (hNonneg : forall i j, 0 <= T i j) (hUpper : forall i j, T i j <= a * q)
    (hNorm : norm (centeredKernel T q) <= rho) (hRho : rho < 1) :
    let g := 1 - rho
    let G := resolventCovariance (bipartiteLift (centeredKernel T q))
    let A0 := (1 : Matrix (Sum Iota Iota) (Sum Iota Iota) Real) -
      Ring.inverse (hamiltonianParityRegularizedKernel T q 0)
    let A1 := (hamiltonianRepairKernel T q) ^ 2 -
      hamiltonianRepairKernel T q + hamiltonianParityProjection q
    (forall i j, g * abs (G i j) <= 2 * a * q) /\
    (forall i j, g * abs (A0 i j) <= (9 / 4 : Real) * a * q) /\
    (forall i j, g ^ 2 * abs (A1 i j) <= 4 * a * q) /\
    g * abs (Matrix.trace G) <= 4 * a := by
  let g := 1 - rho
  let G := resolventCovariance (bipartiteLift (centeredKernel T q))
  let A0 := (1 : Matrix (Sum Iota Iota) (Sum Iota Iota) Real) -
    Ring.inverse (hamiltonianParityRegularizedKernel T q 0)
  let A1 := (hamiltonianRepairKernel T q) ^ 2 -
    hamiltonianRepairKernel T q + hamiltonianParityProjection q
  have hg : 0 < g := sub_pos.mpr hRho
  have hRho0 : 0 <= rho := le_trans (norm_nonneg _) hNorm
  have hg1 : g <= 1 := by dsimp only [g]; linarith only [hRho0]
  have ha0 : 0 <= a := le_trans (by norm_num) ha
  have hCard : 0 < (Fintype.card Iota : Real) := Nat.cast_pos.mpr Fintype.card_pos
  have hq0 : 0 <= q := by nlinarith only [hq, hCard]
  have haq : 0 <= a * q := mul_nonneg ha0 hq0
  have hFull : (Fintype.card (Sum Iota Iota) : Real) * q = 2 := by
    simp only [Fintype.card_sum, Nat.cast_add]
    nlinarith only [hq]
  have hG (i j : Sum Iota Iota) : g * abs (G i j) <= 2 * a * q := by
    have h := stochastic_block_covariance_entry_bound T q a rho hq ha
      hRow hCol hNonneg hUpper hRho hNorm i j
    change g * norm (G i j) <= (2 - rho) * (a * q) at h
    rw [Real.norm_eq_abs] at h
    nlinarith only [h, mul_nonneg hRho0 haq]
  have hA0Value : A0 = G + averagingKernel (Iota := Sum Iota Iota) (q / 4) :=
    stochastic_regularized_covariance_value T q rho hq hRow hCol hNorm hRho
  have hA0 (i j : Sum Iota Iota) :
      g * abs (A0 i j) <= (9 / 4 : Real) * a * q := by
    have hAbs : abs (A0 i j) <= abs (G i j) + q / 4 := by
      rw [hA0Value]
      change abs (G i j + q / 4) <= _
      simpa only [abs_of_nonneg (div_nonneg hq0 (by norm_num : (0 : Real) <= 4))] using
        abs_add_le (G i j) (q / 4)
    have h := mul_le_mul_of_nonneg_left hAbs (le_of_lt hg)
    have hqa := mul_le_mul_of_nonneg_right (le_trans hg1 ha) hq0
    nlinarith only [h, hqa, hG i j]
  have hgSq1 : g ^ 2 <= 1 := by nlinarith only [hg, hg1]
  have hqSq : g ^ 2 * q <= a * q :=
    le_trans (mul_le_mul_of_nonneg_right hgSq1 hq0)
      (by simpa only [one_mul] using mul_le_mul_of_nonneg_right ha hq0)
  have hA1Identity : A1 =
      -G + G * G - averagingKernel (Iota := Sum Iota Iota) (q / 8) +
        hamiltonianParityProjection q :=
    stochastic_regularized_covariance_jet_identity T q rho hq hRow hCol hNorm hRho
  have hA1 (i j : Sum Iota Iota) : g ^ 2 * abs (A1 i j) <= 4 * a * q := by
    have hSquare := stochastic_covariance_square_entry T q a rho hq
      hRow hCol hNonneg hUpper hNorm hRho i j
    have hPi := hamiltonian_parity_projection_abs_entry q hq0 i j
    have hAbs : abs (A1 i j) <= abs (G i j) + abs ((G * G) i j) + q / 8 + q / 2 := by
      rw [hA1Identity]
      change abs (-G i j + (G * G) i j - q / 8 + hamiltonianParityProjection q i j) <= _
      have h1 := abs_add_le (-G i j) ((G * G) i j)
      have h2 := hamiltonian_abs_sub_bound (-G i j + (G * G) i j) (q / 8)
      have h3 := abs_add_le (-G i j + (G * G) i j - q / 8)
        (hamiltonianParityProjection q i j)
      rw [abs_neg] at h1
      rw [abs_of_nonneg (div_nonneg hq0 (by norm_num : (0 : Real) <= 8))] at h2
      linarith only [h1, h2, h3, hPi]
    have hScaled := mul_le_mul_of_nonneg_left hAbs (sq_nonneg g)
    have hGscaled : g ^ 2 * abs (G i j) <= 2 * a * q := by
      have h := mul_le_mul_of_nonneg_left (hG i j) (le_of_lt hg)
      have hSmall := mul_le_mul_of_nonneg_right hg1 haq
      nlinarith only [h, hSmall]
    change g ^ 2 * abs ((G * G) i j) <= a * q at hSquare
    nlinarith only [hScaled, hGscaled, hSquare, hqSq, haq]
  have hTrace : g * abs (Matrix.trace G) <= 4 * a := by
    have hAbs : abs (Matrix.trace G) <= Finset.univ.sum (fun i => abs (G i i)) :=
      Finset.abs_sum_le_sum_abs _ _
    calc
      _ <= g * Finset.univ.sum (fun i => abs (G i i)) :=
        mul_le_mul_of_nonneg_left hAbs (le_of_lt hg)
      _ = Finset.univ.sum (fun i => g * abs (G i i)) := Finset.mul_sum _ _ _
      _ <= Finset.univ.sum (fun _ : Sum Iota Iota => 2 * a * q) :=
        Finset.sum_le_sum (fun i _ => hG i i)
      _ = 2 * a * ((Fintype.card (Sum Iota Iota) : Real) * q) := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        ring
      _ = _ := by rw [hFull]; ring
  exact And.intro hG (And.intro hA0 (And.intro hA1 hTrace))

end PrimeFactorOscillations

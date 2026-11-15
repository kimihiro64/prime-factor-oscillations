/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import PrimeFactorOscillations.Helpers.HamiltonianPermanentWindowRemainder

/-! # Quantitative cutoff parameters for the complete signed consumer

The physical scale and Cauchy radius are both 1+delta/16. Explicit gaps
control the same kappa constants and tails appearing in the actual
full-window remainder, without changing its signed low main term.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

def hamiltonianWindowScale (delta : Real) : Real := 1 + delta / 16

theorem hamiltonian_window_scale_bounds (delta : Real)
    (hDelta0 : 0 < delta) (hDelta1 : delta <= 1) :
    And (1 < hamiltonianWindowScale delta) (hamiltonianWindowScale delta <= 17 / 16) := by
  unfold hamiltonianWindowScale
  constructor <;> linarith

theorem hamiltonian_window_coefficient_gap (delta : Real) (_hDelta0 : 0 < delta) :
    7 * delta / 16 <= 1 - hamiltonianWindowScale delta * (1 - delta / 2) := by
  unfold hamiltonianWindowScale
  nlinarith [sq_nonneg delta]

theorem hamiltonian_window_circle_gap (delta : Real) (hDelta0 : 0 < delta) :
    3 * delta / 8 <=
      1 - hamiltonianWindowScale delta * hamiltonianWindowScale delta * (1 - delta / 2) := by
  unfold hamiltonianWindowScale
  nlinarith [sq_nonneg delta, mul_nonneg (sq_nonneg delta) hDelta0.le]

theorem hamiltonian_window_rook_gap (delta : Real) (hDelta0 : 0 < delta) :
    7 * delta / 8 <=
      1 - hamiltonianWindowScale delta * hamiltonianWindowScale delta * (1 - delta) := by
  unfold hamiltonianWindowScale
  nlinarith [sq_nonneg delta, mul_nonneg (sq_nonneg delta) hDelta0.le]

theorem hamiltonian_window_coefficient_kappa_bound (delta a : Real)
    (hDelta0 : 0 < delta) (hDelta1 : delta <= 1) (ha : 0 <= a) :
    2 * hamiltonianWindowScale delta ^ 2 * a /
        (1 - hamiltonianWindowScale delta * (1 - delta / 2)) <=
      6 * a / delta := by
  let b := hamiltonianWindowScale delta
  have hb := hamiltonian_window_scale_bounds delta hDelta0 hDelta1
  have hb0 : 0 <= b := le_trans (by norm_num) hb.1.le
  have hPow := wick_nonnegative_power_le b (17 / 16) hb0 hb.2 2
  have hNum := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hPow (by norm_num : (0 : Real) <= 2)) ha
  have hGap := hamiltonian_window_coefficient_gap delta hDelta0
  have hGapPos : 0 < 1 - b * (1 - delta / 2) :=
    lt_of_lt_of_le (by positivity) hGap
  change 2 * b ^ 2 * a / (1 - b * (1 - delta / 2)) <= _
  calc
    _ <= (2 * (17 / 16 : Real) ^ 2 * a) / (7 * delta / 16) :=
      le_trans (div_le_div_of_nonneg_right hNum hGapPos.le)
        (div_le_div_of_nonneg_left (by positivity) (by positivity) hGap)
    _ = (289 / 56 : Real) * (a / delta) := by field_simp [ne_of_gt hDelta0]; ring
    _ <= 6 * (a / delta) :=
      mul_le_mul_of_nonneg_right (by norm_num) (div_nonneg ha hDelta0.le)
    _ = _ := by ring

theorem hamiltonian_window_circle_kappa_bound (delta a : Real)
    (hDelta0 : 0 < delta) (hDelta1 : delta <= 1) (ha : 0 <= a) :
    2 * (hamiltonianWindowScale delta * hamiltonianWindowScale delta) ^ 2 * a /
        (1 - hamiltonianWindowScale delta * hamiltonianWindowScale delta * (1 - delta / 2)) <=
      8 * a / delta := by
  let b := hamiltonianWindowScale delta
  have hb := hamiltonian_window_scale_bounds delta hDelta0 hDelta1
  have hb0 : 0 <= b := le_trans (by norm_num) hb.1.le
  have hPow := wick_nonnegative_power_le b (17 / 16) hb0 hb.2 4
  have hNum : 2 * (b * b) ^ 2 * a <= 2 * (17 / 16 : Real) ^ 4 * a := by
    have hId : (b * b) ^ 2 = b ^ 4 := by ring
    rw [hId]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hPow (by norm_num : (0 : Real) <= 2)) ha
  have hGap := hamiltonian_window_circle_gap delta hDelta0
  have hGapPos : 0 < 1 - b * b * (1 - delta / 2) :=
    lt_of_lt_of_le (by positivity) hGap
  change 2 * (b * b) ^ 2 * a / (1 - b * b * (1 - delta / 2)) <= _
  calc
    _ <= (2 * (17 / 16 : Real) ^ 4 * a) / (3 * delta / 8) :=
      le_trans (div_le_div_of_nonneg_right hNum hGapPos.le)
        (div_le_div_of_nonneg_left (by positivity) (by positivity) hGap)
    _ = (83521 / 12288 : Real) * (a / delta) := by field_simp [ne_of_gt hDelta0]; ring
    _ <= 8 * (a / delta) :=
      mul_le_mul_of_nonneg_right (by norm_num) (div_nonneg ha hDelta0.le)
    _ = _ := by ring

theorem hamiltonian_window_inverse_gap (delta : Real) (hDelta0 : 0 < delta) :
    1 - Inv.inv (hamiltonianWindowScale delta) = delta / (16 + delta) := by
  have hScale : hamiltonianWindowScale delta = (16 + delta) / 16 := by
    unfold hamiltonianWindowScale
    ring
  rw [hScale, inv_div]
  field_simp [ne_of_gt (show 0 < 16 + delta by linarith)]
  ring

theorem hamiltonian_window_log_lower (delta : Real)
    (hDelta0 : 0 < delta) (hDelta1 : delta <= 1) :
    delta / 17 <= Real.log (hamiltonianWindowScale delta) := by
  have hb := hamiltonian_window_scale_bounds delta hDelta0 hDelta1
  have hLog := Real.one_sub_inv_le_log_of_pos
    (lt_trans (by norm_num : (0 : Real) < 1) hb.1)
  rw [hamiltonian_window_inverse_gap delta hDelta0] at hLog
  have hFraction : delta / 17 <= delta / (16 + delta) :=
    div_le_div_of_nonneg_left hDelta0.le (by linarith) (by linarith)
  exact le_trans hFraction hLog

theorem hamiltonian_window_cauchy_prefactor_bound (delta : Real)
    (hDelta0 : 0 < delta) (hDelta1 : delta <= 1) :
    Inv.inv (1 - Inv.inv (hamiltonianWindowScale delta)) <= 17 / delta := by
  rw [hamiltonian_window_inverse_gap delta hDelta0, inv_div]
  exact div_le_div_of_nonneg_right (by linarith) hDelta0.le


theorem hamiltonian_window_rook_ratio_bound (delta s : Real)
    (hDelta0 : 0 < delta) (hDelta1 : delta <= 1)
    (hs : abs s <= hamiltonianWindowScale delta) :
    2 * abs s * hamiltonianWindowScale delta /
        (1 - abs s * hamiltonianWindowScale delta * (1 - delta)) <= 3 / delta := by
  let b := hamiltonianWindowScale delta
  have hb := hamiltonian_window_scale_bounds delta hDelta0 hDelta1
  have hb0 : 0 <= b := le_trans (by norm_num) hb.1.le
  have hArg : abs s * b <= b * b := mul_le_mul_of_nonneg_right hs hb0
  have hGap : 7 * delta / 8 <= 1 - abs s * b * (1 - delta) := by
    have h := mul_le_mul_of_nonneg_right hArg (sub_nonneg.mpr hDelta1)
    have hG := hamiltonian_window_rook_gap delta hDelta0
    linarith
  have hGapPos : 0 < 1 - abs s * b * (1 - delta) :=
    lt_of_lt_of_le (by positivity) hGap
  have hPow := wick_nonnegative_power_le b (17 / 16) hb0 hb.2 2
  have hNum : 2 * abs s * b <= 2 * (17 / 16 : Real) ^ 2 := by
    have hArg' : abs s * b <= (17 / 16 : Real) ^ 2 := by
      calc
        _ <= b * b := hArg
        _ = b ^ 2 := by ring
        _ <= _ := hPow
    nlinarith only [hArg']
  change 2 * abs s * b / (1 - abs s * b * (1 - delta)) <= _
  calc
    _ <= (2 * (17 / 16 : Real) ^ 2) / (7 * delta / 8) :=
      le_trans (div_le_div_of_nonneg_right hNum hGapPos.le)
        (div_le_div_of_nonneg_left (by positivity) (by positivity) hGap)
    _ = (289 / 112 : Real) / delta := by field_simp [ne_of_gt hDelta0]; ring
    _ <= _ := div_le_div_of_nonneg_right (by norm_num) hDelta0.le

theorem hamiltonian_sqrt_product_bound (x a : Real) (hx : 0 <= x) (ha : 1 <= a) :
    Real.sqrt (x * (a - 1)) <= a * Real.sqrt x := by
  have ha0 : 0 <= a := le_trans (by norm_num) ha
  have hA : Real.sqrt (a - 1) <= a := by
    calc
      _ <= Real.sqrt (a ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
      _ = _ := Real.sqrt_sq ha0
  rw [Real.sqrt_mul hx]
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left hA (Real.sqrt_nonneg x)

theorem hamiltonian_window_exponent_bound (delta s x a : Real)
    (hDelta0 : 0 < delta) (hDelta1 : delta <= 1)
    (hx : 1 <= x) (ha : 1 <= a)
    (hs : abs s <= hamiltonianWindowScale delta) :
    2 * abs s * hamiltonianWindowScale delta /
        (1 - abs s * hamiltonianWindowScale delta * (1 - delta)) *
        Real.sqrt (x * (a - 1)) +
      abs s ^ 2 * hamiltonianWindowScale delta ^ 2 * (a - 1) / 2 <=
        4 * a * Real.sqrt x / delta := by
  let b := hamiltonianWindowScale delta
  have hb := hamiltonian_window_scale_bounds delta hDelta0 hDelta1
  have hb0 : 0 <= b := le_trans (by norm_num) hb.1.le
  have ha0 : 0 <= a := le_trans (by norm_num) ha
  have hAbsPow := wick_nonnegative_power_le (abs s) b (abs_nonneg s) hs 2
  have hBPow := wick_nonnegative_power_le b (17 / 16) hb0 hb.2 4
  have hProduct : abs s ^ 2 * b ^ 2 <= 2 := by
    calc
      _ <= b ^ 2 * b ^ 2 := mul_le_mul_of_nonneg_right hAbsPow (sq_nonneg b)
      _ = b ^ 4 := by ring
      _ <= (17 / 16 : Real) ^ 4 := hBPow
      _ <= _ := by norm_num
  have hQuadratic : abs s ^ 2 * b ^ 2 * (a - 1) / 2 <= a := by
    have h := mul_le_mul_of_nonneg_right hProduct (sub_nonneg.mpr ha)
    nlinarith only [h, ha]
  have hRoot : 1 <= Real.sqrt x := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hx
  have hReserve : a <= a * Real.sqrt x / delta := by
    calc
      _ <= a * Real.sqrt x := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hRoot ha0
      _ = (a * Real.sqrt x) / 1 := by rw [div_one]
      _ <= _ := div_le_div_of_nonneg_left
        (mul_nonneg ha0 (Real.sqrt_nonneg x)) hDelta0 hDelta1
  have hMain := mul_le_mul (hamiltonian_window_rook_ratio_bound delta s hDelta0 hDelta1 hs)
    (hamiltonian_sqrt_product_bound x a (le_trans (by norm_num) hx) ha)
    (Real.sqrt_nonneg _) (div_nonneg (by norm_num : (0 : Real) <= 3) hDelta0.le)
  change 2 * abs s * b / (1 - abs s * b * (1 - delta)) *
    Real.sqrt (x * (a - 1)) + abs s ^ 2 * b ^ 2 * (a - 1) / 2 <= _
  calc
    _ <= (3 / delta) * (a * Real.sqrt x) + a := add_le_add hMain hQuadratic
    _ <= (3 / delta) * (a * Real.sqrt x) + (a * Real.sqrt x) / delta :=
      add_le_add (le_refl _) hReserve
    _ = _ := by ring

theorem hamiltonian_log_le_twice_sqrt (x : Real) (hx : 1 <= x) :
    Real.log x <= 2 * Real.sqrt x := by
  have hPos : 0 < x := lt_of_lt_of_le (by norm_num) hx
  have hRootPos : 0 < Real.sqrt x := Real.sqrt_pos.mpr hPos
  have hSquare := Real.mul_self_sqrt hPos.le
  have hLog := Real.log_le_sub_one_of_pos hRootPos
  calc
    _ = Real.log (Real.sqrt x * Real.sqrt x) := congrArg Real.log hSquare.symm
    _ = 2 * Real.log (Real.sqrt x) := by
      rw [Real.log_mul (ne_of_gt hRootPos) (ne_of_gt hRootPos)]
      ring
    _ <= 2 * (Real.sqrt x - 1) := mul_le_mul_of_nonneg_left hLog (by norm_num)
    _ <= _ := by linarith

theorem hamiltonian_inverse_power_exp (b : Real) (hb : 0 < b) (n : Nat) :
    (Inv.inv b) ^ n = Real.exp (-((n : Real) * Real.log b)) := by
  induction n with
  | zero => simp only [pow_zero, Nat.cast_zero, zero_mul, neg_zero, Real.exp_zero]
  | succ n ih =>
    rw [pow_succ, ih]
    simp only [Nat.cast_add, Nat.cast_one, add_mul, one_mul, neg_add,
      Real.exp_add, Real.exp_neg, Real.exp_log hb]


theorem hamiltonian_cutoff_log_budget (delta a x h : Real)
    (hDelta0 : 0 < delta) (hDelta1 : delta <= 1) (ha : 0 <= a)
    (hLarge : 1000 * (1 + a) ^ 3 * Real.sqrt x / delta ^ 2 <= h) :
    25 * (1 + a) * Real.sqrt x / delta <=
      h * Real.log (hamiltonianWindowScale delta) := by
  have hH0 : 0 <= h := le_trans (by positivity) hLarge
  have hBase : 1 <= 1 + a := by linarith
  have hRest : 1 <= (1 + a) ^ 2 := by
    simpa only [one_pow] using
      wick_nonnegative_power_le 1 (1 + a) (by norm_num) hBase 2
  have hPoly : 1 + a <= (1 + a) ^ 3 := by
    calc
      _ = (1 + a) * 1 := by ring
      _ <= (1 + a) * (1 + a) ^ 2 :=
        mul_le_mul_of_nonneg_left hRest (by linarith)
      _ = _ := by ring
  have hFraction : (1 + a) * Real.sqrt x / delta <=
      (1 + a) ^ 3 * Real.sqrt x / delta :=
    div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hPoly (Real.sqrt_nonneg x)) hDelta0.le
  calc
    _ = 25 * ((1 + a) * Real.sqrt x / delta) := by ring
    _ <= (1000 / 17 : Real) * ((1 + a) * Real.sqrt x / delta) :=
      mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
    _ <= (1000 / 17 : Real) * ((1 + a) ^ 3 * Real.sqrt x / delta) :=
      mul_le_mul_of_nonneg_left hFraction (by norm_num)
    _ = (1000 * (1 + a) ^ 3 * Real.sqrt x / delta ^ 2) * (delta / 17) := by
      field_simp [ne_of_gt hDelta0]
    _ <= h * (delta / 17) :=
      mul_le_mul_of_nonneg_right hLarge (by positivity)
    _ <= _ := mul_le_mul_of_nonneg_left
      (hamiltonian_window_log_lower delta hDelta0 hDelta1) hH0

theorem hamiltonian_cutoff_exponent_margin (delta a x h C : Real)
    (hDelta0 : 0 < delta) (hDelta1 : delta <= 1)
    (ha : 1 <= a) (hx : 1 <= x)
    (hLarge : 1000 * (1 + a) ^ 3 * Real.sqrt x / delta ^ 2 <= h)
    (hC : C <= 4 * a * Real.sqrt x / delta) :
    C - h * Real.log (hamiltonianWindowScale delta) + Real.log (17 / delta) <=
      -2 * Real.log x := by
  let S := (1 + a) * Real.sqrt x
  let q := S / delta
  have hRoot : 1 <= Real.sqrt x := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hx
  have hS : 1 <= S := by
    have h := mul_le_mul (show 1 <= 1 + a by linarith) hRoot
      (by norm_num : (0 : Real) <= 1) (show 0 <= 1 + a by linarith)
    simpa only [one_mul] using h
  have hS0 : 0 <= S := le_trans (by norm_num) hS
  have hSdiv : S <= q := by
    calc
      _ = S / 1 := by rw [div_one]
      _ <= S / delta := div_le_div_of_nonneg_left hS0 hDelta0 hDelta1
  have hRootS : Real.sqrt x <= S := by
    have h := mul_le_mul_of_nonneg_right
      (show 1 <= 1 + a by linarith) (Real.sqrt_nonneg x)
    simpa only [one_mul] using h
  have hAS : a * Real.sqrt x <= S :=
    mul_le_mul_of_nonneg_right (by linarith : a <= 1 + a) (Real.sqrt_nonneg x)
  have hCq : C <= 4 * q := by
    calc
      _ <= 4 * a * Real.sqrt x / delta := hC
      _ <= 4 * S / delta :=
        div_le_div_of_nonneg_right
          (by nlinarith only [hAS]) hDelta0.le
      _ = _ := by dsimp only [q]; ring
  have hLogq : 2 * Real.log x <= 4 * q := by
    have h := hamiltonian_log_le_twice_sqrt x hx
    have hRQ := le_trans hRootS hSdiv
    linarith
  have hPrefq : Real.log (17 / delta) <= 17 * q := by
    calc
      _ <= 17 / delta :=
        Real.log_le_self (div_nonneg (by norm_num) hDelta0.le)
      _ <= 17 * S / delta :=
        div_le_div_of_nonneg_right (by nlinarith only [hS]) hDelta0.le
      _ = _ := by dsimp only [q]; ring
  have hBudget : 25 * q <= h * Real.log (hamiltonianWindowScale delta) := by
    calc
      _ = 25 * (1 + a) * Real.sqrt x / delta := by dsimp only [q, S]; ring
      _ <= _ := hamiltonian_cutoff_log_budget delta a x h
        hDelta0 hDelta1 (le_trans (by norm_num) ha) hLarge
  linarith only [hCq, hLogq, hPrefq, hBudget]


theorem hamiltonian_window_cauchy_tail_small (delta a x C : Real) (H : Nat)
    (hDelta0 : 0 < delta) (hDelta1 : delta <= 1)
    (ha : 1 <= a) (hx : 1 <= x)
    (hLarge : 1000 * (1 + a) ^ 3 * Real.sqrt x / delta ^ 2 <= (H : Real))
    (hC : C <= 4 * a * Real.sqrt x / delta) :
    Real.exp C * (Inv.inv (hamiltonianWindowScale delta)) ^ (H + 1) /
      (1 - Inv.inv (hamiltonianWindowScale delta)) <= 1 / x ^ 2 := by
  let b := hamiltonianWindowScale delta
  have hb := hamiltonian_window_scale_bounds delta hDelta0 hDelta1
  have hbPos : 0 < b := lt_trans (by norm_num) hb.1
  have hXPos : 0 < x := lt_of_lt_of_le (by norm_num) hx
  have hPrefPos : 0 < (17 / delta : Real) := by positivity
  have hNat : (H : Real) <= ((H + 1 : Nat) : Real) := by
    exact_mod_cast Nat.le_succ H
  have hMargin := hamiltonian_cutoff_exponent_margin delta a x
    ((H + 1 : Nat) : Real) C hDelta0 hDelta1 ha hx (le_trans hLarge hNat) hC
  change Real.exp C * (Inv.inv b) ^ (H + 1) * Inv.inv (1 - Inv.inv b) <= _
  rw [hamiltonian_inverse_power_exp b hbPos (H + 1)]
  calc
    _ = Real.exp (C - ((H + 1 : Nat) : Real) * Real.log b) * Inv.inv (1 - Inv.inv b) := by
      simpa only [sub_eq_add_neg] using
        congrArg (fun y : Real => y * Inv.inv (1 - Inv.inv b))
          (Real.exp_add C (-(((H + 1 : Nat) : Real) * Real.log b))).symm
    _ <= Real.exp (C - ((H + 1 : Nat) : Real) * Real.log b) * (17 / delta) :=
      mul_le_mul_of_nonneg_left
        (hamiltonian_window_cauchy_prefactor_bound delta hDelta0 hDelta1) (Real.exp_pos _).le
    _ = Real.exp (C - ((H + 1 : Nat) : Real) * Real.log b + Real.log (17 / delta)) := by
      rw [Real.exp_add, Real.exp_log hPrefPos]
    _ <= Real.exp (-2 * Real.log x) := Real.exp_le_exp.mpr hMargin
    _ = _ := by
      have hNeg : -2 * Real.log x = -(Real.log x + Real.log x) := by ring
      rw [hNeg]
      simp only [Real.exp_neg, Real.exp_add, Real.exp_log hXPos, pow_two, one_div]

end PrimeFactorOscillations

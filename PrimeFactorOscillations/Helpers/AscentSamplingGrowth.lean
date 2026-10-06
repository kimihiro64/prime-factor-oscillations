/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.LocalizedReversalCriterion
import PrimeFactorOscillations.Helpers.TiltedPowerExcursion

/-!
# Quantitative growth retained through the tilt mesh

A power-logarithmic count implies subpower supply. Multiplication by the
square-root mesh and a false-RH excursion exponent below one half absorbs
both logarithmic frequency loss and the full unit rounding loss per pair.
-/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace PrimeFactorOscillations
open Filter

theorem power_subpower_mesh_amplification (m : Nat -> Nat)
    (hm : forall e : Real, 0 < e ->
      Filter.Eventually (fun X : Nat =>
        (X : Real) ^ (7 / 10 - e) <= (m X : Real)) atTop)
    (b C : Real) (hb : b < 1 / 2) (hC : 0 < C) :
    Filter.Eventually (fun X : Nat =>
      C * (X : Real) ^ (7 / 10 : Real) <
        (m X : Real) * ((localTiltMesh X : Real) * (X : Real) ^ (-b) - 1)) atTop := by
  let e : Real := (1 / 2 - b) / 2
  have he : 0 < e := by dsimp [e]; linarith
  have hCast : Tendsto (fun n : Nat => (n : Real)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hGrow := hCast.eventually ((tendsto_rpow_atTop he).eventually_gt_atTop (2 * C + 2))
  filter_upwards [hm e he, hGrow, eventually_ge_atTop (1 : Nat)] with X hCount hLarge hOne
  have hx : 0 < (X : Real) := by exact_mod_cast (by omega : 0 < X)
  have hx1 : (1 : Real) <= X := by exact_mod_cast hOne
  have hEOne : 1 <= (X : Real) ^ e := by
    simpa only [Real.rpow_zero] using Real.rpow_le_rpow_of_exponent_le hx1 he.le
  have hEPos : 0 < (X : Real) ^ e := Real.rpow_pos_of_pos hx _
  have hTwice : (X : Real) ^ (1 / 2 : Real) * (X : Real) ^ (-b) =
      (X : Real) ^ e * (X : Real) ^ e := by
    rw [<- Real.rpow_add hx, <- Real.rpow_add hx]
    congr 1
    dsimp [e]
    ring
  have hMesh := mul_le_mul_of_nonneg_right (Nat.le_ceil ((X : Real) ^ (1 / 2 : Real)))
    (Real.rpow_nonneg hx.le (-b))
  change (X : Real) ^ (1 / 2 : Real) * (X : Real) ^ (-b) <=
    (localTiltMesh X : Real) * (X : Real) ^ (-b) at hMesh
  rw [hTwice] at hMesh
  have hGain : (1 / 2 : Real) * ((X : Real) ^ e * (X : Real) ^ e) <=
      (localTiltMesh X : Real) * (X : Real) ^ (-b) - 1 := by
    have hLarge2 : 2 < (X : Real) ^ e := by linarith
    nlinarith
  have hProduct := mul_le_mul hCount hGain (by positivity) (Nat.cast_nonneg (m X))
  have heq : (X : Real) ^ (7 / 10 - e) *
      ((1 / 2 : Real) * ((X : Real) ^ e * (X : Real) ^ e)) =
      ((X : Real) ^ e / 2) * (X : Real) ^ (7 / 10 : Real) := by
    have hc : (X : Real) ^ (7 / 10 - e) * (X : Real) ^ e =
        (X : Real) ^ (7 / 10 : Real) := by
      rw [<- Real.rpow_add hx]
      congr 1
      ring
    calc
      _ = ((X : Real) ^ (7 / 10 - e) * (X : Real) ^ e) * ((X : Real) ^ e / 2) := by ring
      _ = _ := by rw [hc]; ring
  rw [heq] at hProduct
  exact (mul_lt_mul_of_pos_right (by linarith : C < (X : Real) ^ e / 2)
    (Real.rpow_pos_of_pos hx (7 / 10))).trans_le hProduct

theorem subpower_supply_of_power_log_lower (m : Nat -> Nat) (c B : Real)
    (hc : 0 < c)
    (hLower : Filter.Eventually (fun X : Nat =>
      c * (X : Real) ^ (7 / 10 : Real) / (Real.log (X : Real)) ^ B <= (m X : Real)) atTop) :
    forall e : Real, 0 < e -> Filter.Eventually (fun X : Nat =>
      (X : Real) ^ (7 / 10 - e) <= (m X : Real)) atTop := by
  intro e he
  have hSmall := (isLittleO_log_rpow_rpow_atTop B he).bound hc
  have hCast : Tendsto (fun n : Nat => (n : Real)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  filter_upwards [hLower, hCast.eventually hSmall, eventually_ge_atTop (2 : Nat)] with X hm hs hx
  have hx0 : 0 < (X : Real) := by exact_mod_cast (by omega : 0 < X)
  have hx1 : (1 : Real) < X := by exact_mod_cast (by omega : 1 < X)
  have hl : 0 < (Real.log (X : Real)) ^ B := Real.rpow_pos_of_pos (Real.log_pos hx1) _
  change norm ((Real.log (X : Real)) ^ B) <= c * norm ((X : Real) ^ e) at hs
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hl.le,
    abs_of_nonneg (Real.rpow_nonneg hx0.le _)] at hs
  have hMul := mul_le_mul_of_nonneg_left hs
    (Real.rpow_nonneg hx0.le (7 / 10 - e))
  have hp : (X : Real) ^ (7 / 10 - e) * (X : Real) ^ e = (X : Real) ^ (7 / 10 : Real) := by
    rw [<- Real.rpow_add hx0]
    congr 1
    ring
  have hBound : (X : Real) ^ (7 / 10 - e) <=
      c * (X : Real) ^ (7 / 10 : Real) / (Real.log (X : Real)) ^ B := by
    have hcanc : (c * (X : Real) ^ (7 / 10 : Real) / (Real.log (X : Real)) ^ B) *
        (Real.log (X : Real)) ^ B = c * (X : Real) ^ (7 / 10 : Real) := by field_simp
    by_contra hn
    have ht := mul_lt_mul_of_pos_right (lt_of_not_ge hn) hl
    rw [hcanc] at ht
    rw [mul_left_comm, hp] at hMul
    linarith
  exact hBound.trans hm

end PrimeFactorOscillations



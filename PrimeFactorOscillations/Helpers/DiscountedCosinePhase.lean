/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Tactic.FieldSimp
import PrimeFactorOscillations.Helpers.GrowingCosineKernel

/-! # The full discounted cosine and its explicit modular phase -/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.PrimeClassDeletion

noncomputable def cosinePhaseRemainder (w a : Real) : Real :=
  w - a - (Int.floor ((w - a) / (2 * Real.pi)) : Real) * (2 * Real.pi)

theorem cosinePhaseRemainder_bounds (w a : Real) :
    And (0 <= cosinePhaseRemainder w a) (cosinePhaseRemainder w a < 2 * Real.pi) := by
  have hp : 0 < 2 * Real.pi := mul_pos (by norm_num) Real.pi_pos
  let z := (w - a) / (2 * Real.pi)
  have hlo := mul_le_mul_of_nonneg_right (Int.floor_le z) hp.le
  have hhi := mul_lt_mul_of_pos_right (Int.lt_floor_add_one z) hp
  have hz : z * (2 * Real.pi) = w - a := by
    dsimp [z]
    field_simp [ne_of_gt hp]
  rw [hz] at hlo hhi
  dsimp [cosinePhaseRemainder]
  change And (0 <= w - a - (Int.floor z : Real) * (2 * Real.pi))
    (w - a - (Int.floor z : Real) * (2 * Real.pi) < 2 * Real.pi)
  constructor <;> nlinarith only [hlo, hhi]

theorem cosinePhaseRemainder_cos (w a z : Real) :
    Real.cos (w - z) = Real.cos (a + cosinePhaseRemainder w a - z) := by
  have hid : w - z = (a + cosinePhaseRemainder w a - z) +
      (Int.floor ((w - a) / (2 * Real.pi)) : Real) * (2 * Real.pi) := by
    dsimp [cosinePhaseRemainder]
    ring
  rw [hid, Real.cos_add_int_mul_two_pi]

theorem discountedCosine_phase_upper (k a d z : Real) (hk : 0 <= k)
    (hcos : 0 <= Real.cos a) (hsin : Real.sin a = k * Real.cos a)
    (hd : 0 <= d) (hd2 : d <= 2 * Real.pi) (hz : 0 <= z) :
    Real.exp (-(k * z)) * Real.cos (a + d - z) <=
      max (Real.cos (a + d)) (Real.cos a * Real.exp (-(k * d))) := by
  let r := d - z
  have hbound := growingCosine_full_prefix_bound k a d r hk hcos hsin hd hd2
    (show r <= d by dsimp [r]; linarith only [hz])
  have he : Real.exp (-(k * z)) = Real.exp (-(k * d)) * Real.exp (k * r) := by
    rw [<- Real.exp_add]
    congr 1
    dsimp [r]
    ring
  have hp : Real.exp (-(k * d)) *
      (Real.exp (k * d) * Real.cos (a + d)) = Real.cos (a + d) := by
    rw [<- mul_assoc, <- Real.exp_add,
      show -(k * d) + k * d = 0 by ring, Real.exp_zero, one_mul]
  have hidentity : Real.exp (-(k * z)) * Real.cos (a + d - z) =
      Real.exp (-(k * d)) * (Real.exp (k * r) * Real.cos (a + r)) := by
    rw [he, show a + d - z = a + r by dsimp [r]; ring, mul_assoc]
  rw [hidentity]
  cases le_total (Real.cos a) (Real.exp (k * d) * Real.cos (a + d)) with
  | inl hc =>
      rw [max_eq_right hc] at hbound
      exact ((mul_le_mul_of_nonneg_left hbound (Real.exp_pos _).le).trans_eq hp).trans
        (le_max_left _ _)
  | inr hc =>
      rw [max_eq_left hc] at hbound
      exact ((mul_le_mul_of_nonneg_left hbound (Real.exp_pos _).le).trans_eq
        (mul_comm _ _)).trans (le_max_right _ _)

end PrimeFactorOscillations.PrimeClassDeletion

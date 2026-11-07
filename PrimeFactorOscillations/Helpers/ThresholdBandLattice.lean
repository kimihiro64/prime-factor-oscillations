/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Algebra.Order.Floor.Semiring
import PrimeFactorOscillations.Helpers.ThresholdNonlinearComparison

/-! # Arithmetic separation and the optimized joint tilt -/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 5000000

noncomputable section
namespace PrimeFactorOscillations

def thresholdBandGap (d p : Real) : Real :=
  min (p - 2 * d * (Nat.floor (p / (2 * d)) : Real))
    (2 * d * ((Nat.floor (p / (2 * d)) : Real) + 1) - p)

def thresholdBandPenalty (A B eta : Real) : Real :=
  if 2 * eta <= A * B then eta ^ 2 / B else A * eta - A ^ 2 * B / 4

theorem thresholdBandGap_cell (d p : Real) (hd : 0 < d) (hp : 0 <= p) :
    And (2 * d * (Nat.floor (p / (2 * d)) : Real) <= p)
      (p < 2 * d * ((Nat.floor (p / (2 * d)) : Real) + 1)) := by
  have hDen : 0 < 2 * d := by positivity
  have hCancel : p / (2 * d) * (2 * d) = p := by field_simp
  have hLo := mul_le_mul_of_nonneg_right (Nat.floor_le (div_nonneg hp hDen.le)) hDen.le
  have hHi := mul_lt_mul_of_pos_right (Nat.lt_floor_add_one (p / (2 * d))) hDen
  rw [hCancel] at hLo hHi
  constructor <;> nlinarith only [hLo, hHi]

theorem thresholdBandGap_nonneg (d p : Real) (hd : 0 < d) (hp : 0 <= p) :
    0 <= thresholdBandGap d p := by
  have h := thresholdBandGap_cell d p hd hp
  exact le_min (sub_nonneg.mpr h.1) (sub_nonneg.mpr h.2.le)

theorem thresholdBandGap_le_distance (d p : Real) (hd : 0 < d) (hp : 0 <= p)
    (m : Nat) : thresholdBandGap d p <= abs (p - 2 * d * (m : Real)) := by
  have hCell := thresholdBandGap_cell d p hd hp
  by_cases hm : m <= Nat.floor (p / (2 * d))
  case pos =>
    have hc : (m : Real) <= (Nat.floor (p / (2 * d)) : Real) := by exact_mod_cast hm
    have hMul := mul_nonneg (show 0 <= 2 * d by positivity) (sub_nonneg.mpr hc)
    rw [abs_of_nonneg (show 0 <= p - 2 * d * (m : Real) by nlinarith only [hCell.1, hMul])]
    exact le_trans (min_le_left _ _) (by nlinarith only [hMul])
  case neg =>
    have hn : Nat.floor (p / (2 * d)) + 1 <= m := by omega
    have hc : (Nat.floor (p / (2 * d)) : Real) + 1 <= (m : Real) := by exact_mod_cast hn
    have hMul := mul_nonneg (show 0 <= 2 * d by positivity) (sub_nonneg.mpr hc)
    rw [abs_of_nonpos (show p - 2 * d * (m : Real) <= 0 by nlinarith only [hCell.2, hMul])]
    exact le_trans (min_le_right _ _) (by nlinarith only [hMul])

theorem thresholdBandGap_pos (d p : Real) (hd : 0 < d) (hp : 0 <= p)
    (hAway : forall m : Nat, Not (p = 2 * d * (m : Real))) :
    0 < thresholdBandGap d p := by
  have hc := thresholdBandGap_cell d p hd hp
  have hStrict : 2 * d * (Nat.floor (p / (2 * d)) : Real) < p :=
    lt_of_le_of_ne hc.1 (Ne.symm (hAway _))
  exact lt_min (sub_pos.mpr hStrict) (sub_pos.mpr hc.2)

theorem thresholdBandGap_pos_small (d p : Real) (hd : 0 < d)
    (hp : And (0 < p) (p < 2 * d)) : 0 < thresholdBandGap d p := by
  apply thresholdBandGap_pos d p hd hp.1.le
  intro m hm
  by_cases hz : m = 0
  case pos => simp [hz] at hm; linarith only [hp.1, hm]
  case neg =>
    have hn : 1 <= m := by omega
    have hc : (1 : Real) <= (m : Real) := by exact_mod_cast hn
    have hMul := mul_nonneg (show 0 <= 2 * d by positivity) (sub_nonneg.mpr hc)
    nlinarith only [hm, hp.2, hMul]

theorem thresholdBandPenalty_le (A B eta Delta : Real)
    (hA : 0 < A) (hB : 0 < B) (he : 0 <= eta)
    (hTilt : forall l : Real, 0 <= l -> l <= A -> l * eta - B * l ^ 2 / 4 <= Delta) :
    thresholdBandPenalty A B eta <= Delta := by
  unfold thresholdBandPenalty
  split_ifs with h
  case pos =>
    have hl : 0 <= 2 * eta / B := div_nonneg (by positivity) hB.le
    have hu : 2 * eta / B <= A := by
      calc
        _ <= (A * B) / B := div_le_div_of_nonneg_right h hB.le
        _ = A := by field_simp
    have ht := hTilt (2 * eta / B) hl hu
    have hi : (2 * eta / B) * eta - B * (2 * eta / B) ^ 2 / 4 = eta ^ 2 / B := by
      field_simp
      <;> ring
    rwa [hi] at ht
  case neg =>
    have ht := hTilt A hA.le (le_refl A)
    nlinarith only [ht]

theorem thresholdBandPenalty_nonneg (A B eta : Real)
    (hA : 0 < A) (hB : 0 < B) (he : 0 <= eta) :
    0 <= thresholdBandPenalty A B eta := by
  unfold thresholdBandPenalty
  split_ifs with h
  case pos => exact div_nonneg (sq_nonneg eta) hB.le
  case neg =>
    have hh : 0 < eta - A * B / 2 := by linarith only [h]
    have hm := mul_pos hA hh
    have hAB := mul_pos (sq_pos_of_pos hA) hB
    nlinarith only [hm, hAB]

theorem thresholdBandPenalty_pos (A B eta : Real)
    (hA : 0 < A) (hB : 0 < B) (he : 0 < eta) :
    0 < thresholdBandPenalty A B eta := by
  unfold thresholdBandPenalty
  split_ifs with h
  case pos => exact div_pos (sq_pos_of_pos he) hB
  case neg =>
    have hh : 0 < eta - A * B / 2 := by linarith only [h]
    have hm := mul_pos hA hh
    have hAB := mul_pos (sq_pos_of_pos hA) hB
    nlinarith only [hm, hAB]

end PrimeFactorOscillations

/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.ThresholdMomentPackets

/-! # A coupled tilted packet for an interior threshold band -/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 5000000

noncomputable section
namespace PrimeFactorOscillations

def thresholdBandIndicator (d y : Real) : Real := if And (d / 2 <= y) (y < d) then 1 else 0

def thresholdBandMass {Iota : Type*} (d : Real) (S : Finset Iota)
    (a y : Iota -> Real) : Real := Finset.sum S (fun i => a i * thresholdBandIndicator d (y i))

def thresholdBandSlope (d z : Real) : Real :=
  (d / 2) * (2 * z + thresholdPositiveMultiplier d z - 2 * d)

def thresholdBandCurvature (d z : Real) : Real := d - thresholdPositiveMultiplier d z

theorem thresholdBand_constants_pos (d z : Real)
    (hd : And (0 < d) (d < 1)) (hz : 1 <= z) :
    And (0 < thresholdBandSlope d z) (0 < thresholdBandCurvature d z) := by
  have hb := thresholdPositiveMultiplier_bounds d z hd hz
  constructor
  case left => unfold thresholdBandSlope; exact mul_pos (by linarith only [hd.1]) (by linarith only [hb.2])
  case right => unfold thresholdBandCurvature; linarith only [hd.1, hb.1]

theorem thresholdBand_low_coercivity (d z y : Real)
    (hd : And (0 < d) (d < 1)) (hz : 1 <= z) (hy : And (0 <= y) (y < d)) :
    thresholdBandSlope d z * abs (y - d * thresholdBandIndicator d y) <=
      thresholdPositivePacket d z y := by
  classical
  let c := 2 * z + thresholdPositiveMultiplier d z - d
  have hc : d < c := (thresholdPositiveMultiplier_bounds d z hd hz).2
  have hSlope : thresholdBandSlope d z = (d / 2) * (c - d) := by
    dsimp [thresholdBandSlope, c]
    ring
  rw [hSlope]
  have hQ : thresholdPositivePacket d z y = y * (d - y) * (c - y) := by
    rw [thresholdPositivePacket_unselected d z y hd hz hy.2]
    dsimp [c]
    ring
  by_cases hHalf : d / 2 <= y
  case pos =>
    have hI : thresholdBandIndicator d y = 1 := if_pos (And.intro hHalf hy.2)
    rw [hI, mul_one, abs_of_nonpos (by linarith only [hy.2])]
    have hProd : (d / 2) * (c - d) <= y * (c - y) := by
      calc
        _ <= y * (c - d) := mul_le_mul_of_nonneg_right hHalf (by linarith only [hc])
        _ <= _ := mul_le_mul_of_nonneg_left (by linarith only [hy.2]) hy.1
    have hMul := mul_le_mul_of_nonneg_right hProd (by linarith only [hy.2] : 0 <= d - y)
    rw [hQ]
    change (d / 2) * (c - d) * -(y - d) <= y * (d - y) * (c - y)
    nlinarith only [hMul]
  case neg =>
    have hI : thresholdBandIndicator d y = 0 := if_neg (fun hh => hHalf hh.1)
    rw [hI, mul_zero, sub_zero, abs_of_nonneg hy.1]
    have hProd : (d / 2) * (c - d) <= (d - y) * (c - y) := by
      calc
        _ <= (d - y) * (c - d) := mul_le_mul_of_nonneg_right (by linarith only [hHalf]) (by linarith only [hc])
        _ <= _ := mul_le_mul_of_nonneg_left (by linarith only [hy.2]) (by linarith only [hy.2])
    have hMul := mul_le_mul_of_nonneg_left hProd hy.1
    rw [hQ]
    change (d / 2) * (c - d) * y <= y * (d - y) * (c - y)
    nlinarith only [hMul]

theorem thresholdBand_high_coercivity (d z y : Real) (hy : d <= y) :
    thresholdBandCurvature d z * (y - z) ^ 2 <= thresholdPositivePacket d z y := by
  rw [thresholdPositivePacket_selected d z y hy]
  have hm := mul_nonneg (sq_nonneg (y - z)) (sub_nonneg.mpr hy)
  unfold thresholdBandCurvature
  nlinarith only [hm]

theorem thresholdBand_tilted_packet (d z y l s : Real)
    (hd : And (0 < d) (d < 1)) (hz : 1 <= z) (hy : 0 <= y)
    (hl : And (0 <= l) (l <= thresholdBandSlope d z)) (hs : Or (s = 1) (s = -1)) :
    0 <= thresholdPositivePacket d z y +
      l ^ 2 / (4 * thresholdBandCurvature d z) * momentRoundIndicator d y -
      l * s * (y - z * momentRoundIndicator d y - d * thresholdBandIndicator d y) := by
  classical
  have hC := (thresholdBand_constants_pos d z hd hz).2
  by_cases hCut : d <= y
  case pos =>
    have hI : thresholdBandIndicator d y = 0 := if_neg (fun h => (not_lt.mpr hCut) h.2)
    simp only [momentRoundIndicator, if_pos hCut, hI, mul_one, mul_zero, sub_zero]
    have hQ := thresholdBand_high_coercivity d z y hCut
    have hId : thresholdBandCurvature d z * (y - z) ^ 2 +
        l ^ 2 / (4 * thresholdBandCurvature d z) - l * s * (y - z) =
        (thresholdBandCurvature d z * (y - z) - l * s / 2) ^ 2 / thresholdBandCurvature d z := by
      rcases hs with h | h <;> rw [h] <;> field_simp <;> ring
    have hSq := div_nonneg (sq_nonneg (thresholdBandCurvature d z * (y - z) - l * s / 2)) hC.le
    linarith only [hQ, hId, hSq]
  case neg =>
    have hQ := thresholdBand_low_coercivity d z y hd hz (And.intro hy (lt_of_not_ge hCut))
    simp only [momentRoundIndicator, if_neg hCut, mul_zero, sub_zero]
    have hSlack := mul_nonneg (sub_nonneg.mpr hl.2) (abs_nonneg (y - d * thresholdBandIndicator d y))
    rcases hs with h | h
    case inl =>
      rw [h, mul_one]
      have hm := mul_le_mul_of_nonneg_left (le_abs_self (y - d * thresholdBandIndicator d y)) hl.1
      nlinarith only [hQ, hSlack, hm]
    case inr =>
      rw [h]
      have hm := mul_le_mul_of_nonneg_left (neg_le_abs (y - d * thresholdBandIndicator d y)) hl.1
      nlinarith only [hQ, hSlack, hm]

end PrimeFactorOscillations

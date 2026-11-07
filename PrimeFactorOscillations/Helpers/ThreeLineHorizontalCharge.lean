/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import PrimeFactorOscillations.Helpers.ThreeLineResolventCertificate

/-! # A quantitative horizontal charge for the signed three-line kernel -/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000

noncomputable section
namespace PrimeFactorOscillations

def threeLineHorizontalA : Real :=
  threeLineDiagonal (1 / 4) - (13 / 2 : Real) *
    (threeLineRadius1 ^ 2 * threeLineRadius2 ^ 2 * threeLineRadius3 ^ 2)

def threeLineHorizontalC : Real :=
  (13 / 2 : Real) * (threeLineRadius1 ^ 2 + threeLineRadius2 ^ 2 +
    threeLineRadius3 ^ 2) - threeLineCharge

def threeLineHorizontalB : Real :=
  -(1329922720112744657 / 700140000000000000 : Real) -
    (9 / 32 : Real) * threeLineCharge + (13 / 2 : Real) *
      (threeLineRadius1 ^ 2 * threeLineRadius2 ^ 2 +
        threeLineRadius1 ^ 2 * threeLineRadius3 ^ 2 +
        threeLineRadius2 ^ 2 * threeLineRadius3 ^ 2) - threeLineHorizontalC / 4

theorem threeLineHorizontalCoefficients_pos :
    And (0 < threeLineHorizontalA)
      (And (0 < threeLineHorizontalB) (0 < threeLineHorizontalC)) := by
  norm_num [threeLineHorizontalA, threeLineHorizontalB, threeLineHorizontalC,
    threeLineDiagonal, threeLineCharge, threeLineRadius1, threeLineRadius2,
    threeLineRadius3]

theorem threeLineKernel_quadratic_charge (u : Real) (hu : abs u <= 1 / 2) :
    threeLineCharge + (13 / 2 : Real) * u ^ 2 <= threeLineKernel u 0 := by
  have h1 : abs u < threeLineRadius1 := hu.trans_lt (by norm_num [threeLineRadius1])
  have h2 : abs u < threeLineRadius2 := hu.trans_lt (by norm_num [threeLineRadius2])
  have h3 : abs u < threeLineRadius3 := hu.trans_lt (by norm_num [threeLineRadius3])
  have hd1 := resolventSquareMargin_pos _ _ h1
  have hd2 := resolventSquareMargin_pos _ _ h2
  have hd3 := resolventSquareMargin_pos _ _ h3
  let D : Real := (threeLineRadius1 ^ 2 - u ^ 2) *
    (threeLineRadius2 ^ 2 - u ^ 2) * (threeLineRadius3 ^ 2 - u ^ 2)
  have hD : 0 < D := mul_pos (mul_pos hd1 hd2) hd3
  have hq : 0 <= 1 / 4 - u ^ 2 := by
    have hh := abs_le.mp hu
    have hm : 0 <= (1 / 2 - u) * (1 / 2 + u) :=
      mul_nonneg (by linarith only [hh.2]) (by linarith only [hh.1])
    nlinarith only [hm]
  have hid : (threeLineKernel u 0 - (threeLineCharge + (13 / 2 : Real) * u ^ 2)) * D =
      u ^ 2 * (threeLineHorizontalA + threeLineHorizontalB * u ^ 2 +
        threeLineHorizontalC * u ^ 2 * (1 / 4 - u ^ 2) + (13 / 2 : Real) * (u ^ 2) ^ 3) := by
    unfold threeLineKernel
    rw [pairedResolventMean_at_zero _ _ h1, pairedResolventMean_at_zero _ _ h2,
      pairedResolventMean_at_zero _ _ h3]
    dsimp only [D]
    field_simp [hd1.ne', hd2.ne', hd3.ne']
    unfold threeLineHorizontalA threeLineHorizontalB threeLineHorizontalC
      threeLineDiagonal threeLineRadius1 threeLineRadius2 threeLineRadius3
      threeLineWeight1 threeLineWeight2 threeLineWeight3 threeLineCharge
    ring
  have hc := threeLineHorizontalCoefficients_pos
  have hA : 0 <= threeLineHorizontalA := hc.1.le
  have hB : 0 <= threeLineHorizontalB := hc.2.1.le
  have hC : 0 <= threeLineHorizontalC := hc.2.2.le
  have hP : 0 <= threeLineHorizontalA + threeLineHorizontalB * u ^ 2 +
      threeLineHorizontalC * u ^ 2 * (1 / 4 - u ^ 2) + (13 / 2 : Real) * (u ^ 2) ^ 3 := by
    positivity
  have hp : 0 <= (threeLineKernel u 0 -
      (threeLineCharge + (13 / 2 : Real) * u ^ 2)) * D := by
    rw [hid]
    exact mul_nonneg (sq_nonneg u) hP
  have hscaled : 0 * D <= (threeLineKernel u 0 -
      (threeLineCharge + (13 / 2 : Real) * u ^ 2)) * D := by simpa using hp
  exact sub_nonneg.mp ((mul_le_mul_iff_of_pos_right hD).mp hscaled)

end PrimeFactorOscillations

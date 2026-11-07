/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Mathlib.Analysis.Complex.PairedResolventKernel

/-! # An exact signed remainder for the full-strip block kernel -/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 5000000

noncomputable section
namespace PrimeFactorOscillations

def unitBlockDenTwo (v w : Real) : Real := (4 + w) ^ 2 + (2 * w - 8) * v + v ^ 2

def unitBlockDenThree (v w : Real) : Real := (9 + w) ^ 2 + (2 * w - 18) * v + v ^ 2

def unitBlockGram (v w : Real) : Real :=
  (4 + w) * (9 + w) - (13 + 6 * w) * v + v ^ 2

def unitBlockDefect (v w : Real) : Real :=
  unitBlockGram v w * (4 + w) * (9 + w) - unitBlockDenTwo v w * unitBlockDenThree v w

theorem unitBlockDefect_identity (v w : Real) :
    unitBlockDefect v w = v * (7 / 64 +
      (1 - w) * (418 + 127 * w + 10 * w ^ 2) + v * w * (39 - 5 * w) +
      4 * v ^ 2 * (1 - w) +
      (1 / 4 - v) * (v ^ 2 - (87 / 4) * v + 3193 / 16)) := by
  unfold unitBlockDefect unitBlockGram unitBlockDenTwo unitBlockDenThree
  ring

theorem unitBlockDefect_lower (v w : Real)
    (hv : And (0 <= v) (v <= 1 / 4)) (hw : And (0 <= w) (w <= 1)) :
    (7 / 64) * v <= unitBlockDefect v w := by
  have hA : 0 <= (1 - w) * (418 + 127 * w + 10 * w ^ 2) :=
    mul_nonneg (sub_nonneg.mpr hw.2) (by nlinarith only [hw.1, sq_nonneg w])
  have hB : 0 <= v * w * (39 - 5 * w) :=
    mul_nonneg (mul_nonneg hv.1 hw.1) (by linarith only [hw.2])
  have hC : 0 <= 4 * v ^ 2 * (1 - w) :=
    mul_nonneg (mul_nonneg (by norm_num : (0 : Real) <= 4) (sq_nonneg v)) (sub_nonneg.mpr hw.2)
  have hD : 0 <= (1 / 4 - v) * (v ^ 2 - (87 / 4) * v + 3193 / 16) :=
    mul_nonneg (sub_nonneg.mpr hv.2) (by nlinarith only [hv.2, sq_nonneg v])
  have hRest : (7 / 64 : Real) <= 7 / 64 +
      (1 - w) * (418 + 127 * w + 10 * w ^ 2) + v * w * (39 - 5 * w) +
      4 * v ^ 2 * (1 - w) + (1 / 4 - v) * (v ^ 2 - (87 / 4) * v + 3193 / 16) := by
    linarith only [hA, hB, hC, hD]
  rw [unitBlockDefect_identity]
  have hMul := mul_le_mul_of_nonneg_left hRest hv.1
  simpa only [mul_comm] using hMul

end PrimeFactorOscillations

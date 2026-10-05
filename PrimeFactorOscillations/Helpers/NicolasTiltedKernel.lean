/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.Robin1984.NicolasLandau.NicolasOscillation
import PrimeFactorOscillations.Mathlib.Analysis.SpecialFunctions.Log.NormalizedLinearProduct

/-!
# The kernel for positive prime-product tilts

The exact derivative kernel differs from the Nicolas kernel by a uniformly
integrable remainder, with explicit dependence on the nonnegative tilt.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

open MeasureTheory Set Robin1984

def nicolasTiltedWeight (z t : Real) : Real :=
  Real.log (1 + z / (t - 1)) / Real.log t

def nicolasTiltedKernel (z t : Real) : Real :=
  z / ((t - 1) * (t - 1 + z) * Real.log t) +
    Real.log (1 + z / (t - 1)) / (t * (Real.log t) ^ 2)

theorem hasDerivAt_nicolasTiltedWeight {z t : Real} (hz : 0 <= z) (ht : 1 < t) :
    HasDerivAt (nicolasTiltedWeight z) (-nicolasTiltedKernel z t) t := by
  have ht0 : 0 < t := by linarith
  have hd : 0 < t - 1 := by linarith
  have hdz : 0 < t - 1 + z := by linarith
  have hl : 0 < Real.log t := Real.log_pos ht
  have ha : 0 < 1 + z / (t - 1) := by positivity
  have h := (((hasDerivAt_const t 1).add
    ((hasDerivAt_const t z).div ((hasDerivAt_id t).sub_const 1) hd.ne')).log
      ha.ne').div (Real.hasDerivAt_log ht0.ne') hl.ne'
  convert h using 1
  . rfl
  . dsimp [nicolasTiltedKernel]
    field_simp
    ring

theorem nicolasTiltedKernel_pos {z t : Real} (hz : 0 < z) (ht : 1 < t) :
    0 < nicolasTiltedKernel z t := by
  have hd : 0 < t - 1 := by linarith
  have hdz : 0 < t - 1 + z := by linarith
  have ht0 : 0 < t := by linarith
  have hl : 0 < Real.log t := Real.log_pos ht
  have ha : 1 < 1 + z / (t - 1) := by
    exact lt_add_of_pos_right 1 (div_pos hz hd)
  unfold nicolasTiltedKernel
  exact add_pos (div_pos hz (mul_pos (mul_pos hd hdz) hl))
    (div_pos (Real.log_pos ha) (mul_pos ht0 (sq_pos_of_pos hl)))

theorem nicolasTiltedKernel_error {z t : Real} (hz : 0 <= z)
    (ht : 2 <= t) (hlog : 1 <= Real.log t) :
    |nicolasTiltedKernel z t - z * nicolasTailKernel t| <=
      14 * (z + z ^ 2) / (t ^ 3 * Real.log t) := by
  have ht0 : 0 < t := by linarith
  have hd : 0 < t - 1 := by linarith
  have hdz : 0 < t - 1 + z := by linarith
  have hl : 0 < Real.log t := by linarith
  have hHalf : t / 2 <= t - 1 := by linarith
  have hInv : 1 / (t - 1) <= 2 / t := by
    convert one_div_le_one_div_of_le (half_pos ht0) hHalf using 1 ; field_simp
  have hDen : t ^ 2 / 4 <= (t - 1) * (t - 1 + z) := by
    have hs := mul_self_le_mul_self (half_pos ht0).le hHalf
    have hp := mul_nonneg hd.le hz
    nlinarith only [hs, hp]
  have hInvDen : 1 / ((t - 1) * (t - 1 + z)) <= 4 / t ^ 2 := by
    convert one_div_le_one_div_of_le (by positivity : 0 < t ^ 2 / 4) hDen using 1 ;
      field_simp
  have hNum : |t ^ 2 - (t - 1) * (t - 1 + z)| <= (2 + z) * t := by
    have hAbs : |1 - z| <= 1 + z := abs_le.mpr (And.intro (by linarith) (by linarith))
    have hIdentity : t ^ 2 - (t - 1) * (t - 1 + z) = t + (1 - z) * (t - 1) := by ring
    rw [hIdentity]
    calc
      _ <= |t| + |(1 - z) * (t - 1)| := abs_add_le _ _
      _ = t + |1 - z| * (t - 1) := by
        rw [abs_of_pos ht0, abs_mul, abs_of_pos hd]
      _ <= t + (1 + z) * (t - 1) := by gcongr
      _ <= (2 + z) * t := by nlinarith only [hz]
  have hRational :
      |z / ((t - 1) * (t - 1 + z)) - z / t ^ 2| <=
        4 * z * (2 + z) / t ^ 3 := by
    have hEq : z / ((t - 1) * (t - 1 + z)) - z / t ^ 2 =
        (z / t ^ 2) * (t ^ 2 - (t - 1) * (t - 1 + z)) *
          (1 / ((t - 1) * (t - 1 + z))) := by
      field_simp
    rw [hEq, abs_mul, abs_mul, abs_of_nonneg (by positivity : 0 <= z / t ^ 2),
      abs_of_pos (by positivity : 0 < 1 / ((t - 1) * (t - 1 + z)))]
    calc
      _ <= (z / t ^ 2) * ((2 + z) * t) * (4 / t ^ 2) := by
        exact mul_le_mul (mul_le_mul_of_nonneg_left hNum (by positivity))
          hInvDen (by positivity) (by positivity)
      _ = _ := by field_simp
  have hA : z / (t - 1) <= 2 * z / t := by
    have h := mul_le_mul_of_nonneg_left hInv hz
    convert h using 1 <;> ring
  have hSq : (z / (t - 1)) ^ 2 <= (2 * z / t) ^ 2 := by
    nlinarith only [mul_self_le_mul_self (by positivity : 0 <= z / (t - 1)) hA]
  have hLogRemainder := Real.sub_log_one_add_bounds (z / (t - 1)) (by positivity)
  have hLogAbs : |Real.log (1 + z / (t - 1)) - z / (t - 1)| <=
      (z / (t - 1)) ^ 2 / 2 := by
    exact abs_le.mpr (And.intro (by linarith [hLogRemainder.2])
      (by nlinarith only [hLogRemainder.1, sq_nonneg (z / (t - 1))]))
  have hShift : |z / (t - 1) - z / t| <= 2 * z / t ^ 2 := by
    have hEq : z / (t - 1) - z / t = (z / t) * (1 / (t - 1)) := by
      field_simp ; ring
    rw [hEq, abs_of_nonneg (by positivity)]
    calc
      _ <= (z / t) * (2 / t) := mul_le_mul_of_nonneg_left hInv (by positivity)
      _ = _ := by ring
  have hLogError : |Real.log (1 + z / (t - 1)) - z / t| <=
      2 * (z + z ^ 2) / t ^ 2 := by
    calc
      _ <= |Real.log (1 + z / (t - 1)) - z / (t - 1)| +
          |z / (t - 1) - z / t| := abs_sub_le _ _ _
      _ <= (2 * z / t) ^ 2 / 2 + 2 * z / t ^ 2 := by
        exact add_le_add (hLogAbs.trans (div_le_div_of_nonneg_right hSq (by norm_num))) hShift
      _ = _ := by field_simp ; ring
  have hEq : nicolasTiltedKernel z t - z * nicolasTailKernel t =
      (z / ((t - 1) * (t - 1 + z)) - z / t ^ 2) / Real.log t +
        (Real.log (1 + z / (t - 1)) - z / t) / (t * (Real.log t) ^ 2) := by
    unfold nicolasTiltedKernel nicolasTailKernel
    field_simp
    ring
  rw [hEq]
  calc
    _ <= |(z / ((t - 1) * (t - 1 + z)) - z / t ^ 2) / Real.log t| +
        |(Real.log (1 + z / (t - 1)) - z / t) / (t * (Real.log t) ^ 2)| := abs_add_le _ _
    _ = |z / ((t - 1) * (t - 1 + z)) - z / t ^ 2| / Real.log t +
        |Real.log (1 + z / (t - 1)) - z / t| / (t * (Real.log t) ^ 2) := by
      rw [abs_div, abs_div, abs_of_pos hl, abs_of_pos (by positivity : 0 < t * (Real.log t) ^ 2)]
    _ <= (4 * z * (2 + z) / t ^ 3) / Real.log t +
        (2 * (z + z ^ 2) / t ^ 2) / (t * (Real.log t) ^ 2) := by
      exact add_le_add (div_le_div_of_nonneg_right hRational hl.le)
        (div_le_div_of_nonneg_right hLogError (by positivity))
    _ = 4 * z * (2 + z) / (t ^ 3 * Real.log t) +
        2 * (z + z ^ 2) / (t ^ 3 * (Real.log t) ^ 2) := by field_simp
    _ <= 4 * z * (2 + z) / (t ^ 3 * Real.log t) +
        2 * (z + z ^ 2) / (t ^ 3 * Real.log t) := by
      gcongr
      nlinarith only [hlog]
    _ <= 14 * (z + z ^ 2) / (t ^ 3 * Real.log t) := by
      rw [<- add_div]
      apply div_le_div_of_nonneg_right _ (by positivity)
      nlinarith only [hz, sq_nonneg z]

end PrimeFactorOscillations

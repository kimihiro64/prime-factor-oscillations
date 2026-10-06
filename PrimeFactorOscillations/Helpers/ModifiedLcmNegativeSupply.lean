/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.LcmNormalizedComparison
import PrimeFactorOscillations.Helpers.NicolasPowerPeak

/-!
# Integer negative Nicolas supply on the square-root scale

Only the actual Nicolas function is rounded. No floor invariance for the
modified-LCM construction is asserted or used.
-/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace PrimeFactorOscillations

open Filter Robin1984

theorem nicolasLog_integer_sqrt_negative_supply_of_not_RH
    (hNotRH : Not RiemannHypothesis) (N : Nat) :
    exists n : Nat, max N 3 <= n /\
      nicolasLogMertensOscillation (n : Real) * Real.sqrt (n : Real) < -1 := by
  choose b hb hbHalf hExc using exists_nicolasLog_two_sided_power_excursions_of_not_RH hNotRH
  choose x hx hFx using (hExc ((max N 3 : Nat) : Real) 2).2
  have hxBase : ((max N 3 : Nat) : Real) <= x := (le_max_left _ _).trans hx.le
  have hxThree : 3 < x := (le_max_right _ _).trans_lt hx
  have hxPos : 0 < x := by linarith
  let n : Nat := Nat.floor x
  have hnBase : max N 3 <= n := Nat.le_floor hxBase
  have hnThree : (3 : Real) <= n := by
    exact_mod_cast ((le_max_right N 3).trans hnBase)
  have hnPos : (0 : Real) < n := by linarith
  have hPow : x ^ (-(1 / 2 : Real)) <= x ^ (-b) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith : (1 : Real) <= x)
      (by linarith only [hbHalf])
  have hFloor : nicolasLogMertensOscillation (n : Real) =
      nicolasLogMertensOscillation x := by
    simpa only [n] using nicolasLogMertensOscillation_natFloor x
  have hHalf : 2 * x ^ (-(1 / 2 : Real)) < -nicolasLogMertensOscillation (n : Real) := by
    rw [hFloor]
    linarith only [hPow, hFx]
  have hNegative : 0 < -nicolasLogMertensOscillation (n : Real) :=
    (mul_pos (by norm_num : (0 : Real) < 2) (Real.rpow_pos_of_pos hxPos _)).trans hHalf
  have hxSucc : x < (n : Real) + 1 := by
    simpa only [n] using Nat.lt_floor_add_one x
  have hRoot : Real.sqrt x <= 2 * Real.sqrt (n : Real) := by
    calc
      Real.sqrt x <= Real.sqrt (4 * (n : Real)) :=
        Real.sqrt_le_sqrt (by linarith only [hxSucc, hnThree])
      _ = 2 * Real.sqrt (n : Real) := by
        rw [Real.sqrt_mul (by norm_num : (0 : Real) <= 4)]
        have hFour : Real.sqrt (4 : Real) = 2 := by
          simpa only [show (2 : Real) ^ 2 = 4 by norm_num] using
            Real.sqrt_sq (by norm_num : (0 : Real) <= 2)
        rw [hFour]
  have hCancel : x ^ (-(1 / 2 : Real)) * Real.sqrt x = 1 := by
    rw [Real.sqrt_eq_rpow, <- Real.rpow_add hxPos]
    norm_num
  have hScaled := mul_lt_mul_of_pos_right hHalf (Real.sqrt_pos.2 hxPos)
  have hTwo : 2 < -nicolasLogMertensOscillation (n : Real) * Real.sqrt x := by
    nlinarith only [hScaled, hCancel]
  have hComparison := mul_le_mul_of_nonneg_left hRoot hNegative.le
  exact Exists.intro n (And.intro hnBase (by nlinarith only [hTwo, hComparison]))

theorem modifiedLcm_negative_signed_supply_of_not_RH
    (hNotRH : Not RiemannHypothesis) (N : Nat) :
    exists n : Nat, N <= n /\
      nicolasLogMertensOscillation (n : Real) + modifiedLcmHeightCorrection n +
        lcmDefectSum (modifiedLcm n) < 0 := by
  have hRoot : Real.sqrt 2 + Real.sqrt 2 < (3 : Real) := by
    nlinarith only [Real.sq_sqrt (by norm_num : (0 : Real) <= 2),
      Real.sqrt_nonneg (2 : Real)]
  have hDU := (tendsto_modifiedLcm_heightCorrection_scaled.add
    tendsto_modifiedLcm_defect_scaled).eventually_lt_const hRoot
  have hLog : Filter.Tendsto (fun n : Nat => Real.log (n : Real))
      Filter.atTop Filter.atTop := by
    simpa only [Function.comp_def] using Real.tendsto_log_atTop.comp
      (tendsto_natCast_atTop_atTop :
        Filter.Tendsto (fun n : Nat => (n : Real)) Filter.atTop Filter.atTop)
  have hLogFour := hLog.eventually (Filter.eventually_gt_atTop (4 : Real))
  choose Y hY using Filter.eventually_atTop.mp (hDU.and hLogFour)
  choose n hn hF using nicolasLog_integer_sqrt_negative_supply_of_not_RH hNotRH (max N Y)
  have hnBase : max N Y <= n := (le_max_left _ _).trans hn
  have hnY : Y <= n := (le_max_right N Y).trans hnBase
  have hBounds := hY n hnY
  have hLogPos : 0 < Real.log (n : Real) := by linarith only [hBounds.2]
  have hScaled := mul_lt_mul_of_pos_right hF hLogPos
  have hAll :
      (nicolasLogMertensOscillation (n : Real) + modifiedLcmHeightCorrection n +
        lcmDefectSum (modifiedLcm n)) * Real.sqrt (n : Real) * Real.log (n : Real) < 0 := by
    nlinarith only [hScaled, hBounds.1, hBounds.2]
  refine Exists.intro n (And.intro ((le_max_left N Y).trans hnBase) ?_)
  by_contra hNot
  have hNonneg := mul_nonneg
    (mul_nonneg (le_of_not_gt hNot) (Real.sqrt_nonneg (n : Real))) hLogPos.le
  exact (not_lt_of_ge hNonneg) hAll

end PrimeFactorOscillations

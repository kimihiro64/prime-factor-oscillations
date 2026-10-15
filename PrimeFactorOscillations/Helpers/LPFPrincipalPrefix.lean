/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.LPFPrincipalLocalization
import PrimeFactorOscillations.Helpers.LPFPrincipalWeighted

/-!
# Pointwise principal prime-count input for the LPF distribution source

The complete degree-two weighted error is bounded using the verified 7/8
strip. Two-sided short-band localization then yields a 15/16 pointwise
power bound. No RH hypothesis is introduced. This is an analytic source
ingredient; it does not assert every-prime reachability of a generated orbit.
-/

set_option autoImplicit false
set_option Elab.async false


namespace Robin1984

/-- Every endpoint beyond x/2 fits one common principal-error allowance. -/
theorem lpfPrincipalWeightedError_endpoint_allowance
    {x t : Real} (hx : 4 <= x) (hLog : 2 <= Real.log x) (ht : x / 2 <= t) :
    abs (robinPsiWeightedErrorIntegral 2 t) <=
      8 * lpfPrincipalSmoothedConstant *
        x ^ (-(9 / 8 : Real)) * Inv.inv (Real.log x) := by
  have hxPos : 0 < x := by linarith only [hx]
  have htTwo : 2 <= t := by linarith only [hx, ht]
  have htPos : 0 < t := by linarith only [htTwo]
  have hLogTwo : Real.log 2 <= 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : Real) < 2)
    linarith only [h]
  have hLogSum : Real.log x <= Real.log 2 + Real.log t := by
    have h := Real.log_le_log hxPos (by linarith only [ht] : x <= 2 * t)
    rw [Real.log_mul (by norm_num : Not ((2 : Real) = 0)) (ne_of_gt htPos)] at h
    exact h
  have hLt : 1 <= Real.log t := by linarith only [hLog, hLogTwo, hLogSum]
  have hLxPos : 0 < Real.log x := by linarith only [hLog]
  have hLtPos : 0 < Real.log t := by linarith only [hLt]
  have hTwoPower : (2 : Real) ^ (9 / 8 : Real) <= 4 := by
    have h := Real.rpow_le_rpow_of_exponent_le
      (by norm_num : (1 : Real) <= 2) (by norm_num : (9 / 8 : Real) <= 2)
    norm_num only [Real.rpow_two] at h
    exact h
  have hPow : x ^ (9 / 8 : Real) <= 4 * t ^ (9 / 8 : Real) := by
    calc
      _ <= (2 * t) ^ (9 / 8 : Real) :=
        Real.rpow_le_rpow hxPos.le (by linarith only [ht]) (by norm_num)
      _ = (2 : Real) ^ (9 / 8 : Real) * t ^ (9 / 8 : Real) :=
        Real.mul_rpow (by norm_num) htPos.le
      _ <= _ := mul_le_mul_of_nonneg_right hTwoPower (Real.rpow_nonneg htPos.le _)
  have hInvPow := one_div_le_one_div_of_le
    (Real.rpow_pos_of_pos hxPos (9 / 8 : Real)) hPow
  have hInvPowFour := mul_le_mul_of_nonneg_left hInvPow (by norm_num : (0 : Real) <= 4)
  have hCancelFour :
      (4 : Real) * (1 / (4 * t ^ (9 / 8 : Real))) = 1 / t ^ (9 / 8 : Real) := by
    field_simp
  rw [hCancelFour] at hInvPowFour
  have hPower : t ^ (-(9 / 8 : Real)) <= 4 * x ^ (-(9 / 8 : Real)) := by
    rw [Real.rpow_neg htPos.le, Real.rpow_neg hxPos.le]
    simpa only [one_div] using hInvPowFour
  have hLogDouble : Real.log x <= 2 * Real.log t := by
    linarith only [hLog, hLogTwo, hLogSum]
  have hInvLog := one_div_le_one_div_of_le hLxPos hLogDouble
  have hInvLogTwo := mul_le_mul_of_nonneg_left hInvLog (by norm_num : (0 : Real) <= 2)
  have hCancelTwo :
      (2 : Real) * (1 / (2 * Real.log t)) = 1 / Real.log t := by
    field_simp
  rw [hCancelTwo] at hInvLogTwo
  have hLogInv : Inv.inv (Real.log t) <= 2 * Inv.inv (Real.log x) := by
    simpa only [one_div] using hInvLogTwo
  have hC : 0 <= lpfPrincipalSmoothedConstant := lpfPrincipalSmoothedConstant_pos.le
  calc
    _ <= lpfPrincipalSmoothedConstant * t ^ (-(9 / 8 : Real)) *
        Inv.inv (Real.log t) := abs_robinPsiWeightedError_two_le_seven_eighths htTwo hLt
    _ <= lpfPrincipalSmoothedConstant * (4 * x ^ (-(9 / 8 : Real))) *
        (2 * Inv.inv (Real.log x)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hPower hC) hLogInv
        (inv_nonneg.mpr hLtPos.le) (by positivity)
    _ = _ := by ring

noncomputable def lpfPrincipalPointwiseConstant : Real :=
  1 + 32 * lpfPrincipalSmoothedConstant

theorem lpfPrincipalPointwiseConstant_pos : 0 < lpfPrincipalPointwiseConstant := by
  have hC := lpfPrincipalSmoothedConstant_pos
  unfold lpfPrincipalPointwiseConstant
  positivity

/-- A genuine pointwise principal prime-count bound, with no RH hypothesis. -/
theorem abs_psi_sub_self_le_fifteen_sixteenths
    {x : Real} (hx : 65536 <= x) (hLog : 2 <= Real.log x) :
    abs (Chebyshev.psi x - x) <=
      lpfPrincipalPointwiseConstant * x ^ (15 / 16 : Real) := by
  have hxPos : 0 < x := by linarith only [hx]
  let H : Real := x ^ (15 / 16 : Real)
  let R : Real := 8 * lpfPrincipalSmoothedConstant *
    x ^ (-(9 / 8 : Real)) * Inv.inv (Real.log x)
  have hH : 0 < H := Real.rpow_pos_of_pos hxPos _
  have hRoot : (2 : Real) <= x ^ (1 / 16 : Real) := by
    have h := Real.rpow_le_rpow (by norm_num : (0 : Real) <= 65536)
      hx (by norm_num : (0 : Real) <= 1 / 16)
    have hBase : (65536 : Real) ^ (1 / 16 : Real) = 2 := by
      rw [show (65536 : Real) = 2 ^ (16 : Nat) by norm_num,
        <- Real.rpow_natCast, <- Real.rpow_mul (by norm_num : (0 : Real) <= 2)]
      norm_num
    rw [hBase] at h
    exact h
  have h2H : 2 * H <= x := by
    calc
      _ <= x ^ (1 / 16 : Real) * H := mul_le_mul_of_nonneg_right hRoot hH.le
      _ = x := by
        dsimp [H]
        rw [<- Real.rpow_add hxPos]
        norm_num
  have hLow : 1 < x - H := by linarith only [hx, h2H]
  have hR : 0 <= R := by
    have hC := lpfPrincipalSmoothedConstant_pos
    have hLogPos : 0 < Real.log x := by linarith only [hLog]
    dsimp [R]
    positivity
  have hxFour : 4 <= x := by linarith only [hx]
  have hEa : abs (robinPsiWeightedErrorIntegral 2 (x - H)) <= R :=
    lpfPrincipalWeightedError_endpoint_allowance hxFour hLog (by linarith only [h2H])
  have hEx : abs (robinPsiWeightedErrorIntegral 2 x) <= R :=
    lpfPrincipalWeightedError_endpoint_allowance hxFour hLog (by linarith only [hxPos])
  have hEb : abs (robinPsiWeightedErrorIntegral 2 (x + H)) <= R :=
    lpfPrincipalWeightedError_endpoint_allowance hxFour hLog (by linarith only [hxPos, hH])
  have hBand := PrimeFactorOscillations.nicolasDegree_two_local_error
    hLow hH.le h2H hR hEa hEx hEb
  have hHsq : H ^ 2 = x ^ (15 / 8 : Real) := by
    dsimp [H]
    rw [<- Real.rpow_natCast, <- Real.rpow_mul hxPos.le]
    norm_num
  have hPowerProduct : x ^ (3 : Nat) * x ^ (-(9 / 8 : Real)) = x ^ (15 / 8 : Real) := by
    rw [<- Real.rpow_natCast, <- Real.rpow_add hxPos]
    norm_num
  have hLogCancel : Real.log x * Inv.inv (Real.log x) = 1 := by
    have hLogPos : 0 < Real.log x := by linarith only [hLog]
    field_simp
  have hBudget : 4 * x ^ 3 * Real.log x * R =
      32 * lpfPrincipalSmoothedConstant * H ^ 2 := by
    dsimp [R]
    calc
      _ = 32 * lpfPrincipalSmoothedConstant *
          (x ^ 3 * x ^ (-(9 / 8 : Real))) *
          (Real.log x * Inv.inv (Real.log x)) := by ring
      _ = _ := by rw [hPowerProduct, hLogCancel, mul_one, hHsq]
  rw [hBudget] at hBand
  have hScaled : abs (Chebyshev.psi x - x) * H <=
      (lpfPrincipalPointwiseConstant * H) * H := by
    dsimp [lpfPrincipalPointwiseConstant]
    nlinarith only [hBand]
  exact le_of_mul_le_mul_right hScaled hH


/-- The cutoffs in the pointwise theorem give an actual eventual estimate. -/
theorem eventually_abs_psi_sub_self_le_fifteen_sixteenths :
    Filter.Eventually (fun x : Real =>
      abs (Chebyshev.psi x - x) <=
        lpfPrincipalPointwiseConstant * x ^ (15 / 16 : Real)) Filter.atTop := by
  filter_upwards [Filter.eventually_ge_atTop (65536 : Real),
    Filter.eventually_ge_atTop (Real.exp 2)] with x hx hExp
  have hLog : 2 <= Real.log x := by
    have h := Real.log_le_log (Real.exp_pos 2) hExp
    rw [Real.log_exp] at h
    exact h
  exact abs_psi_sub_self_le_fifteen_sixteenths hx hLog

end Robin1984

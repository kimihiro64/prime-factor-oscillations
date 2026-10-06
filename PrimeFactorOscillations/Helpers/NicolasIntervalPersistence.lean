/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.NicolasDiscretePeak
import PrimeFactorOscillations.Mathlib.Analysis.SpecialFunctions.Log.SignedIteratedRemainder

/-!
# A finite lower envelope for the Nicolas logarithmic error

An absolute theta-error bound on a whole interval controls the loss in the
signed tail integral and in the logarithmic Taylor remainder. The nonnegative
Euler tail is retained with its correct sign. No Riemann hypothesis is used.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

open Filter MeasureTheory Set Robin1984

/-- A peak of the signed tail survives up to the displayed integral and
quadratic losses whenever theta stays within the given absolute envelope. -/
theorem nicolasLog_interval_lower_bound
    (x y M : Real) (hx : 4 <= x) (hLog : 1 <= Real.log (x / 2))
    (hxy : x <= y) (hM : 0 <= M) (hSmall : M <= x / 2)
    (hError : forall t : Real, x <= t -> t <= y ->
      abs (Chebyshev.theta t - t) <= M) :
    nicolasK x -
      (2 * M * (y - x) + 6 * M ^ (2 : Nat)) /
        (x ^ (2 : Nat) * Real.log x) <= nicolasLogMertensOscillation y := by
  have hxPos : 0 < x := by linarith
  have hLogX : 1 <= Real.log x :=
    hLog.trans (Real.log_le_log (by positivity) (by linarith : x / 2 <= x))
  have hLxPos : 0 < Real.log x := by linarith
  have hDen : 0 < x ^ (2 : Nat) * Real.log x := by positivity
  have hKernel : forall t : Real, x <= t ->
      0 <= (1 / Real.log t + 1 / (Real.log t) ^ 2) / t ^ 2 /\
      (1 / Real.log t + 1 / (Real.log t) ^ 2) / t ^ 2 <=
        2 / (x ^ (2 : Nat) * Real.log x) := by
    intro t ht
    have htPos : 0 < t := hxPos.trans_le ht
    have hLogs : Real.log x <= Real.log t := Real.log_le_log hxPos ht
    have hLt : 1 <= Real.log t := hLogX.trans hLogs
    have hLtPos : 0 < Real.log t := by linarith
    have hInv : 1 / (Real.log t) ^ 2 <= 1 / Real.log t :=
      div_le_div_of_nonneg_left (by norm_num) hLtPos (by nlinarith)
    have hSquares : x ^ (2 : Nat) <= t ^ (2 : Nat) := by nlinarith
    have hDenom : x ^ (2 : Nat) * Real.log x <= t ^ (2 : Nat) * Real.log t :=
      mul_le_mul hSquares hLogs hLxPos.le (sq_nonneg t)
    refine And.intro (by positivity) ?_
    calc
      _ <= (2 / Real.log t) / t ^ 2 :=
        div_le_div_of_nonneg_right (calc
          1 / Real.log t + 1 / (Real.log t) ^ 2 <=
              1 / Real.log t + 1 / Real.log t := add_le_add le_rfl hInv
          _ = 2 / Real.log t := by ring) (sq_nonneg t)
      _ = 2 / (t ^ (2 : Nat) * Real.log t) := by ring
      _ <= 2 / (x ^ (2 : Nat) * Real.log x) :=
        div_le_div_of_nonneg_left (by norm_num) hDen hDenom
  have hIntegral := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := x) (b := y) (C := 2 * M / (x ^ (2 : Nat) * Real.log x))
    (f := fun t : Real => (Chebyshev.theta t - t) *
      ((1 / Real.log t + 1 / (Real.log t) ^ 2) / t ^ 2)) (fun t ht => by
        rw [uIoc_of_le hxy] at ht
        have hk := hKernel t ht.1.le
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hk.1]
        calc
          _ <= M * (2 / (x ^ (2 : Nat) * Real.log x)) :=
            mul_le_mul (hError t ht.1.le ht.2) hk.2 hk.1 hM
          _ = _ := by ring)
  have hK : abs (nicolasK x - nicolasK y) <=
      2 * M * (y - x) / (x ^ (2 : Nat) * Real.log x) := by
    rw [nicolasK_sub_eq_intervalIntegral (by linarith) hxy]
    convert hIntegral using 1 <;>
      simp only [abs_of_nonneg (sub_nonneg.mpr hxy)] <;> ring
  have hyPos : 0 < y := hxPos.trans_le hxy
  have hEy := hError y hxy le_rfl
  have hEyBoth := abs_le.mp hEy
  have hThetaHalf : x / 2 <= Chebyshev.theta y := by linarith
  have hThetaOne : 1 < Chebyshev.theta y := by linarith
  have hLogY : 1 <= Real.log y := hLogX.trans (Real.log_le_log hxPos hxy)
  have hLogTheta : 1 <= Real.log (Chebyshev.theta y) :=
    hLog.trans (Real.log_le_log (by positivity) hThetaHalf)
  have hHeight : y <= 2 * Chebyshev.theta y := by linarith
  have hTaylor := Real.logLog_remainder_abs_le
    (by linarith : (1 : Real) < y) hThetaOne hLogY hLogTheta hHeight
  have hSquare : (Chebyshev.theta y - y) ^ (2 : Nat) <= M ^ (2 : Nat) := by
    have h := mul_self_le_mul_self (abs_nonneg (Chebyshev.theta y - y)) hEy
    simpa only [<- pow_two, sq_abs] using h
  have hDenom : x ^ (2 : Nat) * Real.log x <= y ^ (2 : Nat) * Real.log y :=
    mul_le_mul (by nlinarith : x ^ (2 : Nat) <= y ^ (2 : Nat))
      (Real.log_le_log hxPos hxy) hLxPos.le (sq_nonneg y)
  have hT : (Chebyshev.theta y - y) / (y * Real.log y) -
      (Real.log (Real.log (Chebyshev.theta y)) - Real.log (Real.log y)) <=
      6 * M ^ (2 : Nat) / (x ^ (2 : Nat) * Real.log x) := by
    apply (le_abs_self _).trans
    apply hTaylor.trans
    calc
      _ <= 6 * M ^ (2 : Nat) / (y ^ (2 : Nat) * Real.log y) :=
        div_le_div_of_nonneg_right (by linarith)
          (mul_nonneg (sq_nonneg y) (by linarith))
      _ <= _ := div_le_div_of_nonneg_left (by positivity) hDen hDenom
  have hEuler := nicolasMertensSummandRemainder_nonneg y
  rw [nicolasLogMertensOscillation_eq_components (by linarith : (3 : Real) <= y)]
  have hKLower := (abs_le.mp hK).2
  have hExpand :
      (2 * M * (y - x) + 6 * M ^ (2 : Nat)) / (x ^ (2 : Nat) * Real.log x) =
        2 * M * (y - x) / (x ^ (2 : Nat) * Real.log x) +
        6 * M ^ (2 : Nat) / (x ^ (2 : Nat) * Real.log x) := by ring
  rw [hExpand]
  dsimp only [nicolasThetaError]
  linarith only [hKLower, hT, hEuler]

end PrimeFactorOscillations


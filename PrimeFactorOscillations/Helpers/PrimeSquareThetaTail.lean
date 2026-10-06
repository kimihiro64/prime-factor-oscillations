/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.NicolasQuantitativeClock
import PrimeFactorOscillations.Helpers.Robin1984.Equivalence.WeightedKernelBounds
import PrimeFactorOscillations.Helpers.Robin1984.NicolasLandau.WeightedPrimePowerTail
import PrimeFactorOscillations.Mathlib.NumberTheory.Chebyshev.PrimeReciprocalSquare

/-!
# Prime-square theta tail and its leading term

The unconditional PNT transfers through the existing real Robin kernel.
The complete theta-weighted inverse-square tail has scaled limit two;
subtracting its endpoint term will produce the reciprocal-prime-square tail.
-/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace PrimeFactorOscillations
open Filter MeasureTheory Set Robin1984

def primeSquareThetaTail (x : Real) : Real :=
  integral (volume.restrict (Ioi x)) (fun t : Real => Chebyshev.theta t * robinRealWeight 2 t)

theorem integrableOn_theta_weight_two :
    IntegrableOn (fun t : Real => Chebyshev.theta t * robinRealWeight 2 t) (Ioi 2) := by
  choose C hC hB using exists_thetaError_bound_div_log_sq
  let M : Real := 1 + C / (Real.log 2) ^ (2 : Nat)
  have hM : 0 <= M := by dsimp [M]; positivity
  have hMain : IntegrableOn (fun t : Real => t * robinRealWeight 2 t) (Ioi 2) := by
    simpa only [Real.rpow_one] using
      (integrableOn_rpow_mul_robinRealWeight (n := 2) (r := (1 : Real))
        (by norm_num : (1 : Real) < 2) (by norm_num))
  apply Integrable.mono' (hMain.const_mul M)
  . have hm : Measurable (fun t : Real => Chebyshev.theta t * robinRealWeight 2 t) := by
      unfold robinRealWeight
      exact Chebyshev.theta_mono.measurable.mul (by fun_prop)
    exact hm.aestronglyMeasurable
  . filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht2 : 2 <= t := ht.le
    have ht0 : 0 < t := by linarith
    have hw := robinRealWeight_nonneg (n := 2) (by linarith : (1 : Real) < t)
    have hl2 : 0 < Real.log (2 : Real) := Real.log_pos (by norm_num)
    have hlog := Real.log_le_log (by norm_num : (0 : Real) < 2) ht2
    have hsq : (Real.log 2) ^ (2 : Nat) <= (Real.log t) ^ (2 : Nat) := by nlinarith
    have he : Chebyshev.theta t - t <= C * t / (Real.log 2) ^ (2 : Nat) :=
      ((le_abs_self _).trans (hB t ht2)).trans
        (div_le_div_of_nonneg_left (mul_nonneg hC ht0.le) (sq_pos_of_pos hl2) hsq)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Chebyshev.theta_nonneg t) hw)]
    calc
      _ <= (M * t) * robinRealWeight 2 t := mul_le_mul_of_nonneg_right
        (by
          dsimp [M]
          have hid : C * t / (Real.log 2) ^ (2 : Nat) =
              (C / (Real.log 2) ^ (2 : Nat)) * t := by ring
          rw [hid] at he
          nlinarith) hw
      _ = _ := by ring

theorem primeSquareThetaTail_integrable {x : Real} (hx : 2 <= x) :
    IntegrableOn (fun t : Real => Chebyshev.theta t * robinRealWeight 2 t) (Ioi x) :=
  integrableOn_theta_weight_two.mono_set (Ioi_subset_Ioi hx)

theorem tendsto_weightTwo_linear_kernel_scaled :
    Tendsto (fun x : Real => (robinZeroKernel 2 (1 : Complex) x).re *
      (x * Real.log x)) atTop (nhds 2) := by
  have hInv : Tendsto (fun x : Real => 1 / Real.log x) atTop (nhds 0) := by
    simpa only [one_div, Function.comp_def] using
      tendsto_inv_atTop_zero.comp Real.tendsto_log_atTop
  have hErr : Tendsto (fun x : Real =>
      (robinZeroKernel 2 (1 : Complex) x).re * (x * Real.log x) - 2)
      atTop (nhds 0) := by
    apply squeeze_zero_norm' (a := fun x : Real => 1 / Real.log x) ?_ hInv
    filter_upwards [eventually_ge_atTop (2 : Real)] with x hx
    have hx1 : 1 < x := by linarith
    have hx0 : 0 < x := by linarith
    have hl : 0 < Real.log x := Real.log_pos hx1
    have hEq := robinZeroKernel_ofReal_eq_main_add_signed_tail 2
      (r := (1 : Real)) (by norm_num) hx1
    have hLo := robinCpowLogTail_ofReal_re_nonneg (-1) 2 hx1
    have hHi := robinCpowLogTail_ofReal_re_le (a := (-1 : Real)) (by norm_num) 2 hx1
    norm_num [Real.rpow_neg_one] at hEq hLo hHi
    have hid : (robinZeroKernel 2 (1 : Complex) x).re * (x * Real.log x) - 2 =
        -(robinCpowLogTail (-1 : Complex) 2 x).re * (x * Real.log x) := by
      rw [hEq]
      field_simp
      <;> ring
    rw [hid, Real.norm_eq_abs, abs_mul, abs_neg,
      abs_of_nonneg hLo, abs_of_pos (mul_pos hx0 hl)]
    calc
      _ <= (Inv.inv x * Inv.inv ((Real.log x) ^ (2 : Nat))) *
          (x * Real.log x) := mul_le_mul_of_nonneg_right hHi (by positivity)
      _ = _ := by field_simp
  have h := hErr.add_const (2 : Real)
  simpa only [sub_add_cancel, zero_add] using h

theorem eventually_primeSquareThetaTail_relative_error
    (epsilon : Real) (he : 0 < epsilon) :
    Filter.Eventually (fun x : Real =>
      abs (primeSquareThetaTail x - (robinZeroKernel 2 (1 : Complex) x).re) <=
        epsilon * (robinZeroKernel 2 (1 : Complex) x).re) atTop := by
  have hRatio : Tendsto (fun t : Real => Chebyshev.theta t / t) atTop (nhds (1 : Real)) :=
    (Asymptotics.isEquivalent_iff_tendsto_one
      (eventually_ne_atTop (0 : Real))).mp primeProfile_theta_isEquivalent_id
  choose X hX using Metric.tendsto_atTop.mp hRatio epsilon he
  filter_upwards [eventually_ge_atTop (max X 2)] with x hx
  have hx2 : 2 <= x := (le_max_right _ _).trans hx
  have hx1 : 1 < x := by linarith
  have hMain : IntegrableOn (fun t : Real => t * robinRealWeight 2 t) (Ioi x) := by
    simpa only [Real.rpow_one] using
      (integrableOn_rpow_mul_robinRealWeight (n := 2) (r := (1 : Real)) hx1 (by norm_num))
  have hKernel : integral (volume.restrict (Ioi x)) (fun t : Real =>
      t * robinRealWeight 2 t) = (robinZeroKernel 2 (1 : Complex) x).re := by
    simpa only [Real.rpow_one, Complex.ofReal_one] using
      integral_rpow_mul_robinRealWeight 2 (1 : Real) hx1
  have hError : primeSquareThetaTail x - (robinZeroKernel 2 (1 : Complex) x).re =
      integral (volume.restrict (Ioi x)) (fun t : Real =>
        (Chebyshev.theta t - t) * robinRealWeight 2 t) := by
    rw [primeSquareThetaTail, <- hKernel, <- integral_sub
      (primeSquareThetaTail_integrable hx2) hMain]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    ring
  have hb := norm_integral_le_of_norm_le (hMain.const_mul epsilon)
    (show Filter.Eventually (fun t : Real =>
      norm ((Chebyshev.theta t - t) * robinRealWeight 2 t) <=
        epsilon * (t * robinRealWeight 2 t)) (ae (volume.restrict (Ioi x))) from by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have hxt : x < t := ht
      have ht0 : 0 < t := by linarith
      have hw := robinRealWeight_nonneg (n := 2) (by linarith : (1 : Real) < t)
      have hClose := hX t (((le_max_left _ _).trans hx).trans ht.le)
      rw [Real.dist_eq] at hClose
      have hid : Chebyshev.theta t - t = (Chebyshev.theta t / t - 1) * t := by
        field_simp
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hw, hid, abs_mul, abs_of_pos ht0]
      have hm := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hClose.le ht0.le) hw
      simpa only [mul_assoc] using hm)
  rw [integral_const_mul, hKernel, Real.norm_eq_abs] at hb
  rw [hError]
  exact hb

theorem tendsto_primeSquareThetaTail_scaled :
    Tendsto (fun x : Real => primeSquareThetaTail x * (x * Real.log x))
      atTop (nhds 2) := by
  apply Metric.tendsto_atTop.mpr
  intro epsilon he
  choose X hX using Metric.tendsto_atTop.mp tendsto_weightTwo_linear_kernel_scaled
    (epsilon / 2) (by positivity)
  have hErr := eventually_primeSquareThetaTail_relative_error (epsilon / 6) (by positivity)
  have hThree := tendsto_weightTwo_linear_kernel_scaled.eventually_lt_const
    (by norm_num : (2 : Real) < 3)
  apply eventually_atTop.mp
  filter_upwards [hErr, hThree, eventually_ge_atTop (max X 2)] with x heX h3 hx
  have hx2 : 2 <= x := (le_max_right _ _).trans hx
  have hs : 0 < x * Real.log x := mul_pos (by linarith) (Real.log_pos (by linarith))
  have hClose := hX x ((le_max_left _ _).trans hx)
  rw [Real.dist_eq] at hClose
  have hError : abs ((primeSquareThetaTail x - (robinZeroKernel 2 (1 : Complex) x).re) *
      (x * Real.log x)) < epsilon / 2 := by
    rw [abs_mul, abs_of_pos hs]
    calc
      _ <= (epsilon / 6 * (robinZeroKernel 2 (1 : Complex) x).re) *
          (x * Real.log x) := mul_le_mul_of_nonneg_right heX hs.le
      _ < epsilon / 2 := by nlinarith
  have hTriangle := abs_sub_le (primeSquareThetaTail x * (x * Real.log x))
    ((robinZeroKernel 2 (1 : Complex) x).re * (x * Real.log x)) 2
  rw [<- sub_mul] at hTriangle
  rw [Real.dist_eq]
  linarith

end PrimeFactorOscillations

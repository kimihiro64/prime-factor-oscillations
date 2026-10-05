/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.NicolasPrimeSquareBias
import PrimeFactorOscillations.Helpers.PrimeProfileThetaClock

/-!
# The unconditional leading prime-power tail

The pinned prime number theorem controls the full psi-square tail. The
higher-power correction is retained and negligible at the square-root scale.
No Riemann-hypothesis assumption is used.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

open Asymptotics Filter MeasureTheory Set Robin1984

theorem nicolasPsi_isEquivalent_id :
    Asymptotics.IsEquivalent atTop Chebyshev.psi (fun x : Real => x) := by
  choose c hc hmedium using MediumPNT
  have ht : Tendsto (fun x : Real => Real.log x ^ ((1 : Real) / 10)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : Real) < 1 / 10)).comp Real.tendsto_log_atTop
  have hdecay : Tendsto
      (fun x : Real => Real.exp (-c * Real.log x ^ ((1 : Real) / 10)))
      atTop (nhds (0 : Real)) := by
    simpa only [Function.comp_def, neg_mul] using
      Real.tendsto_exp_neg_atTop_nhds_zero.comp (ht.const_mul_atTop hc)
  have hLittle : Asymptotics.IsLittleO atTop
      (fun x : Real => Real.exp (-c * Real.log x ^ ((1 : Real) / 10)))
      (fun _ : Real => (1 : Real)) :=
    (Asymptotics.isLittleO_one_iff Real).mpr hdecay
  change Asymptotics.IsLittleO atTop (Chebyshev.psi - (fun x : Real => x))
    (fun x : Real => x)
  apply hmedium.trans_isLittleO
  simpa only [mul_one] using
    (Asymptotics.isBigO_refl (fun x : Real => x) atTop).mul_isLittleO hLittle

theorem tendsto_nicolasPsi_ratio :
    Tendsto (fun x : Real => Chebyshev.psi x / x) atTop (nhds 1) := by
  exact (Asymptotics.isEquivalent_iff_tendsto_one (eventually_ne_atTop (0 : Real))).mp
    nicolasPsi_isEquivalent_id

theorem tendsto_nicolasHalfKernel_scaled :
    Tendsto (fun x : Real =>
      (robinZeroKernel 1 (1 / 2 : Complex) x).re *
        (x ^ (1 / 2 : Real) * Real.log x)) atTop (nhds 2) := by
  have hInv : Tendsto (fun x : Real => Inv.inv (Real.log x)) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp Real.tendsto_log_atTop
  have hSmall : Tendsto (fun x : Real =>
      2 * (Inv.inv (Real.log x) + 4 * (Inv.inv (Real.log x)) ^ 2))
      atTop (nhds 0) := by
    have h : Tendsto (fun x : Real =>
        2 * (Inv.inv (Real.log x) + 4 * (Inv.inv (Real.log x)) ^ 2))
        atTop (nhds ((2 : Real) * (0 + 4 * 0 ^ 2))) :=
      tendsto_const_nhds.mul (hInv.add (tendsto_const_nhds.mul (hInv.pow 2)))
    simpa using h
  apply Metric.tendsto_atTop.mpr
  intro epsilon hEpsilon
  apply eventually_atTop.mp
  filter_upwards [hSmall.eventually_lt_const hEpsilon, eventually_ge_atTop (4 : Real)]
    with x he hx
  have hx1 : 1 < x := by linarith
  have hx0 : 0 < x := by linarith
  have hl : 0 < Real.log x := Real.log_pos hx1
  have hr : 0 < x ^ (1 / 2 : Real) := Real.rpow_pos_of_pos hx0 _
  let s := x ^ (1 / 2 : Real) * Real.log x
  have hs : 0 < s := mul_pos hr hl
  have hCancel : x ^ (-(1 / 2 : Real)) * Inv.inv (Real.log x) * s = 1 := by
    dsimp [s]
    rw [Real.rpow_neg hx0.le]
    field_simp
  have hArg : ((robinZeroKernel 1 (1 / 2 : Complex) x).re -
      2 * x ^ (-(1 / 2 : Real)) * Inv.inv (Real.log x)) * s =
      (robinZeroKernel 1 (1 / 2 : Complex) x).re * s - 2 := by
    nlinarith only [hCancel]
  have hScale : 2 * nicolasSpectralRemainderScale x * s =
      2 * (Inv.inv (Real.log x) + 4 * (Inv.inv (Real.log x)) ^ 2) := by
    dsimp [nicolasSpectralRemainderScale, s]
    rw [Real.rpow_neg hx0.le]
    field_simp
  have h := mul_le_mul_of_nonneg_right (nicolasHalfKernel_explicit_error hx1) hs.le
  rw [hScale] at h
  rw [Real.dist_eq]
  change |(robinZeroKernel 1 (1 / 2 : Complex) x).re * s - 2| < epsilon
  rw [<- hArg, abs_mul, abs_of_pos hs]
  exact h.trans_lt he

theorem eventually_nicolasPsiSquareTail_relative_error
    (epsilon : Real) (hEpsilon : 0 < epsilon) :
    Filter.Eventually (fun x : Real =>
      |nicolasPsiRootTail 2 x - (robinZeroKernel 1 (1 / 2 : Complex) x).re| <=
        epsilon * (robinZeroKernel 1 (1 / 2 : Complex) x).re) atTop := by
  have hRootRatio : Tendsto (fun t : Real =>
      Chebyshev.psi (t ^ (1 / 2 : Real)) / t ^ (1 / 2 : Real))
      atTop (nhds 1) :=
    tendsto_nicolasPsi_ratio.comp (tendsto_rpow_atTop (by norm_num : (0 : Real) < 1 / 2))
  choose X hX using Metric.tendsto_atTop.mp hRootRatio epsilon hEpsilon
  filter_upwards [eventually_ge_atTop (max X 4)] with x hx
  have hx4 : 4 <= x := (le_max_right X 4).trans hx
  have hx1 : 1 < x := by linarith
  have hMain : IntegrableOn (fun t : Real =>
      t ^ (1 / 2 : Real) * robinRealWeight 1 t) (Ioi x) :=
    integrableOn_rpow_mul_robinRealWeight hx1 (by norm_num)
  have hPsi : IntegrableOn (fun t : Real =>
      Chebyshev.psi (t ^ (1 / 2 : Real)) * robinRealWeight 1 t) (Ioi x) := by
    simpa only [Nat.cast_ofNat, inv_eq_one_div] using
      integrableOn_psi_root_mul_robinRealWeight (n := 1) (k := 2)
        (by norm_num) (by norm_num) hx1
  have hKernel : integral (volume.restrict (Ioi x)) (fun t : Real =>
      t ^ (1 / 2 : Real) * robinRealWeight 1 t) =
      (robinZeroKernel 1 (1 / 2 : Complex) x).re := by
    simpa only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat] using
      integral_rpow_mul_robinRealWeight 1 (1 / 2 : Real) hx1
  have hPsiEq : nicolasPsiRootTail 2 x = integral (volume.restrict (Ioi x))
      (fun t : Real => Chebyshev.psi (t ^ (1 / 2 : Real)) * robinRealWeight 1 t) := by
    simp only [nicolasPsiRootTail, Nat.cast_ofNat, inv_eq_one_div]
  have hErrorEq : nicolasPsiRootTail 2 x - (robinZeroKernel 1 (1 / 2 : Complex) x).re =
      integral (volume.restrict (Ioi x)) (fun t : Real =>
        (Chebyshev.psi (t ^ (1 / 2 : Real)) - t ^ (1 / 2 : Real)) * robinRealWeight 1 t) := by
    rw [hPsiEq, <- hKernel, <- integral_sub hPsi hMain]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t _
    ring
  have hBound := norm_integral_le_of_norm_le (hMain.const_mul epsilon)
    (show Filter.Eventually (fun t : Real =>
      norm ((Chebyshev.psi (t ^ (1 / 2 : Real)) - t ^ (1 / 2 : Real)) *
        robinRealWeight 1 t) <= epsilon * (t ^ (1 / 2 : Real) * robinRealWeight 1 t))
        (ae (volume.restrict (Ioi x))) from by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have ht1 : 1 < t := hx1.trans ht
      have ht0 : 0 < t := zero_lt_one.trans ht1
      have hr : 0 < t ^ (1 / 2 : Real) := Real.rpow_pos_of_pos ht0 _
      have hw : 0 <= robinRealWeight 1 t := robinRealWeight_nonneg ht1
      have hClose := hX t (((le_max_left X 4).trans hx).trans ht.le)
      rw [Real.dist_eq] at hClose
      have hIdentity : Chebyshev.psi (t ^ (1 / 2 : Real)) - t ^ (1 / 2 : Real) =
          (Chebyshev.psi (t ^ (1 / 2 : Real)) / t ^ (1 / 2 : Real) - 1) *
            t ^ (1 / 2 : Real) := by field_simp
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hw, hIdentity, abs_mul, abs_of_pos hr]
      have h := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hClose.le hr.le) hw
      simpa only [mul_assoc] using h)
  rw [integral_const_mul, hKernel, Real.norm_eq_abs] at hBound
  rw [hErrorEq]
  exact hBound

theorem tendsto_nicolasPsiSquareTail_scaled :
    Tendsto (fun x : Real =>
      nicolasPsiRootTail 2 x * (x ^ (1 / 2 : Real) * Real.log x)) atTop (nhds 2) := by
  apply Metric.tendsto_atTop.mpr
  intro epsilon hEpsilon
  choose X hX using Metric.tendsto_atTop.mp tendsto_nicolasHalfKernel_scaled
    (epsilon / 2) (by positivity)
  have hSmall := eventually_nicolasPsiSquareTail_relative_error (epsilon / 6) (by positivity)
  have hThree := tendsto_nicolasHalfKernel_scaled.eventually_lt_const
    (by norm_num : (2 : Real) < 3)
  apply eventually_atTop.mp
  filter_upwards [hSmall, hThree, eventually_ge_atTop (max X 4)] with x he hthree hx
  have hx4 : 4 <= x := (le_max_right X 4).trans hx
  have hx1 : 1 < x := by linarith
  have hx0 : 0 < x := by linarith
  let s := x ^ (1 / 2 : Real) * Real.log x
  have hs : 0 < s := mul_pos (Real.rpow_pos_of_pos hx0 _) (Real.log_pos hx1)
  have hClose := hX x ((le_max_left X 4).trans hx)
  rw [Real.dist_eq] at hClose
  change (robinZeroKernel 1 (1 / 2 : Complex) x).re * s < 3 at hthree
  have hError : |(nicolasPsiRootTail 2 x - (robinZeroKernel 1 (1 / 2 : Complex) x).re) * s| <
      epsilon / 2 := by
    rw [abs_mul, abs_of_pos hs]
    calc
      _ <= ((epsilon / 6) * (robinZeroKernel 1 (1 / 2 : Complex) x).re) * s :=
        mul_le_mul_of_nonneg_right he hs.le
      _ < epsilon / 2 := by nlinarith only [hthree, hEpsilon]
  have hTriangle := abs_sub_le (nicolasPsiRootTail 2 x * s)
    ((robinZeroKernel 1 (1 / 2 : Complex) x).re * s) (2 : Real)
  have hEq : nicolasPsiRootTail 2 x * s -
      (robinZeroKernel 1 (1 / 2 : Complex) x).re * s =
      (nicolasPsiRootTail 2 x - (robinZeroKernel 1 (1 / 2 : Complex) x).re) * s := by ring
  rw [hEq] at hTriangle
  rw [Real.dist_eq]
  change |nicolasPsiRootTail 2 x * s - 2| < epsilon
  change |(robinZeroKernel 1 (1 / 2 : Complex) x).re * s - 2| < epsilon / 2 at hClose
  linarith only [hTriangle, hError, hClose]

theorem tendsto_nicolasPrimePowerTail_sub_square_scaled :
    Tendsto (fun x : Real =>
      (nicolasPrimePowerTail x - nicolasPsiRootTail 2 x) *
        (x ^ (1 / 2 : Real) * Real.log x)) atTop (nhds 0) := by
  let C : Real := (Real.log 4 + 4) * (79 / 3 : Real)
  have hInv : Tendsto (fun x : Real => Inv.inv (Real.log x)) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp Real.tendsto_log_atTop
  have hSmall : Tendsto (fun x : Real => C / Real.log x) atTop (nhds 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using tendsto_const_nhds.mul hInv
  apply Metric.tendsto_atTop.mpr
  intro epsilon hEpsilon
  apply eventually_atTop.mp
  filter_upwards [hSmall.eventually_lt_const hEpsilon, eventually_ge_atTop (4 : Real),
    Real.tendsto_log_atTop.eventually_ge_atTop 1] with x he hx hlog
  have hx1 : 1 < x := by linarith
  have hx0 : 0 < x := by linarith
  have hl : 0 < Real.log x := Real.log_pos hx1
  have hr : 0 < x ^ (1 / 2 : Real) := Real.rpow_pos_of_pos hx0 _
  let s := x ^ (1 / 2 : Real) * Real.log x
  have hs : 0 < s := mul_pos hr hl
  have h := nicolasPrimePowerTail_higher_roots_bound (by linarith : 3 <= x) hlog
  have hUpper := mul_le_mul_of_nonneg_right h.2 hs.le
  have hCancel : (C * x ^ (-(1 / 2 : Real)) * Inv.inv ((Real.log x) ^ 2)) * s =
      C / Real.log x := by
    dsimp [s]
    rw [Real.rpow_neg hx0.le]
    field_simp
  change (nicolasPrimePowerTail x - nicolasPsiRootTail 2 x) * s <=
    (C * x ^ (-(1 / 2 : Real)) * Inv.inv ((Real.log x) ^ 2)) * s at hUpper
  rw [hCancel] at hUpper
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (mul_nonneg h.1 hs.le)]
  exact hUpper.trans_lt he

theorem tendsto_nicolasPrimePowerTail_scaled :
    Tendsto (fun x : Real =>
      nicolasPrimePowerTail x * (x ^ (1 / 2 : Real) * Real.log x)) atTop (nhds 2) := by
  have h := tendsto_nicolasPsiSquareTail_scaled.add
    tendsto_nicolasPrimePowerTail_sub_square_scaled
  convert h using 1
  . funext x
    ring
  . norm_num

end PrimeFactorOscillations

/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.NicolasPowerPersistence
import PrimeFactorOscillations.Helpers.NicolasTiltedTail

/-!
# Growing square-root tilted-product RH criteria

Every fixed c>0 gives an RH criterion at tilt c*sqrt(x). The forward
implication uses the existing common-cutoff result for all positive tilts.
The converse retains the uniform quadratic Euler-tail allowance; false-RH
power peaks dominate it. No fixed-tilt error is used outside its range.
The sharper normalized quadratic-tail asymptotic is a separate statement.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations

open Filter Robin1984

theorem riemannHypothesis_iff_eventually_sqrt_tilt_log_neg
    (c : Real) (hc : 0 < c) :
    RiemannHypothesis <->
      Filter.Eventually (fun x : Real =>
        nicolasTiltedLog (c * x ^ (1 / 2 : Real)) x < 0) atTop := by
  have hTheta : Filter.Eventually (fun N : Nat =>
      1 < Chebyshev.theta (N : Real)) atTop :=
    tendsto_primeProfile_theta_atTop.eventually_gt_atTop 1
  constructor
  . intro hRH
    choose N0 hN0 using eventually_atTop.mp
      (eventually_forall_pos_nicolasTiltedLog_nat_neg_of_RH hRH)
    filter_upwards [eventually_ge_atTop (N0 : Real), eventually_gt_atTop (0 : Real)]
      with x hx hxPos
    have h := hN0 (Nat.floor x) (Nat.le_floor hx) (c * x ^ (1 / 2 : Real))
      (mul_pos hc (Real.rpow_pos_of_pos hxPos _))
    rwa [nicolasTiltedLog_natFloor] at h
  . intro hEvent
    by_contra hNotRH
    have hCast : Tendsto (fun n : Nat => (n : Real)) atTop atTop :=
      tendsto_natCast_atTop_atTop
    choose N0 hN0 using eventually_atTop.mp (hTheta.and (hCast.eventually hEvent))
    choose b hb hbHalf hWindows using exists_nicolasLog_power_intervals_of_not_RH hNotRH
    choose n hn hnSix hF using hWindows 0 c (N0 : Real) (by linarith) hc
    have hn0 : N0 <= n := by exact_mod_cast hn.le
    have hnPos : (0 : Real) < n := by exact_mod_cast (by omega : 0 < n)
    have hnOne : (1 : Real) <= n := by exact_mod_cast (by omega : 1 <= n)
    have hFn := hF (n : Real) le_rfl (by rw [Real.rpow_zero]; linarith)
    have hCompare : (n : Real) ^ (-(1 / 2 : Real)) <= (n : Real) ^ (-b) :=
      Real.rpow_le_rpow_of_exponent_le hnOne (by linarith)
    have hSignal : c * (n : Real) ^ (-(1 / 2 : Real)) <
        nicolasLogMertensOscillation (n : Real) :=
      (mul_le_mul_of_nonneg_left hCompare hc.le).trans_lt hFn
    let z := c * (n : Real) ^ (1 / 2 : Real)
    have hz : 0 < z := mul_pos hc (Real.rpow_pos_of_pos hnPos _)
    have hBound := (nicolasTiltedLog_nat_tail_bounds n (by omega)
      (hN0 n hn0).1 z hz.le).1
    have hScaled := mul_lt_mul_of_pos_left hSignal hz
    have hPower : ((n : Real) ^ (1 / 2 : Real)) ^ 2 = n := by
      rw [pow_two, <- Real.rpow_add hnPos]
      norm_num
    have hLeft : z * (c * (n : Real) ^ (-(1 / 2 : Real))) = c ^ 2 := by
      dsimp [z]
      calc
        _ = c ^ 2 * ((n : Real) ^ (1 / 2 : Real) *
            (n : Real) ^ (-(1 / 2 : Real))) := by ring
        _ = _ := by rw [<- Real.rpow_add hnPos]; norm_num
    have hSquare : z ^ 2 / (n : Real) = c ^ 2 := by
      dsimp [z]
      rw [mul_pow, hPower]
      field_simp [hnPos.ne']
    rw [hLeft] at hScaled
    rw [hSquare] at hBound
    have hNegative : nicolasTiltedLog z (n : Real) < 0 := (hN0 n hn0).2
    linarith

theorem riemannHypothesis_iff_eventually_sqrt_tilt_product_lt_one
    (c : Real) (hc : 0 < c) :
    RiemannHypothesis <->
      Filter.Eventually (fun x : Real =>
        nicolasTiltedProduct (c * x ^ (1 / 2 : Real)) x < 1) atTop := by
  have hTheta : Filter.Eventually (fun x : Real => 1 < Chebyshev.theta x) atTop :=
    (primeProfile_theta_isEquivalent_id.symm.tendsto_atTop tendsto_id).eventually_gt_atTop 1
  constructor
  . intro hRH
    have hAll := (riemannHypothesis_iff_eventually_all_positive_tiltedProducts_lt_one).mp hRH
    filter_upwards [hAll, eventually_gt_atTop (0 : Real)] with x hx hxPos
    exact hx _ (mul_pos hc (Real.rpow_pos_of_pos hxPos _))
  . intro hEvent
    apply (riemannHypothesis_iff_eventually_sqrt_tilt_log_neg c hc).mpr
    filter_upwards [hEvent, hTheta, eventually_gt_atTop (0 : Real)] with x hx ht hxPos
    have hz : 0 <= c * x ^ (1 / 2 : Real) := (mul_pos hc (Real.rpow_pos_of_pos hxPos _)).le
    rw [<- log_nicolasTiltedProduct _ x hz ht]
    exact Real.log_neg (nicolasTiltedProduct_pos _ x hz ht) hx

end PrimeFactorOscillations

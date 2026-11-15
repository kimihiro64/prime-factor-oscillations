/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianAnalyticCoefficientScale
import PrimeFactorOscillations.Helpers.HamiltonianLocalPermanentRemainder

/-! # Actual analytic linear remainder for the signed Gamma consumer

The constant and linear Taylor terms are retained exactly. Bounds apply
only to the subsequent remainder and have explicit radius dependence.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

theorem hamiltonianFiniteSeriesValue_one (f : Complex -> Complex) :
    hamiltonianFiniteSeriesValue 1 (wickTaylorSeries f) =
      f 0 + PowerSeries.coeff 1 (wickTaylorSeries f) := by
  have hZero : PowerSeries.coeff 0 (wickTaylorSeries f) = f 0 := by
    rw [wickTaylorSeries_coeff]
    norm_num [iteratedDeriv_zero]
  simp only [hamiltonianFiniteSeriesValue, Finset.sum_range_succ,
    Finset.sum_range_zero, zero_add, hZero]

theorem hamiltonianTaylorCoefficient_norm_bound
    (f : Complex -> Complex) (R : NNReal) (M : Real) (k : Nat)
    (hR : 0 < R)
    (hAnalytic : forall w, Membership.mem (Metric.closedBall (0 : Complex) (R : Real)) w ->
      AnalyticAt Complex f w)
    (hCircle : forall w, Membership.mem (Metric.sphere (0 : Complex) (R : Real)) w ->
      norm (f w) <= M) :
    norm (PowerSeries.coeff k (wickTaylorSeries f)) <= M * (Inv.inv (R : Real)) ^ k := by
  have hSeries : HasFPowerSeriesOnBall f (cauchyPowerSeries f 0 R) 0 R := by
    apply DifferentiableOn.hasFPowerSeriesOnBall _ hR
    intro w hw
    exact (hAnalytic w hw).differentiableAt.differentiableWithinAt
  have hRReal : 0 < (R : Real) := by exact_mod_cast hR
  have hBound := hamiltonianCauchyCoefficient_norm_bound f R M k hRReal hCircle
  rw [hamiltonianCauchyCoefficient_eq_taylor f R hSeries k] at hBound
  exact hBound

theorem hamiltonianCauchy_linear_remainder_one
    (f : Complex -> Complex) (R : NNReal) (M : Real)
    (hR : 1 < (R : Real))
    (hAnalytic : forall w, Membership.mem (Metric.closedBall (0 : Complex) (R : Real)) w ->
      AnalyticAt Complex f w)
    (hCircle : forall w, Membership.mem (Metric.sphere (0 : Complex) (R : Real)) w ->
      norm (f w) <= M) :
    norm (f 1 - f 0 - PowerSeries.coeff 1 (wickTaylorSeries f)) <=
      M * (Inv.inv (R : Real)) ^ 2 / (1 - Inv.inv (R : Real)) := by
  have hR0 : 0 < R := by exact_mod_cast lt_trans (by norm_num : (0 : Real) < 1) hR
  have hSeries : HasFPowerSeriesOnBall f (cauchyPowerSeries f 0 R) 0 R := by
    apply DifferentiableOn.hasFPowerSeriesOnBall _ hR0
    intro w hw
    exact (hAnalytic w hw).differentiableAt.differentiableWithinAt
  have hOne : Membership.mem (Metric.eball (0 : Complex) (R : ENNReal)) (1 : Complex) := by
    rw [mem_eball_zero_iff, enorm_lt_coe]
    simpa only [nnnorm_one] using (show (1 : NNReal) < R by exact_mod_cast hR)
  have hSum : HasSum (hamiltonianCauchyCoefficient f R) (f 1) := by
    change HasSum (fun k => cauchyPowerSeries f 0 R k (fun _ => 1)) (f 1)
    simpa only [zero_add] using hSeries.hasSum hOne
  have hTail := hamiltonianCauchyTail_of_hasSum f R M 2 hR hSum hCircle
  have hCoeff : forall k, hamiltonianCauchyCoefficient f R k =
      PowerSeries.coeff k (wickTaylorSeries f) := by
    intro k
    exact hamiltonianCauchyCoefficient_eq_taylor f R hSeries k
  simp_rw [hCoeff] at hTail
  change norm (f 1 - hamiltonianFiniteSeriesValue 1 (wickTaylorSeries f)) <= _ at hTail
  rw [hamiltonianFiniteSeriesValue_one] at hTail
  have hIdentity : f 1 - (f 0 + PowerSeries.coeff 1 (wickTaylorSeries f)) =
      f 1 - f 0 - PowerSeries.coeff 1 (wickTaylorSeries f) := by ring
  rw [hIdentity] at hTail
  exact hTail

theorem hamiltonianCauchy_linear_remainder
    (f : Complex -> Complex) (r : NNReal) (M : Real)
    (hr : 0 < r) (hM : 0 <= M)
    (hAnalytic : forall w, Membership.mem (Metric.closedBall (0 : Complex) (r : Real)) w ->
      AnalyticAt Complex f w)
    (hCircle : forall w, Membership.mem (Metric.sphere (0 : Complex) (r : Real)) w ->
      norm (f w) <= M)
    (t : Complex) (ht : norm t <= (r : Real) / 2) :
    norm (f t - f 0 - t * PowerSeries.coeff 1 (wickTaylorSeries f)) <=
      2 * M * norm t ^ 2 / (r : Real) ^ 2 := by
  have hrReal : 0 < (r : Real) := by exact_mod_cast hr
  by_cases htZero : t = 0
  case pos =>
    subst t
    simp
  case neg =>
    have htPos : 0 < norm t := norm_pos_iff.mpr htZero
    let R : NNReal := Subtype.mk ((r : Real) / norm t)
      (div_nonneg r.property (norm_nonneg t))
    have hTwo : 2 <= (R : Real) := by
      calc
        _ = (2 * norm t) / norm t := by field_simp [ne_of_gt htPos]
        _ <= (r : Real) / norm t :=
          div_le_div_of_nonneg_right (by linarith only [ht]) htPos.le
        _ = _ := rfl
    have hR : 1 < (R : Real) := by linarith only [hTwo]
    have hZero : Membership.mem (Metric.closedBall (0 : Complex) (r : Real)) (0 : Complex) := by
      rw [Metric.mem_closedBall, dist_self]
      exact r.property
    have hf0 := hAnalytic 0 hZero
    have hScaledAnalytic : forall w,
        Membership.mem (Metric.closedBall (0 : Complex) (R : Real)) w ->
          AnalyticAt Complex (fun z => f (t * z)) w := by
      intro w hw
      have hwNorm : norm w <= (R : Real) := by
        simpa only [Metric.mem_closedBall, dist_zero_right] using hw
      have hNorm : norm (t * w) <= (r : Real) := by
        calc
          _ = norm t * norm w := norm_mul _ _
          _ <= norm t * (R : Real) := mul_le_mul_of_nonneg_left hwNorm (norm_nonneg t)
          _ = _ := by
            change norm t * ((r : Real) / norm t) = (r : Real)
            field_simp [ne_of_gt htPos]
      have hImage : Membership.mem (Metric.closedBall (0 : Complex) (r : Real)) (t * w) := by
        simpa only [Metric.mem_closedBall, dist_zero_right] using hNorm
      exact (hAnalytic (t * w) hImage).comp (analyticAt_const.mul analyticAt_id)
    have hScaledCircle : forall w,
        Membership.mem (Metric.sphere (0 : Complex) (R : Real)) w ->
          norm (f (t * w)) <= M := by
      intro w hw
      have hwNorm : norm w = (R : Real) := by
        simpa only [Metric.mem_sphere, dist_zero_right] using hw
      have hNorm : norm (t * w) = (r : Real) := by
        rw [norm_mul, hwNorm]
        change norm t * ((r : Real) / norm t) = (r : Real)
        field_simp [ne_of_gt htPos]
      apply hCircle (t * w)
      simpa only [Metric.mem_sphere, dist_zero_right] using hNorm
    have hTail := hamiltonianCauchy_linear_remainder_one (fun z => f (t * z))
      R M hR hScaledAnalytic hScaledCircle
    have hCoeff := wickTaylorSeries_coeff_comp_mul f hf0 t 1
    simp only [pow_one] at hCoeff
    simp only [mul_one, mul_zero, hCoeff] at hTail
    have hInv : Inv.inv (R : Real) = norm t / (r : Real) := by
      change Inv.inv ((r : Real) / norm t) = norm t / (r : Real)
      field_simp [ne_of_gt htPos, ne_of_gt hrReal]
    have hHalf : norm t / (r : Real) <= 1 / 2 := by
      calc
        _ <= ((r : Real) / 2) / (r : Real) :=
          div_le_div_of_nonneg_right ht hrReal.le
        _ = _ := by field_simp [ne_of_gt hrReal]
    calc
      _ <= M * (Inv.inv (R : Real)) ^ 2 / (1 - Inv.inv (R : Real)) := hTail
      _ = M * (norm t / (r : Real)) ^ 2 / (1 - norm t / (r : Real)) := by rw [hInv]
      _ <= M * (norm t / (r : Real)) ^ 2 / (1 / 2) :=
        div_le_div_of_nonneg_left (mul_nonneg hM (sq_nonneg _))
          (by norm_num) (by linarith only [hHalf])
      _ = _ := by field_simp [ne_of_gt hrReal] <;> ring

end PrimeFactorOscillations

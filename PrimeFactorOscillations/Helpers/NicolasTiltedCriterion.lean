/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.NicolasPrimeProductCriterion
import PrimeFactorOscillations.Helpers.PrimeProfilePositive
import PrimeFactorOscillations.Helpers.PrimeProfileTail

/-!
# Positive tilted prime products and Nicolas's logarithm

The finite and infinite normalized profiles have a common positive lower
bound on each fixed nonnegative real compact interval. Their actual
inverse-cutoff error therefore remains inverse-cutoff after taking logs.
The exact finite logarithmic correction is retained. For every fixed
positive tilt, the eventual negative logarithm and eventual product bound
are each equivalent to RH, with both natural and real cutoff conventions.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations

open Filter Robin1984

theorem exists_primePrefixProfile_log_error (b : Real) (hb : 0 <= b) :
    exists C : Real, 0 <= C /\ forall N : Nat, 1 <= N ->
      forall z : Real, 0 <= z -> z <= b ->
        abs (Real.log (primePrefixProfile N (z : Complex)).re -
          Real.log (primeProfile (z : Complex)).re) <= C / (N : Real) := by
  choose A hA hError using exists_primePrefixProfile_uniform_error b hb
  let d := Real.exp (-(b ^ 2 * tsum (fun p : Nat.Primes =>
    (primeProfileWeight (p : Nat)) ^ 2)) / 2)
  have hd : 0 < d := Real.exp_pos _
  refine Exists.intro (A / d) (And.intro (div_nonneg hA hd.le) ?_)
  intro N hN z hz hzb
  have hBall : Membership.mem (Metric.closedBall (0 : Complex) b) (z : Complex) := by
    simpa only [Metric.mem_closedBall, dist_zero_right, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg hz] using hzb
  let u := (primePrefixProfile N (z : Complex)).re
  let v := (primeProfile (z : Complex)).re
  have hdu : d <= u := primePrefixProfile_re_lower_bound N b z hb hz hzb
  have hdv : d <= v := primeProfile_re_lower_bound b z hb hz hzb
  have hu : 0 < u := hd.trans_le hdu
  have hv : 0 < v := hd.trans_le hdv
  have hAbs : abs (u - v) <= A / (N : Real) := by
    have h := (Complex.abs_re_le_norm
      (primePrefixProfile N (z : Complex) - primeProfile (z : Complex))).trans
      (hError N hN (z : Complex) hBall)
    simpa only [Complex.sub_re] using h
  have hSecant (x y : Real) (hx : 0 < x) (hy : 0 < y) (hdy : d <= y) :
      Real.log x - Real.log y <= abs (x - y) / d := by
    calc
      _ = Real.log (x / y) := (Real.log_div hx.ne' hy.ne').symm
      _ <= x / y - 1 := Real.log_le_sub_one_of_pos (div_pos hx hy)
      _ = (x - y) / y := by field_simp
      _ <= abs (x - y) / y :=
        div_le_div_of_nonneg_right (le_abs_self _) hy.le
      _ <= abs (x - y) / d :=
        div_le_div_of_nonneg_left (abs_nonneg _) hd hdy
  have hScale : abs (u - v) / d <= (A / d) / (N : Real) := by
    calc
      _ <= (A / (N : Real)) / d := div_le_div_of_nonneg_right hAbs hd.le
      _ = _ := by ring
  have hUpper := (hSecant u v hu hv hdv).trans hScale
  have hLower := hSecant v u hv hu hdu
  rw [abs_sub_comm v u] at hLower
  change abs (Real.log u - Real.log v) <= (A / d) / (N : Real)
  exact abs_le.mpr (And.intro (by linarith) hUpper)

noncomputable def nicolasTiltedLog (z x : Real) : Real :=
  z * (Real.eulerMascheroniConstant + Real.log (Real.log (Chebyshev.theta x))) +
    Real.log (primeProfile (z : Complex)).re -
      (primeProfilePrefixSet (Nat.floor x)).sum
        (fun p => Real.log (1 + primeProfileWeight (p : Nat) * z))

theorem primePrefixProfile_log_eq_sum (N : Nat) (z : Real) (hz : 0 <= z) :
    Real.log (primePrefixProfile N (z : Complex)).re =
      (primeProfilePrefixSet N).sum
        (fun p => Real.log (1 + primeProfileWeight (p : Nat) * z)) -
      z * (primeProfilePrefixSet N).sum
        (fun p => Real.log (1 + primeProfileWeight (p : Nat))) := by
  rw [primePrefixProfile_ofReal_eq_exp N z hz, Complex.ofReal_re, Real.log_exp,
    Finset.sum_sub_distrib, <- Finset.sum_mul]
  ring

theorem nicolasTiltedLog_nat_eq_components (z : Real) (hz : 0 <= z)
    (N : Nat) (hTheta : 1 < Chebyshev.theta (N : Real)) :
    nicolasTiltedLog z (N : Real) =
      z * nicolasLogMertensOscillation (N : Real) +
        (Real.log (primeProfile (z : Complex)).re -
          Real.log (primePrefixProfile N (z : Complex)).re) := by
  rw [nicolasLog_nat_eq_primeProfile_clock_difference N hTheta,
    primePrefixProfile_log_eq_sum N z hz]
  unfold nicolasTiltedLog
  rw [Nat.floor_natCast]
  ring

theorem exists_nicolasTiltedLog_nat_error (b : Real) (hb : 0 <= b) :
    exists C : Real, 0 <= C /\ forall N : Nat, 1 <= N ->
      1 < Chebyshev.theta (N : Real) ->
      forall z : Real, 0 <= z -> z <= b ->
        abs (nicolasTiltedLog z (N : Real) -
          z * nicolasLogMertensOscillation (N : Real)) <= C / (N : Real) := by
  choose C hC hError using exists_primePrefixProfile_log_error b hb
  refine Exists.intro C (And.intro hC ?_)
  intro N hN hTheta z hz hzb
  rw [nicolasTiltedLog_nat_eq_components z hz N hTheta, add_sub_cancel_left,
    abs_sub_comm]
  exact hError N hN z hz hzb

theorem riemannHypothesis_iff_eventually_nicolasTiltedLog_nat_neg
    (z : Real) (hz : 0 < z) :
    RiemannHypothesis <-> Filter.Eventually (fun N : Nat =>
      nicolasTiltedLog z (N : Real) < 0) atTop := by
  choose C hC hError using exists_nicolasTiltedLog_nat_error z hz.le
  have hTheta : Filter.Eventually (fun N : Nat =>
      1 < Chebyshev.theta (N : Real)) atTop :=
    tendsto_primeProfile_theta_atTop.eventually_gt_atTop 1
  constructor
  . intro hRH
    have hNegative := eventually_nicolasLog_nat_lt_neg_div_of_RH hRH ((C + 1) / z)
    filter_upwards [hNegative, hTheta, eventually_ge_atTop (1 : Nat)]
      with N hNegativeN hThetaN hN
    have hNR : (0 : Real) < N := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)
    have hBound := hError N hN hThetaN z hz.le le_rfl
    have hScaled := mul_lt_mul_of_pos_left hNegativeN hz
    have hCancel : z * (-((C + 1) / z) / (N : Real)) =
        -(C / (N : Real)) - 1 / (N : Real) := by
      field_simp [hz.ne', hNR.ne']
      ring
    rw [hCancel] at hScaled
    have hReserve : 0 < 1 / (N : Real) := one_div_pos.mpr hNR
    linarith only [(abs_le.mp hBound).2, hScaled, hReserve]
  . intro hEvent
    by_contra hNotRH
    have hAll : Filter.Eventually (fun N : Nat =>
        1 <= N /\ 1 < Chebyshev.theta (N : Real) /\
          nicolasTiltedLog z (N : Real) < 0) atTop := by
      filter_upwards [eventually_ge_atTop (1 : Nat), hTheta, hEvent]
        with N hN hT hE
      exact And.intro hN (And.intro hT hE)
    choose N0 hN0 using eventually_atTop.mp hAll
    choose N hN hPeak using
      nicolasLog_scaled_unbounded_of_not_RH hNotRH ((C + 1) / z) N0
    have hDomain := hN0 N hN
    have hNR : (0 : Real) < N := by
      exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hDomain.1)
    have hBound := hError N hDomain.1 hDomain.2.1 z hz.le le_rfl
    have hScaled := mul_le_mul_of_nonneg_left (abs_le.mp hBound).1 hNR.le
    have hCancel : (N : Real) * (-(C / (N : Real))) = -C := by
      field_simp
    rw [hCancel] at hScaled
    have hPositive := mul_lt_mul_of_pos_left hPeak hz
    have hCancelZ : z * ((C + 1) / z) = C + 1 := by field_simp
    rw [hCancelZ] at hPositive
    have hNegative := mul_neg_of_pos_of_neg hNR hDomain.2.2
    nlinarith only [hScaled, hPositive, hNegative]

theorem nicolasTiltedLog_natFloor (z x : Real) :
    nicolasTiltedLog z (Nat.floor x : Real) = nicolasTiltedLog z x := by
  unfold nicolasTiltedLog
  rw [Nat.floor_natCast, <- Chebyshev.theta_eq_theta_coe_floor x]

theorem riemannHypothesis_iff_eventually_nicolasTiltedLog_neg
    (z : Real) (hz : 0 < z) :
    RiemannHypothesis <-> Filter.Eventually (fun x : Real =>
      nicolasTiltedLog z x < 0) atTop := by
  constructor
  . intro hRH
    have hNat := (riemannHypothesis_iff_eventually_nicolasTiltedLog_nat_neg z hz).mp hRH
    choose N0 hN0 using eventually_atTop.mp hNat
    refine eventually_atTop.mpr (Exists.intro (N0 : Real) ?_)
    intro x hx
    rw [<- nicolasTiltedLog_natFloor z x]
    exact hN0 (Nat.floor x) (Nat.le_floor hx)
  . intro hEvent
    apply (riemannHypothesis_iff_eventually_nicolasTiltedLog_nat_neg z hz).mpr
    exact (tendsto_natCast_atTop_atTop :
      Tendsto (fun N : Nat => (N : Real)) atTop atTop).eventually hEvent

noncomputable def nicolasTiltedProduct (z x : Real) : Real :=
  Real.exp (z * Real.eulerMascheroniConstant + Real.log (primeProfile (z : Complex)).re) *
    (Real.log (Chebyshev.theta x)) ^ z /
      (primeProfilePrefixSet (Nat.floor x)).prod
        (fun p => 1 + primeProfileWeight (p : Nat) * z)

theorem nicolasTiltedProduct_pos (z x : Real) (hz : 0 <= z)
    (hTheta : 1 < Chebyshev.theta x) : 0 < nicolasTiltedProduct z x := by
  have hFactor (p : Nat.Primes) : 0 < 1 + primeProfileWeight (p : Nat) * z := by
    have hNonneg := mul_nonneg (primeProfileWeight_nonneg (p : Nat)) hz
    linarith
  unfold nicolasTiltedProduct
  exact div_pos (mul_pos (Real.exp_pos _)
    (Real.rpow_pos_of_pos (Real.log_pos hTheta) z))
    (Finset.prod_pos (fun p _ => hFactor p))

theorem log_nicolasTiltedProduct (z x : Real) (hz : 0 <= z)
    (hTheta : 1 < Chebyshev.theta x) :
    Real.log (nicolasTiltedProduct z x) = nicolasTiltedLog z x := by
  have hFactor (p : Nat.Primes) : 0 < 1 + primeProfileWeight (p : Nat) * z := by
    have hNonneg := mul_nonneg (primeProfileWeight_nonneg (p : Nat)) hz
    linarith
  have hProduct : 0 < (primeProfilePrefixSet (Nat.floor x)).prod
      (fun p => 1 + primeProfileWeight (p : Nat) * z) :=
    Finset.prod_pos (fun p _ => hFactor p)
  have hPower : 0 < (Real.log (Chebyshev.theta x)) ^ z :=
    Real.rpow_pos_of_pos (Real.log_pos hTheta) z
  unfold nicolasTiltedProduct nicolasTiltedLog
  rw [Real.log_div (mul_pos (Real.exp_pos _) hPower).ne' hProduct.ne',
    Real.log_mul (Real.exp_pos _).ne' hPower.ne', Real.log_exp,
    Real.log_rpow (Real.log_pos hTheta),
    Real.log_prod (fun p _ => (hFactor p).ne')]
  ring

theorem riemannHypothesis_iff_eventually_nicolasTiltedProduct_lt_one
    (z : Real) (hz : 0 < z) :
    RiemannHypothesis <-> Filter.Eventually (fun x : Real =>
      nicolasTiltedProduct z x < 1) atTop := by
  have hTheta : Filter.Eventually (fun x : Real => 1 < Chebyshev.theta x) atTop :=
    (primeProfile_theta_isEquivalent_id.symm.tendsto_atTop tendsto_id).eventually_gt_atTop 1
  constructor
  . intro hRH
    have hLog := (riemannHypothesis_iff_eventually_nicolasTiltedLog_neg z hz).mp hRH
    filter_upwards [hLog, hTheta] with x hx hTx
    have h := Real.exp_lt_exp.mpr hx
    rw [<- log_nicolasTiltedProduct z x hz.le hTx,
      Real.exp_log (nicolasTiltedProduct_pos z x hz.le hTx), Real.exp_zero] at h
    exact h
  . intro hEvent
    apply (riemannHypothesis_iff_eventually_nicolasTiltedLog_neg z hz).mpr
    filter_upwards [hEvent, hTheta] with x hx hTx
    have h := Real.log_lt_log (nicolasTiltedProduct_pos z x hz.le hTx) hx
    rw [log_nicolasTiltedProduct z x hz.le hTx, Real.log_one] at h
    exact h

end PrimeFactorOscillations

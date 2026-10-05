/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.NicolasTiltedCriterion

/-!
# Explicit tilted logarithmic tails

Exact finite prefix differences retain all tail primes. The elementary
one-add-log remainders give a quadratic lower allowance and a linear upper
allowance in the tilt, uniformly for every nonnegative tilt. Under RH a
single eventual cutoff works for all positive tilts simultaneously, and
that simultaneous actual-product inequality also implies RH.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations

open Filter Robin1984

theorem primePrefixProfile_log_tail_bounds
    (N M : Nat) (hN : 1 <= N) (hNM : N <= M) (z : Real) (hz : 0 <= z) :
    -(z ^ 2 / (N : Real)) <=
      Real.log (primePrefixProfile M (z : Complex)).re -
        Real.log (primePrefixProfile N (z : Complex)).re /\
    Real.log (primePrefixProfile M (z : Complex)).re -
      Real.log (primePrefixProfile N (z : Complex)).re <= z / (N : Real) := by
  classical
  let S := primeProfilePrefixSet M \ primeProfilePrefixSet N
  let g : Nat.Primes -> Real := fun p =>
    Real.log (1 + primeProfileWeight (p : Nat) * z) -
      Real.log (1 + primeProfileWeight (p : Nat)) * z
  have hLocal (p : Nat.Primes) :
      -(z ^ 2 / 2) * (primeProfileWeight (p : Nat)) ^ 2 <= g p /\
        g p <= (z / 2) * (primeProfileWeight (p : Nat)) ^ 2 := by
    let a := primeProfileWeight (p : Nat)
    have ha : 0 <= a := primeProfileWeight_nonneg _
    have hOne := Real.sub_log_one_add_bounds (a * z) (mul_nonneg ha hz)
    have hTwo := Real.sub_log_one_add_bounds a ha
    have hLower := mul_nonneg hz hTwo.1
    have hUpper := mul_le_mul_of_nonneg_left hTwo.2 hz
    change -(z ^ 2 / 2) * a ^ 2 <=
      Real.log (1 + a * z) - Real.log (1 + a) * z /\
      Real.log (1 + a * z) - Real.log (1 + a) * z <= (z / 2) * a ^ 2
    constructor
    . nlinarith only [hOne.2, hLower]
    . nlinarith only [hOne.1, hUpper]
  have hMass : S.sum (fun p => (primeProfileWeight (p : Nat)) ^ 2) <=
      2 / (N : Real) := by
    apply sum_primeProfileWeight_sq_tail_le S N hN
    intro p hp
    have hNot := (Finset.mem_sdiff.mp hp).2
    exact Nat.lt_of_not_ge (fun h => hNot ((mem_primeProfilePrefixSet p N).mpr h))
  have hLog (K : Nat) : Real.log (primePrefixProfile K (z : Complex)).re =
      (primeProfilePrefixSet K).sum g := by
    rw [primePrefixProfile_ofReal_eq_exp K z hz, Complex.ofReal_re, Real.log_exp]
  have hExact : Real.log (primePrefixProfile M (z : Complex)).re -
      Real.log (primePrefixProfile N (z : Complex)).re = S.sum g := by
    rw [hLog M, hLog N]
    dsimp [S]
    have hSum : (primeProfilePrefixSet M \ primeProfilePrefixSet N).sum g +
        (primeProfilePrefixSet N).sum g = (primeProfilePrefixSet M).sum g :=
      Finset.sum_sdiff (monotone_primeProfilePrefixSet hNM)
    linarith only [hSum]
  rw [hExact]
  constructor
  . calc
      -(z ^ 2 / (N : Real)) = -(z ^ 2 / 2) * (2 / (N : Real)) := by ring
      _ <= -(z ^ 2 / 2) * S.sum (fun p => (primeProfileWeight (p : Nat)) ^ 2) :=
        mul_le_mul_of_nonpos_left hMass (neg_nonpos.mpr (by positivity))
      _ = S.sum (fun p => -(z ^ 2 / 2) * (primeProfileWeight (p : Nat)) ^ 2) :=
        Finset.mul_sum _ _ _
      _ <= S.sum g := Finset.sum_le_sum (fun p _ => (hLocal p).1)
  . calc
      S.sum g <= S.sum (fun p => (z / 2) * (primeProfileWeight (p : Nat)) ^ 2) :=
        Finset.sum_le_sum (fun p _ => (hLocal p).2)
      _ = (z / 2) * S.sum (fun p => (primeProfileWeight (p : Nat)) ^ 2) :=
        (Finset.mul_sum _ _ _).symm
      _ <= (z / 2) * (2 / (N : Real)) :=
        mul_le_mul_of_nonneg_left hMass (by positivity)
      _ = z / (N : Real) := by ring

theorem primeProfile_log_tail_bounds
    (N : Nat) (hN : 1 <= N) (z : Real) (hz : 0 <= z) :
    -(z ^ 2 / (N : Real)) <=
      Real.log (primeProfile (z : Complex)).re -
        Real.log (primePrefixProfile N (z : Complex)).re /\
    Real.log (primeProfile (z : Complex)).re -
      Real.log (primePrefixProfile N (z : Complex)).re <= z / (N : Real) := by
  have hBall : Membership.mem (Metric.closedBall (0 : Complex) z) (z : Complex) := by
    simp only [Metric.mem_closedBall, dist_zero_right, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg hz, le_refl]
  have hComplex := (tendstoUniformlyOn_primePrefixProfile z hz).tendsto_at hBall
  have hReal := (Complex.continuous_re.tendsto (primeProfile (z : Complex))).comp hComplex
  have hLog := (Real.continuousAt_log (primeProfile_re_pos z hz).ne').tendsto.comp hReal
  have hLimit := hLog.sub_const (Real.log (primePrefixProfile N (z : Complex)).re)
  constructor
  . exact ge_of_tendsto hLimit ((eventually_ge_atTop N).mono
      (fun M hNM => (primePrefixProfile_log_tail_bounds N M hN hNM z hz).1))
  . exact le_of_tendsto hLimit ((eventually_ge_atTop N).mono
      (fun M hNM => (primePrefixProfile_log_tail_bounds N M hN hNM z hz).2))

theorem nicolasTiltedLog_nat_tail_bounds
    (N : Nat) (hN : 1 <= N) (hTheta : 1 < Chebyshev.theta (N : Real))
    (z : Real) (hz : 0 <= z) :
    z * nicolasLogMertensOscillation (N : Real) - z ^ 2 / (N : Real) <=
      nicolasTiltedLog z (N : Real) /\
    nicolasTiltedLog z (N : Real) <=
      z * nicolasLogMertensOscillation (N : Real) + z / (N : Real) := by
  have h := primeProfile_log_tail_bounds N hN z hz
  rw [nicolasTiltedLog_nat_eq_components z hz N hTheta]
  constructor <;> linarith only [h.1, h.2]

theorem eventually_forall_pos_nicolasTiltedLog_nat_neg_of_RH
    (hRH : RiemannHypothesis) :
    Filter.Eventually (fun N : Nat => forall z : Real, 0 < z ->
      nicolasTiltedLog z (N : Real) < 0) atTop := by
  have hNegative := eventually_nicolasLog_nat_lt_neg_div_of_RH hRH 1
  have hTheta : Filter.Eventually (fun N : Nat =>
      1 < Chebyshev.theta (N : Real)) atTop :=
    tendsto_primeProfile_theta_atTop.eventually_gt_atTop 1
  filter_upwards [hNegative, hTheta, eventually_ge_atTop (1 : Nat)]
    with N hNeg hT hN
  intro z hz
  have hBound := nicolasTiltedLog_nat_tail_bounds N hN hT z hz.le
  have hScaled := mul_lt_mul_of_pos_left hNeg hz
  have hCancel : z * (-(1 : Real) / (N : Real)) = -z / (N : Real) := by ring
  rw [hCancel] at hScaled
  rw [neg_div] at hScaled
  linarith only [hBound.2, hScaled]

theorem riemannHypothesis_iff_eventually_all_positive_tiltedProducts_lt_one :
    RiemannHypothesis <-> Filter.Eventually (fun x : Real =>
      forall z : Real, 0 < z -> nicolasTiltedProduct z x < 1) atTop := by
  have hTheta : Filter.Eventually (fun x : Real => 1 < Chebyshev.theta x) atTop :=
    (primeProfile_theta_isEquivalent_id.symm.tendsto_atTop tendsto_id).eventually_gt_atTop 1
  constructor
  . intro hRH
    choose N0 hN0 using eventually_atTop.mp
      (eventually_forall_pos_nicolasTiltedLog_nat_neg_of_RH hRH)
    filter_upwards [eventually_ge_atTop (N0 : Real), hTheta] with x hx hTx
    intro z hz
    have hLog := hN0 (Nat.floor x) (Nat.le_floor hx) z hz
    rw [nicolasTiltedLog_natFloor] at hLog
    have h := Real.exp_lt_exp.mpr hLog
    rw [<- log_nicolasTiltedProduct z x hz.le hTx,
      Real.exp_log (nicolasTiltedProduct_pos z x hz.le hTx), Real.exp_zero] at h
    exact h
  . intro hEvent
    apply (riemannHypothesis_iff_eventually_nicolasTiltedProduct_lt_one 1
      (by norm_num)).mpr
    filter_upwards [hEvent] with x hx
    exact hx 1 (by norm_num)

end PrimeFactorOscillations

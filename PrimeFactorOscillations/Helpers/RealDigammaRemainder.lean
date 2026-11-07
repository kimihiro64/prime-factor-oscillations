/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import PrimeFactorOscillations.Helpers.RealDigammaHeight

/-!
# A compensated real-part remainder for the digamma function

Finite trapezoid identities retain the endpoint correction before passing
from the reciprocal profile to the complete digamma series.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace Complex

open MeasureTheory
open scoped Interval Topology BigOperators

def digammaReciprocalProfile (z : Complex) (t : Real) : Real :=
  (1 / (z + (t : Complex))).re

def digammaReciprocalSlope (z : Complex) (t : Real) : Real :=
  (-1 / (z + (t : Complex)) ^ 2).re

def digammaReciprocalCurvature (z : Complex) (t : Real) : Real :=
  (2 / (z + (t : Complex)) ^ 3).re

theorem digammaReciprocal_ne_zero (z : Complex) (t : Real)
    (hz : 0 < z.re) (ht : 0 <= t) : Not (z + (t : Complex) = 0) := by
  have hh : 0 < (z + (t : Complex)).re := by
    rw [Complex.add_re, Complex.ofReal_re]
    linarith only [hz, ht]
  intro hn
  rw [hn, Complex.zero_re] at hh
  exact (lt_irrefl 0) hh

theorem digammaReciprocalProfile_hasDerivAt (z : Complex) (t : Real)
    (hne : Not (z + (t : Complex) = 0)) :
    HasDerivAt (digammaReciprocalProfile z) (digammaReciprocalSlope z t) t := by
  have hh := ((hasDerivAt_id (t : Complex)).const_add z).inv hne
  convert hh.real_of_complex using 1 <;>
    first
    | (funext x; simp only [digammaReciprocalProfile, one_div, Pi.inv_apply, id_eq])
    | (simp only [digammaReciprocalSlope, id_eq])

theorem digammaReciprocalSlope_hasDerivAt (z : Complex) (t : Real)
    (hne : Not (z + (t : Complex) = 0)) :
    HasDerivAt (digammaReciprocalSlope z) (digammaReciprocalCurvature z t) t := by
  have hh := (((hasDerivAt_id (t : Complex)).const_add z).pow 2).inv
    (pow_ne_zero 2 hne)
  have hc : HasDerivAt (fun w : Complex => -1 / (z + w) ^ 2)
      (2 / (z + (t : Complex)) ^ 3) (t : Complex) := by
    convert hh.neg using 1 <;>
      first
      | (funext w; simp only [neg_div, one_div, Pi.inv_apply, Pi.neg_apply, Pi.pow_apply, id_eq])
      | (simp only [Pi.pow_apply, id_eq]; norm_num; field_simp [hne] <;> ring)
  exact hc.real_of_complex

theorem digammaReciprocalCurvature_abs_le (z : Complex) (t : Real)
    (hz : 0 < z.re) (ht : 0 <= t) :
    abs (digammaReciprocalCurvature z t) <= 2 / (z.re + t) ^ 3 := by
  have hreal : 0 < z.re + t := by linarith only [hz, ht]
  have hnorm : z.re + t <= norm (z + (t : Complex)) := by
    simpa only [Complex.add_re, Complex.ofReal_re] using
      Complex.re_le_norm (z + (t : Complex))
  calc
    abs (digammaReciprocalCurvature z t) <= norm (2 / (z + (t : Complex)) ^ 3) :=
      Complex.abs_re_le_norm _
    _ = 2 / (norm (z + (t : Complex))) ^ 3 := by rw [norm_div, norm_pow]; norm_num
    _ <= 2 / (z.re + t) ^ 3 := by gcongr

theorem digammaReciprocal_log_primitive (z : Complex) (t : Real)
    (hz : 0 < z.re) (ht : 0 <= t) :
    HasDerivAt (fun x : Real => Real.log (norm (z + (x : Complex))))
      (digammaReciprocalProfile z t) t := by
  have hslit : Membership.mem Complex.slitPlane (z + (t : Complex)) :=
    Or.inl (by rw [Complex.add_re, Complex.ofReal_re]; linarith only [hz, ht])
  have hh := (Complex.hasDerivAt_log hslit).comp (t : Complex)
    ((hasDerivAt_id (t : Complex)).const_add z)
  simpa only [Complex.log_re, digammaReciprocalProfile, one_div, mul_one,
    Function.comp_apply, id_eq]
    using hh.real_of_complex

theorem digammaReciprocalCurvature_continuousAt (z : Complex) (t : Real)
    (hne : Not (z + (t : Complex) = 0)) :
    ContinuousAt (digammaReciprocalCurvature z) t := by
  have hh := ((((hasDerivAt_id (t : Complex)).const_add z).pow 3).inv
    (pow_ne_zero 3 hne)).const_mul 2
  convert hh.real_of_complex.continuousAt using 1
  funext x
  simp only [digammaReciprocalCurvature, div_eq_mul_inv, Pi.inv_apply, Pi.pow_apply, id_eq]

def digammaTrapezoidAntiderivative (z : Complex) (t : Real) : Real :=
  t * (1 - t) * digammaReciprocalSlope z t -
    (1 - 2 * t) * digammaReciprocalProfile z t

theorem digammaTrapezoidAntiderivative_hasDerivAt (z : Complex) (t : Real)
    (hne : Not (z + (t : Complex) = 0)) :
    HasDerivAt (digammaTrapezoidAntiderivative z)
      (t * (1 - t) * digammaReciprocalCurvature z t +
        2 * digammaReciprocalProfile z t) t := by
  have hw : HasDerivAt (fun x : Real => x * (1 - x)) (1 - 2 * t) t := by
    convert (hasDerivAt_id t).mul ((hasDerivAt_const t 1).sub (hasDerivAt_id t)) using 1 <;>
      first
      | (funext x; simp only [Pi.mul_apply, Pi.sub_apply, Pi.pow_apply, id_eq] <;> ring)
      | (simp only [Pi.mul_apply, Pi.sub_apply, id_eq]; ring)
  have hw' : HasDerivAt (fun x : Real => 1 - 2 * x) (-2) t := by
    convert (hasDerivAt_const t 1).sub ((hasDerivAt_id t).const_mul 2) using 1 <;>
      first
      | (funext x; simp only [Pi.sub_apply, id_eq] <;> ring)
      | ring
  have hh := (hw.mul (digammaReciprocalSlope_hasDerivAt z t hne)).sub
    (hw'.mul (digammaReciprocalProfile_hasDerivAt z t hne))
  change HasDerivAt (fun x : Real => x * (1 - x) * digammaReciprocalSlope z x -
    (1 - 2 * x) * digammaReciprocalProfile z x) _ t
  convert hh using 1 <;> ring

theorem digamma_trapezoid_identity (z : Complex) (hz : 0 < z.re) :
    (digammaReciprocalProfile z 0 + digammaReciprocalProfile z 1) / 2 -
      (intervalIntegral (digammaReciprocalProfile z) 0 1 volume) =
      (1 / 2 : Real) * intervalIntegral
        (fun t : Real => t * (1 - t) * digammaReciprocalCurvature z t) 0 1 volume := by
  have h0 (t : Real) (ht : Membership.mem (Set.uIcc (0 : Real) 1) t) : 0 <= t := by
    have hh : And (0 <= t) (t <= 1) := by simpa [Set.uIcc] using ht
    exact hh.1
  have hf : ContinuousOn (digammaReciprocalProfile z) (Set.uIcc (0 : Real) 1) := by
    intro t ht
    exact (digammaReciprocalProfile_hasDerivAt z t
      (digammaReciprocal_ne_zero z t hz (h0 t ht))).continuousAt.continuousWithinAt
  have hq : ContinuousOn (digammaReciprocalCurvature z) (Set.uIcc (0 : Real) 1) := by
    intro t ht
    exact (digammaReciprocalCurvature_continuousAt z t
      (digammaReciprocal_ne_zero z t hz (h0 t ht))).continuousWithinAt
  have hw : Continuous (fun t : Real => t * (1 - t)) :=
    continuous_id.mul (continuous_const.sub continuous_id)
  have hwi : IntervalIntegrable
      (fun t : Real => t * (1 - t) * digammaReciprocalCurvature z t) volume 0 1 :=
    (hw.continuousOn.mul hq).intervalIntegrable
  have hfi : IntervalIntegrable (digammaReciprocalProfile z) volume 0 1 := hf.intervalIntegrable
  have hderiv : forall t : Real, Membership.mem (Set.uIcc (0 : Real) 1) t ->
      HasDerivAt (digammaTrapezoidAntiderivative z)
        (t * (1 - t) * digammaReciprocalCurvature z t +
          2 * digammaReciprocalProfile z t) t := by
    intro t ht
    exact digammaTrapezoidAntiderivative_hasDerivAt z t
      (digammaReciprocal_ne_zero z t hz (h0 t ht))
  have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    (hwi.add (hfi.const_mul 2))
  rw [intervalIntegral.integral_add hwi (hfi.const_mul 2),
    intervalIntegral.integral_const_mul] at hint
  norm_num [digammaTrapezoidAntiderivative] at hint
  linarith only [hint]

theorem digammaReciprocalSlope_ofReal (u t : Real) :
    digammaReciprocalSlope (u : Complex) t = -1 / (u + t) ^ 2 := by
  simp [digammaReciprocalSlope, <- Complex.ofReal_add, <- Complex.ofReal_pow,
    Complex.div_ofReal_re]

theorem digammaReciprocalCurvature_ofReal (u t : Real) :
    digammaReciprocalCurvature (u : Complex) t = 2 / (u + t) ^ 3 := by
  simp [digammaReciprocalCurvature, <- Complex.ofReal_add, <- Complex.ofReal_pow,
    Complex.div_ofReal_re]

theorem digamma_trapezoid_error (z : Complex) (hz : 0 < z.re) :
    abs ((digammaReciprocalProfile z 0 + digammaReciprocalProfile z 1) / 2 -
      intervalIntegral (digammaReciprocalProfile z) 0 1 volume) <=
      1 / (8 * z.re ^ 2) - 1 / (8 * (z.re + 1) ^ 2) := by
  let E : Real -> Real := fun t =>
    (1 / 2) * (t * (1 - t) * digammaReciprocalCurvature z t)
  let M : Real -> Real := fun t =>
    (1 / 8) * digammaReciprocalCurvature (z.re : Complex) t
  let J : Real -> Real := fun t =>
    (1 / 8) * digammaReciprocalSlope (z.re : Complex) t
  have h0 (t : Real) (ht : Membership.mem (Set.uIcc (0 : Real) 1) t) : 0 <= t := by
    have hh : And (0 <= t) (t <= 1) := by simpa [Set.uIcc] using ht
    exact hh.1
  have hq : ContinuousOn (digammaReciprocalCurvature z) (Set.uIcc (0 : Real) 1) := by
    intro t ht
    exact (digammaReciprocalCurvature_continuousAt z t
      (digammaReciprocal_ne_zero z t hz (h0 t ht))).continuousWithinAt
  have hw : Continuous (fun t : Real => t * (1 - t)) :=
    continuous_id.mul (continuous_const.sub continuous_id)
  have hE : ContinuousOn E (Set.uIcc (0 : Real) 1) :=
    continuousOn_const.mul (hw.continuousOn.mul hq)
  have hMi : IntervalIntegrable M volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    intro t ht
    have hh := (digammaReciprocalCurvature_continuousAt (z.re : Complex) t
      (digammaReciprocal_ne_zero (z.re : Complex) t
        (by simpa only [Complex.ofReal_re] using hz) (h0 t ht))).const_mul (1 / 8 : Real)
    exact hh.continuousWithinAt
  have hJ : forall t : Real, Membership.mem (Set.uIcc (0 : Real) 1) t ->
      HasDerivAt J (M t) t := by
    intro t ht
    exact (digammaReciprocalSlope_hasDerivAt (z.re : Complex) t
      (digammaReciprocal_ne_zero (z.re : Complex) t
        (by simpa only [Complex.ofReal_re] using hz) (h0 t ht))).const_mul (1 / 8 : Real)
  have hIntM := intervalIntegral.integral_eq_sub_of_hasDerivAt hJ hMi
  have hEvalM : intervalIntegral M 0 1 volume =
      1 / (8 * z.re ^ 2) - 1 / (8 * (z.re + 1) ^ 2) := by
    rw [hIntM]
    dsimp only [J]
    rw [digammaReciprocalSlope_ofReal, digammaReciprocalSlope_ofReal]
    simp only [add_zero]
    field_simp [hz.ne', (by linarith only [hz] : Not (z.re + 1 = 0))] <;> ring
  have hTrap : (digammaReciprocalProfile z 0 + digammaReciprocalProfile z 1) / 2 -
      intervalIntegral (digammaReciprocalProfile z) 0 1 volume =
        intervalIntegral E 0 1 volume := by
    rw [digamma_trapezoid_identity z hz]
    exact (intervalIntegral.integral_const_mul (1 / 2 : Real) _).symm
  have hPoint (t : Real) (ht : Membership.mem (Set.Icc (0 : Real) 1) t) :
      abs (E t) <= M t := by
    have hw0 : 0 <= t * (1 - t) := mul_nonneg ht.1 (sub_nonneg.mpr ht.2)
    have hw1 : t * (1 - t) <= 1 / 4 := by nlinarith only [sq_nonneg (t - 1 / 2)]
    have hc := digammaReciprocalCurvature_abs_le z t hz ht.1
    have hQ : 0 <= 2 / (z.re + t) ^ 3 :=
      div_nonneg (by norm_num) (pow_nonneg (by linarith only [hz, ht.1]) 3)
    have hP0 := mul_nonneg hw0 (sub_nonneg.mpr hc)
    have hP1 := mul_nonneg (sub_nonneg.mpr hw1) hQ
    have hMt : M t = (1 / 8) * (2 / (z.re + t) ^ 3) := by
      dsimp only [M]
      rw [digammaReciprocalCurvature_ofReal]
    simp only [E, abs_mul, abs_of_pos (by norm_num : (0 : Real) < 1 / 2),
      abs_of_nonneg hw0]
    rw [hMt]
    nlinarith only [hP0, hP1]
  calc
    abs ((digammaReciprocalProfile z 0 + digammaReciprocalProfile z 1) / 2 -
        intervalIntegral (digammaReciprocalProfile z) 0 1 volume) =
        abs (intervalIntegral E 0 1 volume) := by rw [hTrap]
    _ <= intervalIntegral (fun t => abs (E t)) 0 1 volume :=
      intervalIntegral.abs_integral_le_integral_abs (by norm_num)
    _ <= intervalIntegral M 0 1 volume :=
      intervalIntegral.integral_mono_on (by norm_num) hE.abs.intervalIntegrable hMi hPoint
    _ = _ := hEvalM

theorem digammaReciprocal_integral (z : Complex) (hz : 0 < z.re) :
    intervalIntegral (digammaReciprocalProfile z) 0 1 volume =
      Real.log (norm (z + 1)) - Real.log (norm z) := by
  have hd : forall t : Real, Membership.mem (Set.uIcc (0 : Real) 1) t ->
      HasDerivAt (fun x : Real => Real.log (norm (z + (x : Complex))))
        (digammaReciprocalProfile z t) t := by
    intro t ht
    have hh : And (0 <= t) (t <= 1) := by simpa [Set.uIcc] using ht
    exact digammaReciprocal_log_primitive z t hz hh.1
  have hi : IntervalIntegrable (digammaReciprocalProfile z) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    intro t ht
    have hh : And (0 <= t) (t <= 1) := by simpa [Set.uIcc] using ht
    exact (digammaReciprocalProfile_hasDerivAt z t
      (digammaReciprocal_ne_zero z t hz hh.1)).continuousAt.continuousWithinAt
  simpa only [Complex.ofReal_one, Complex.ofReal_zero, add_zero] using
    intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi

theorem digammaReciprocalProfile_shift (z : Complex) (n t : Real) :
    digammaReciprocalProfile (z + (n : Complex)) t =
      digammaReciprocalProfile z (n + t) := by
  simp only [digammaReciprocalProfile, Complex.ofReal_add, add_assoc]

noncomputable def digammaTrapezoidSum (z : Complex) (N : Nat) : Real :=
  Finset.sum (Finset.range N) (fun n => digammaReciprocalProfile z (n : Real)) +
    (digammaReciprocalProfile z (N : Real) - digammaReciprocalProfile z 0) / 2 -
    Real.log (norm (z + (N : Complex))) + Real.log (norm z)

theorem digammaTrapezoidSum_succ (z : Complex) (N : Nat) :
    digammaTrapezoidSum z (N + 1) - digammaTrapezoidSum z N =
      (digammaReciprocalProfile z (N : Real) +
        digammaReciprocalProfile z ((N : Real) + 1)) / 2 -
      (Real.log (norm (z + (N : Complex) + 1)) -
        Real.log (norm (z + (N : Complex)))) := by
  simp only [digammaTrapezoidSum, Finset.sum_range_succ, Nat.cast_add,
    Nat.cast_one, add_assoc]
  ring

theorem digammaTrapezoidSum_succ_abs_le (z : Complex) (hz : 0 < z.re) (N : Nat) :
    abs (digammaTrapezoidSum z (N + 1) - digammaTrapezoidSum z N) <=
      1 / (8 * (z.re + N) ^ 2) - 1 / (8 * (z.re + N + 1) ^ 2) := by
  have hpos : 0 < (z + (N : Complex)).re := by
    simp only [Complex.add_re, Complex.natCast_re]
    positivity
  have he := digamma_trapezoid_error (z + (N : Complex)) hpos
  rw [digammaReciprocal_integral _ hpos] at he
  rw [digammaTrapezoidSum_succ]
  simpa only [digammaReciprocalProfile, Complex.ofReal_add, Complex.ofReal_natCast,
    Complex.ofReal_zero, Complex.ofReal_one, add_zero, Complex.add_re,
    Complex.natCast_re, add_assoc] using he

theorem digammaTrapezoidSum_abs_le (z : Complex) (hz : 0 < z.re) (N : Nat) :
    abs (digammaTrapezoidSum z N) <=
      1 / (8 * z.re ^ 2) - 1 / (8 * (z.re + N) ^ 2) := by
  induction N with
  | zero => simp [digammaTrapezoidSum]
  | succ N ih =>
    have hs := digammaTrapezoidSum_succ_abs_le z hz N
    have ha := abs_add_le (digammaTrapezoidSum z (N + 1) -
      digammaTrapezoidSum z N) (digammaTrapezoidSum z N)
    rw [sub_add_cancel] at ha
    have hb := ha.trans (add_le_add hs ih)
    convert hb using 1 <;> push_cast <;> ring

theorem digammaReciprocalProfile_nat_abs_le (z : Complex) (hz : 1 <= z.re) (N : Nat) :
    abs (digammaReciprocalProfile z (N : Real)) <= 1 / ((N : Real) + 1) := by
  have hp : (0 : Real) < (N : Real) + 1 := by positivity
  have hn : (N : Real) + 1 <= norm (z + (N : Complex)) := by
    have hh := Complex.re_le_norm (z + (N : Complex))
    simp only [Complex.add_re, Complex.natCast_re] at hh
    linarith only [hz, hh]
  calc
    abs (digammaReciprocalProfile z (N : Real)) <=
        norm (1 / (z + (N : Complex))) := by
      simpa only [digammaReciprocalProfile, Complex.ofReal_natCast] using
        Complex.abs_re_le_norm (1 / (z + (N : Complex)))
    _ = 1 / norm (z + (N : Complex)) := by rw [norm_div, norm_one]
    _ <= _ := one_div_le_one_div_of_le hp hn

theorem digammaReciprocalProfile_nat_tendsto (z : Complex) (hz : 1 <= z.re) :
    Filter.Tendsto (fun N : Nat => digammaReciprocalProfile z (N : Real))
      Filter.atTop (nhds 0) := by
  have hN : Filter.Tendsto (fun N : Nat => (N : Real) + 1)
      Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_mono (fun N => by linarith)
      (tendsto_natCast_atTop_atTop : Filter.Tendsto (fun N : Nat => (N : Real)) _ _)
  have hi : Filter.Tendsto (fun N : Nat => 1 / ((N : Real) + 1))
      Filter.atTop (nhds 0) := by
    simpa only [one_div, Function.comp_def] using tendsto_inv_atTop_zero.comp hN
  have hn := hi.neg
  simp only [neg_zero] at hn
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le hn hi
  all_goals intro N
  next =>
    simpa only [neg_neg] using
      neg_le_neg ((neg_le_abs _).trans (digammaReciprocalProfile_nat_abs_le z hz N))
  next =>
    exact (le_abs_self _).trans (digammaReciprocalProfile_nat_abs_le z hz N)

theorem digamma_log_norm_nat_tendsto (z : Complex) (hz : 1 <= z.re) :
    Filter.Tendsto (fun N : Nat => Real.log (norm (z + (N : Complex))) -
      Real.log ((N : Real) + 1)) Filter.atTop (nhds 0) := by
  have h1 := (Real.tendsto_log_comp_add_sub_log (norm z)).comp
    (tendsto_natCast_atTop_atTop : Filter.Tendsto (fun N : Nat => (N : Real)) _ _)
  have h2 := (Real.tendsto_log_comp_add_sub_log 1).comp
    (tendsto_natCast_atTop_atTop : Filter.Tendsto (fun N : Nat => (N : Real)) _ _)
  have hb : Filter.Tendsto (fun N : Nat => Real.log ((N : Real) + norm z) -
      Real.log ((N : Real) + 1)) Filter.atTop (nhds 0) := by
    convert h1.sub h2 using 1 <;>
      first | (funext N; simp only [Function.comp_apply]; ring) | ring
  apply squeeze_zero (fun N => ?_) (fun N => ?_) hb
  next =>
    have hp : (0 : Real) < (N : Real) + 1 := by positivity
    have hn : (N : Real) + 1 <= norm (z + (N : Complex)) := by
      have hh := Complex.re_le_norm (z + (N : Complex))
      simp only [Complex.add_re, Complex.natCast_re] at hh
      linarith only [hz, hh]
    exact sub_nonneg.mpr (Real.log_le_log hp hn)
  next =>
    apply sub_le_sub_right
    apply Real.log_le_log
    next =>
      exact norm_pos_iff.mpr (digammaReciprocal_ne_zero z (N : Real)
        (by linarith only [hz]) (Nat.cast_nonneg N))
    next =>
      have hh := norm_add_le z (N : Complex)
      simpa only [Complex.norm_natCast, add_comm] using hh

theorem digamma_harmonic_profile_tendsto (z : Complex) (hz : 0 < z.re) :
    Filter.Tendsto (fun N : Nat => Real.log ((N : Real) + 1) -
      Finset.sum (Finset.range N) (fun n => digammaReciprocalProfile z (n : Real)))
      Filter.atTop (nhds (digamma z).re) := by
  have hc := (Complex.continuous_re.tendsto _).comp
    (hasSum_digamma_of_re_pos hz).tendsto_sum_nat
  have he (N : Nat) :
      (Finset.sum (Finset.range N) (fun n : Nat =>
        ((n : Complex) + 1) ^ (-1 : Int) - (z + (n : Complex)) ^ (-1 : Int))).re =
      (harmonic N : Real) - Finset.sum (Finset.range N)
        (fun n => digammaReciprocalProfile z (n : Real)) := by
    rw [Finset.sum_sub_distrib]
    have hh : Finset.sum (Finset.range N)
        (fun n : Nat => ((n : Complex) + 1) ^ (-1 : Int)) =
        ((harmonic N : Rat) : Complex) := by
      simpa only [zpow_neg_one] using sum_inv_natCast_add_one N
    rw [hh, Complex.sub_re, Complex.ratCast_re]
    congr 1
    simpa only [Complex.coe_reAddGroupHom, digammaReciprocalProfile,
      Complex.ofReal_natCast, one_div, zpow_neg_one] using
      map_sum Complex.reAddGroupHom (fun n : Nat => (z + (n : Complex)) ^ (-1 : Int))
        (Finset.range N)
  have hr : Filter.Tendsto (fun N : Nat => (harmonic N : Real) -
      Finset.sum (Finset.range N) (fun n => digammaReciprocalProfile z (n : Real)))
      Filter.atTop (nhds ((digamma z).re + Real.eulerMascheroniConstant)) := by
    have he1 (N : Nat) := he N
    simp only [zpow_neg_one] at he1
    simpa only [Function.comp_def, he1, Complex.add_re, Complex.ofReal_re] using hc
  convert hr.sub Real.tendsto_harmonic_sub_log_add_one using 1 <;>
    first | (funext N; ring) | ring

theorem digamma_real_log_norm_remainder (z : Complex) (hz : 1 <= z.re) :
    abs ((digamma z).re - Real.log (norm z) +
      (1 / 2 : Real) * (1 / z).re) <= 1 / (8 * z.re ^ 2) := by
  have hsum := digamma_harmonic_profile_tendsto z (by linarith only [hz])
  have hlog := digamma_log_norm_nat_tendsto z hz
  have hprof := digammaReciprocalProfile_nat_tendsto z hz
  have hlim : Filter.Tendsto (digammaTrapezoidSum z) Filter.atTop
      (nhds (-((digamma z).re - Real.log (norm z) +
        (1 / 2 : Real) * (1 / z).re))) := by
    have hh := (((hsum.add hlog).neg.add
      ((hprof.sub_const (digammaReciprocalProfile z 0)).div_const 2)).add_const
        (Real.log (norm z)))
    convert hh using 1 <;> (first | funext N | skip) <;>
      dsimp [digammaTrapezoidSum, digammaReciprocalProfile] <;>
      simp only [Complex.ofReal_zero, add_zero, zero_sub] <;> ring
  have hb (N : Nat) : abs (digammaTrapezoidSum z N) <= 1 / (8 * z.re ^ 2) := by
    have hh := digammaTrapezoidSum_abs_le z (by linarith only [hz]) N
    have hn : 0 <= 1 / (8 * (z.re + N) ^ 2) := by positivity
    linarith only [hh, hn]
  have hh := le_of_tendsto hlim.abs (Filter.Eventually.of_forall hb)
  simpa only [abs_neg] using hh

end Complex

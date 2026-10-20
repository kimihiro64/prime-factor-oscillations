/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import PrimeNumberTheoremAnd.EulerMaclaurin

/-!
# RHFourierMean

Maintained extraction of completed detector/packet proof components.
All original theorem hypotheses and retained proof bodies are preserved.
This module alone asserts no improved zero-free boundary.
-/

set_option autoImplicit false
set_option Elab.async false

open Filter MeasureTheory
open scoped Topology

noncomputable section

namespace PrimeFactorOscillations

def logCharacter (v x : Real) : Complex :=
  Complex.exp ((v : Complex) * Complex.I * (Real.log x : Complex))

theorem norm_logCharacter (v x : Real) : norm (logCharacter v x) = 1 := by
  rw [logCharacter, Complex.norm_exp]
  simp [Complex.mul_re, Complex.mul_im]

theorem hasDerivAt_logCharacter (v x : Real) (hx : Not (x = 0)) :
    HasDerivAt (logCharacter v)
      (((v : Complex) * Complex.I) * logCharacter v x / (x : Complex)) x := by
  have hLog := Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt x (Real.hasDerivAt_log hx)
  have hExp := (hLog.const_mul ((v : Complex) * Complex.I)).cexp
  convert hExp using 1 <;>
    first | rfl | (simp [logCharacter, div_eq_mul_inv] <;> ring)

def harmonicCharacter (v x : Real) : Complex :=
  logCharacter v x / (x : Complex)

theorem hasDerivAt_harmonicCharacter (v x : Real) (hx : Not (x = 0)) :
    HasDerivAt (harmonicCharacter v)
      ((((v : Complex) * Complex.I) - 1) * logCharacter v x / (x : Complex) ^ 2) x := by
  have hId : HasDerivAt (fun t : Real => (t : Complex)) 1 x :=
    Complex.ofRealCLM.hasDerivAt
  have hxC : Not ((x : Complex) = 0) := by exact_mod_cast hx
  have h := (hasDerivAt_logCharacter v x hx).div hId hxC
  convert h using 1 <;> first | rfl | (field_simp [harmonicCharacter, hxC] <;> ring)

theorem norm_harmonicCharacter (v : Real) {x : Real} (hx : 0 < x) :
    norm (harmonicCharacter v x) = 1 / x := by
  simp only [harmonicCharacter, norm_div, norm_logCharacter, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hx]

theorem norm_deriv_harmonicCharacter (v : Real) {x : Real} (hx : 0 < x) :
    norm (deriv (harmonicCharacter v) x) =
      norm ((v : Complex) * Complex.I - 1) / x ^ 2 := by
  rw [(hasDerivAt_harmonicCharacter v x hx.ne').deriv,
    norm_div, norm_mul, norm_logCharacter, mul_one, norm_pow,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx]

theorem continuousOn_logCharacter (v : Real) :
    ContinuousOn (logCharacter v) (Set.Ioi (0 : Real)) := by
  intro x hx
  exact (hasDerivAt_logCharacter v x (ne_of_gt hx)).continuousAt.continuousWithinAt

theorem continuousOn_harmonicCharacter (v : Real) :
    ContinuousOn (harmonicCharacter v) (Set.Ioi (0 : Real)) := by
  intro x hx
  exact (hasDerivAt_harmonicCharacter v x (ne_of_gt hx)).continuousAt.continuousWithinAt

theorem continuousOn_deriv_harmonicCharacter (v : Real) :
    ContinuousOn (deriv (harmonicCharacter v)) (Set.Ioi (0 : Real)) := by
  have h : ContinuousOn (fun x : Real =>
      ((v : Complex) * Complex.I - 1) * logCharacter v x / (x : Complex) ^ 2)
      (Set.Ioi (0 : Real)) :=
    (continuousOn_const.mul (continuousOn_logCharacter v)).div
    (Complex.continuous_ofReal.continuousOn.pow 2)
    (fun x hx => pow_ne_zero 2 (by exact_mod_cast (ne_of_gt hx)))
  exact h.congr (fun x hx => (hasDerivAt_harmonicCharacter v x (ne_of_gt hx)).deriv)

theorem hasDerivAt_logCharacter_primitive (v : Real) (hv : Not (v = 0))
    (x : Real) (hx : Not (x = 0)) :
    HasDerivAt (fun t : Real => logCharacter v t / ((v : Complex) * Complex.I))
      (harmonicCharacter v x) x := by
  have hvC : Not ((v : Complex) = 0) := by exact_mod_cast hv
  have hxC : Not ((x : Complex) = 0) := by exact_mod_cast hx
  have h := (hasDerivAt_logCharacter v x hx).div_const ((v : Complex) * Complex.I)
  convert h using 1 <;> first | rfl | (dsimp only [harmonicCharacter]; field_simp [hvC, hxC] <;> ring)

theorem integral_harmonicCharacter_eq (v : Real) (hv : Not (v = 0))
    (M : Real) (hM : 1 <= M) :
    (intervalIntegral (harmonicCharacter v) 1 M volume) =
      (logCharacter v M - 1) / ((v : Complex) * Complex.I) := by
  have hsub : Set.Subset (Set.uIcc (1 : Real) M) (Set.Ioi (0 : Real)) := by
    rw [Set.uIcc_of_le hM]
    intro x hx
    exact lt_of_lt_of_le (by norm_num : (0 : Real) < 1) hx.1
  have hInt : IntervalIntegrable (harmonicCharacter v) volume 1 M :=
    ((continuousOn_harmonicCharacter v).mono hsub).intervalIntegrable
  have hDeriv := fun x (hx : Set.uIcc (1 : Real) M x) =>
    hasDerivAt_logCharacter_primitive v hv x (ne_of_gt (hsub hx))
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hDeriv hInt]
  have hOne : logCharacter v 1 = 1 := by simp [logCharacter]
  rw [hOne, sub_div]

def harmonicRemainder (v x : Real) : Complex :=
  deriv (harmonicCharacter v) x * (B1 x : Complex)

theorem integrableOn_harmonicRemainder (v : Real) :
    IntegrableOn (harmonicRemainder v) (Set.Ioi (1 : Real)) volume := by
  have hd : AEStronglyMeasurable (deriv (harmonicCharacter v))
      (volume.restrict (Set.Ioi (1 : Real))) :=
    ((continuousOn_deriv_harmonicCharacter v).mono
      (Set.Ioi_subset_Ioi (by norm_num : (0 : Real) <= 1))).aestronglyMeasurable
        measurableSet_Ioi
  have hb : AEStronglyMeasurable (fun x : Real => (B1 x : Complex))
      (volume.restrict (Set.Ioi (1 : Real))) :=
    Complex.continuous_ofReal.comp_aestronglyMeasurable
      (aestronglyMeasurable_B1.mono_measure Measure.restrict_le_self)
  have hMajor : IntegrableOn (fun x : Real =>
      (norm ((v : Complex) * Complex.I - 1) / 2) * x ^ (-2 : Real))
      (Set.Ioi (1 : Real)) volume :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : Real) < -1)
      (by norm_num : (0 : Real) < 1)).const_mul _
  apply hMajor.mono' (hd.mul hb)
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with x hx
  have hxPos : 0 < x := zero_lt_one.trans hx
  change norm (deriv (harmonicCharacter v) x * (B1 x : Complex)) <= _
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  calc
    norm (deriv (harmonicCharacter v) x) * abs (B1 x) <=
        norm (deriv (harmonicCharacter v) x) * (1 / 2) :=
      mul_le_mul_of_nonneg_left (abs_B1_le_half hxPos.le) (norm_nonneg _)
    _ = (norm ((v : Complex) * Complex.I - 1) / 2) * x ^ (-2 : Real) := by
      rw [norm_deriv_harmonicCharacter v hxPos, Real.rpow_neg hxPos.le]
      norm_num [div_eq_mul_inv, inv_pow] <;> ring

def harmonicRemainderMass (v : Real) : Real :=
  MeasureTheory.integral (volume.restrict (Set.Ioi (1 : Real)))
    (fun x : Real => norm (harmonicRemainder v x))

theorem harmonicRemainderMass_nonneg (v : Real) : 0 <= harmonicRemainderMass v :=
  integral_nonneg (fun _ => norm_nonneg _)

theorem norm_integral_harmonicRemainder_le (v M : Real) (hM : 1 <= M) :
    norm (intervalIntegral (harmonicRemainder v) 1 M volume) <= harmonicRemainderMass v := by
  calc
    _ <= intervalIntegral (fun x => norm (harmonicRemainder v x)) 1 M volume :=
      intervalIntegral.norm_integral_le_integral_norm hM
    _ = MeasureTheory.integral (volume.restrict (Set.Ioc (1 : Real) M))
        (fun x : Real => norm (harmonicRemainder v x)) :=
      intervalIntegral.integral_of_le hM
    _ <= harmonicRemainderMass v := by
      apply setIntegral_mono_set (integrableOn_harmonicRemainder v).norm
        (Filter.Eventually.of_forall (fun _ => norm_nonneg _))
      exact Filter.Eventually.of_forall (fun x hx => hx.1)

theorem harmonicCharacter_sum_sub_integral_bounded (v : Real) (N : Nat) (hN : 1 <= N) :
    norm (Finset.sum (Finset.Ioc 1 N) (fun n : Nat => harmonicCharacter v (n : Real)) -
      intervalIntegral (harmonicCharacter v) 1 (N : Real) volume) <=
        2 + harmonicRemainderMass v := by
  have hM : (1 : Real) <= N := by exact_mod_cast hN
  have hsub : Set.Subset (Set.uIcc (1 : Real) (N : Real)) (Set.Ioi (0 : Real)) := by
    rw [Set.uIcc_of_le hM]
    intro x hx
    exact zero_lt_one.trans_le hx.1
  have hDiff : forall x : Real, Set.Icc (1 : Real) (N : Real) x ->
      DifferentiableAt Real (harmonicCharacter v) x := by
    intro x hx
    exact (hasDerivAt_harmonicCharacter v x (ne_of_gt (zero_lt_one.trans_le hx.1))).differentiableAt
  have hEM := sum_eq_integral_add_integral_deriv (f := harmonicCharacter v)
    (by norm_num : (0 : Real) <= 1) hM hDiff
    ((continuousOn_deriv_harmonicCharacter v).mono hsub)
  have hOne : norm (harmonicCharacter v 1 * (B1 1 : Complex)) <= 1 := by
    norm_num [harmonicCharacter, logCharacter, B1]
  have hEnd : norm (harmonicCharacter v (N : Real) * (B1 (N : Real) : Complex)) <= 1 := by
    rw [norm_mul, norm_harmonicCharacter v (zero_lt_one.trans_le hM),
      Complex.norm_real, Real.norm_eq_abs]
    have hi : (1 : Real) / N <= 1 := (div_le_one (zero_lt_one.trans_le hM)).mpr hM
    have hb : abs (B1 (N : Real)) <= 1 :=
      (abs_B1_le_half (Nat.cast_nonneg N)).trans (by norm_num)
    have h := mul_le_mul hi hb (abs_nonneg _) (by norm_num : (0 : Real) <= 1)
    simpa only [one_mul] using h
  have hId : Finset.sum (Finset.Ioc 1 N) (fun n : Nat => harmonicCharacter v (n : Real)) -
      intervalIntegral (harmonicCharacter v) 1 (N : Real) volume =
      (harmonicCharacter v 1 * (B1 1 : Complex) -
        harmonicCharacter v (N : Real) * (B1 (N : Real) : Complex)) +
      intervalIntegral (harmonicRemainder v) 1 (N : Real) volume := by
    simp only [Nat.floor_one, Nat.floor_natCast] at hEM
    rw [hEM]
    unfold harmonicRemainder
    ring_nf
    rfl
  rw [hId]
  have hPair := (norm_sub_le
    (harmonicCharacter v 1 * (B1 1 : Complex))
    (harmonicCharacter v (N : Real) * (B1 (N : Real) : Complex))).trans
      (add_le_add hOne hEnd)
  have hRest := norm_integral_harmonicRemainder_le v (N : Real) hM
  exact (norm_add_le _ _).trans (by linarith only [hPair, hRest])

theorem exists_bound_harmonicCharacter_sum (v : Real) (hv : Not (v = 0)) :
    exists C : Real, 0 <= C /\ forall N : Nat, 1 <= N ->
      norm (Finset.sum (Finset.Ioc 1 N) (fun n : Nat => harmonicCharacter v (n : Real))) <= C := by
  refine Exists.intro (2 + harmonicRemainderMass v +
    2 / norm ((v : Complex) * Complex.I)) (And.intro ?_ ?_)
  . have hR := harmonicRemainderMass_nonneg v
    positivity
  . intro N hN
    have hM : (1 : Real) <= N := by exact_mod_cast hN
    have hI : norm (intervalIntegral (harmonicCharacter v) 1 (N : Real) volume) <=
        2 / norm ((v : Complex) * Complex.I) := by
      rw [integral_harmonicCharacter_eq v hv (N : Real) hM, norm_div]
      have h := norm_sub_le (logCharacter v (N : Real)) (1 : Complex)
      rw [norm_logCharacter, norm_one] at h
      norm_num at h
      exact div_le_div_of_nonneg_right h (norm_nonneg _)
    have hE := harmonicCharacter_sum_sub_integral_bounded v N hN
    have h := norm_add_le
      ((Finset.sum (Finset.Ioc 1 N) (fun n : Nat => harmonicCharacter v (n : Real))) -
        intervalIntegral (harmonicCharacter v) 1 (N : Real) volume)
      (intervalIntegral (harmonicCharacter v) 1 (N : Real) volume)
    rw [sub_add_cancel] at h
    linarith only [h, hE, hI]

/-- Every fixed nonzero logarithmic frequency has zero harmonic mean. -/
theorem tendsto_harmonicCharacter_mean_of_ne (v : Real) (hv : Not (v = 0)) :
    Tendsto (fun N : Nat =>
      Finset.sum (Finset.Ioc 1 N) (fun n : Nat => harmonicCharacter v (n : Real)) /
        (Real.log (N : Real) : Complex)) atTop (nhds 0) := by
  choose C hC hBound using exists_bound_harmonicCharacter_sum v hv
  have hLog : Tendsto (fun N : Nat => Real.log (N : Real)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hZero : Tendsto (fun N : Nat => C / Real.log (N : Real)) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop hLog
  apply squeeze_zero_norm' ?_ hZero
  filter_upwards [eventually_ge_atTop (2 : Nat)] with N hN
  have hM : (1 : Real) < N := by exact_mod_cast (show 1 < N by omega)
  have hLogPos := Real.log_pos hM
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hLogPos]
  exact div_le_div_of_nonneg_right (hBound N (by omega)) hLogPos.le

theorem integral_harmonicCharacter_zero (M : Real) (hM : 1 <= M) :
    intervalIntegral (harmonicCharacter 0) 1 M volume = (Real.log M : Complex) := by
  have hsub : Set.Subset (Set.uIcc (1 : Real) M) (Set.Ioi (0 : Real)) := by
    rw [Set.uIcc_of_le hM]
    intro x hx
    exact zero_lt_one.trans_le hx.1
  have hInt : IntervalIntegrable (harmonicCharacter 0) volume 1 M :=
    ((continuousOn_harmonicCharacter 0).mono hsub).intervalIntegrable
  have hDeriv : forall x : Real, Set.uIcc (1 : Real) M x ->
      HasDerivAt (fun t : Real => (Real.log t : Complex)) (harmonicCharacter 0 x) x := by
    intro x hx
    have h := Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt x
      (Real.hasDerivAt_log (ne_of_gt (hsub hx)))
    convert h using 1 <;> first | rfl | (simp [harmonicCharacter, logCharacter])
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hDeriv hInt]
  simp

theorem tendsto_harmonicCharacter_mean_zero :
    Tendsto (fun N : Nat =>
      Finset.sum (Finset.Ioc 1 N) (fun n : Nat => harmonicCharacter 0 (n : Real)) /
        (Real.log (N : Real) : Complex)) atTop (nhds 1) := by
  have hLog : Tendsto (fun N : Nat => Real.log (N : Real)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hZero : Tendsto (fun N : Nat =>
      (2 + harmonicRemainderMass 0) / Real.log (N : Real)) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop hLog
  have hMean : Tendsto (fun N : Nat =>
      Finset.sum (Finset.Ioc 1 N) (fun n : Nat => harmonicCharacter 0 (n : Real)) /
        (Real.log (N : Real) : Complex) - 1) atTop (nhds 0) := by
    apply squeeze_zero_norm' ?_ hZero
    filter_upwards [eventually_ge_atTop (2 : Nat)] with N hN
    have hM : (1 : Real) < N := by exact_mod_cast (show 1 < N by omega)
    have hLogPos := Real.log_pos hM
    have hLogC : Not ((Real.log (N : Real) : Complex) = 0) := by
      exact_mod_cast hLogPos.ne'
    have hB := harmonicCharacter_sum_sub_integral_bounded 0 N (by omega)
    rw [integral_harmonicCharacter_zero (N : Real) hM.le] at hB
    have hId : Finset.sum (Finset.Ioc 1 N)
          (fun n : Nat => harmonicCharacter 0 (n : Real)) /
            (Real.log (N : Real) : Complex) - 1 =
        (Finset.sum (Finset.Ioc 1 N) (fun n : Nat => harmonicCharacter 0 (n : Real)) -
          (Real.log (N : Real) : Complex)) / (Real.log (N : Real) : Complex) := by
      field_simp [hLogC]
    rw [hId, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hLogPos]
    exact div_le_div_of_nonneg_right hB hLogPos.le
  simpa only [sub_add_cancel, zero_add] using hMean.add_const (1 : Complex)

/-- Harmonic logarithmic averaging isolates exactly the zero frequency. -/
theorem tendsto_harmonicCharacter_mean (v : Real) :
    Tendsto (fun N : Nat =>
      Finset.sum (Finset.Ioc 1 N) (fun n : Nat => harmonicCharacter v (n : Real)) /
        (Real.log (N : Real) : Complex)) atTop (nhds (if v = 0 then 1 else 0)) := by
  classical
  by_cases hv : v = 0
  . subst v
    simpa using tendsto_harmonicCharacter_mean_zero
  . simpa [hv] using tendsto_harmonicCharacter_mean_of_ne v hv

def harmonicCharacterMean (v : Real) (N : Nat) : Complex :=
  Finset.sum (Finset.Ioc 1 N) (fun n : Nat => harmonicCharacter v (n : Real)) /
    (Real.log (N : Real) : Complex)

/-- One eventual bound holds simultaneously for every real frequency. -/
theorem eventually_norm_harmonicCharacterMean_le_two :
    Filter.Eventually (fun N : Nat => forall v : Real,
      norm (harmonicCharacterMean v N) <= 2) atTop := by
  have hReal : Tendsto (fun N : Nat => (harmonicCharacterMean 0 N).re) atTop (nhds 1) := by
    simpa only [harmonicCharacterMean, Function.comp_def, Complex.one_re] using
      (Complex.continuous_re.tendsto (1 : Complex)).comp tendsto_harmonicCharacter_mean_zero
  have hSmall := hReal.eventually
    (eventually_le_nhds (by norm_num : (1 : Real) < 2))
  filter_upwards [hSmall, eventually_ge_atTop (2 : Nat)] with N hs hN
  intro v
  have hM : (1 : Real) < N := by exact_mod_cast (show 1 < N by omega)
  have hLog := Real.log_pos hM
  have hTriangle := norm_sum_le (Finset.Ioc 1 N)
    (fun n : Nat => harmonicCharacter v (n : Real))
  have hEach : Finset.sum (Finset.Ioc 1 N)
      (fun n : Nat => norm (harmonicCharacter v (n : Real))) =
      (Finset.sum (Finset.Ioc 1 N) (fun n : Nat => harmonicCharacter 0 (n : Real))).re := by
    rw [Complex.re_sum]
    apply Finset.sum_congr rfl
    intro n hn
    have hnPos : (0 : Real) < n := by
      exact_mod_cast (zero_lt_one.trans (Finset.mem_Ioc.mp hn).1)
    rw [norm_harmonicCharacter v hnPos]
    have hZero : harmonicCharacter 0 (n : Real) = ((1 / (n : Real) : Real) : Complex) := by
      simp [harmonicCharacter, logCharacter]
    rw [hZero, Complex.ofReal_re]
  rw [hEach] at hTriangle
  have hCompare : norm (harmonicCharacterMean v N) <= (harmonicCharacterMean 0 N).re := by
    rw [harmonicCharacterMean, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hLog]
    calc
      _ <= (Finset.sum (Finset.Ioc 1 N)
          (fun n : Nat => harmonicCharacter 0 (n : Real))).re / Real.log (N : Real) :=
        div_le_div_of_nonneg_right hTriangle hLog.le
      _ = _ := by rw [harmonicCharacterMean, Complex.div_ofReal_re]
  exact hCompare.trans hs

/-- Harmonic averaging extracts the zero-frequency fiber of every absolutely
summable complex spectrum. No frequency separation is assumed. -/
theorem tendsto_tsum_harmonicCharacterMean {J : Type*}
    (a : J -> Complex) (f : J -> Real) (ha : Summable (fun j : J => norm (a j))) :
    Tendsto (fun N : Nat => tsum (fun j : J => a j * harmonicCharacterMean (f j) N))
      atTop (nhds (tsum (fun j : J => if f j = 0 then a j else 0))) := by
  classical
  refine tendsto_tsum_of_dominated_convergence
    (bound := fun j : J => 2 * norm (a j)) (ha.mul_left 2) ?_ ?_
  . intro j
    have hConst : Tendsto (fun _ : Nat => a j) atTop (nhds (a j)) := tendsto_const_nhds
    have h := hConst.mul (tendsto_harmonicCharacter_mean (f j))
    change Tendsto (fun N : Nat => a j * harmonicCharacterMean (f j) N) atTop
      (nhds (a j * (if f j = 0 then 1 else 0))) at h
    simpa only [mul_ite, mul_one, mul_zero] using h
  . filter_upwards [eventually_norm_harmonicCharacterMean_le_two] with N hN
    intro j
    rw [norm_mul]
    have h := mul_le_mul_of_nonneg_left (hN (f j)) (norm_nonneg (a j))
    simpa only [mul_comm] using h

theorem logCharacter_sub (v w x : Real) :
    logCharacter (v - w) x = logCharacter v x * logCharacter (-w) x := by
  unfold logCharacter
  rw [<- Complex.exp_add]
  congr 1 <;> push_cast <;> ring

def logSpectrum {J : Type*} (a : J -> Complex) (f : J -> Real) (x : Real) : Complex :=
  tsum (fun j : J => a j * logCharacter (f j) x)

theorem summable_logSpectrum {J : Type*} (a : J -> Complex) (f : J -> Real)
    (ha : Summable (fun j : J => norm (a j))) (x : Real) :
    Summable (fun j : J => a j * logCharacter (f j) x) := by
  apply ha.of_norm_bounded
  intro j
  rw [norm_mul, norm_logCharacter, mul_one]

def harmonicSpectrumMean {J : Type*} (a : J -> Complex) (f : J -> Real)
    (w : Real) (N : Nat) : Complex :=
  Finset.sum (Finset.Ioc 1 N) (fun n : Nat =>
    logSpectrum a f (n : Real) * logCharacter (-w) (n : Real) / (n : Complex)) /
      (Real.log (N : Real) : Complex)

theorem harmonicSpectrumMean_eq_tsum {J : Type*} (a : J -> Complex) (f : J -> Real)
    (ha : Summable (fun j : J => norm (a j))) (w : Real) (N : Nat) :
    harmonicSpectrumMean a f w N =
      tsum (fun j : J => a j * harmonicCharacterMean (f j - w) N) := by
  have hS : forall n : Nat,
      Summable (fun j : J => a j * harmonicCharacter (f j - w) (n : Real)) := by
    intro n
    have h := (summable_logSpectrum a (fun j : J => f j - w) ha (n : Real)).div_const
      (n : Complex)
    convert h using 1
    funext j
    dsimp only [harmonicCharacter]
    push_cast
    ring
  have hTerm : forall n : Nat,
      logSpectrum a f (n : Real) * logCharacter (-w) (n : Real) / (n : Complex) =
      tsum (fun j : J => a j * harmonicCharacter (f j - w) (n : Real)) := by
    intro n
    unfold logSpectrum
    rw [<- tsum_mul_right, <- tsum_div_const]
    apply tsum_congr
    intro j
    dsimp only [harmonicCharacter]
    rw [logCharacter_sub]
    push_cast
    ring
  have hSwap := Summable.tsum_finsetSum (s := Finset.Ioc (1 : Nat) N)
    (f := fun (n : Nat) (j : J) => a j * harmonicCharacter (f j - w) (n : Real))
    (fun n _ => hS n)
  calc
    harmonicSpectrumMean a f w N =
        tsum (fun j : J => Finset.sum (Finset.Ioc 1 N)
          (fun n : Nat => a j * harmonicCharacter (f j - w) (n : Real))) /
            (Real.log (N : Real) : Complex) := by
      unfold harmonicSpectrumMean
      simp_rw [hTerm]
      rw [<- hSwap]
    _ = _ := by
      rw [<- tsum_div_const]
      apply tsum_congr
      intro j
      unfold harmonicCharacterMean
      rw [<- Finset.mul_sum, mul_div_assoc]

/-- Finite harmonic observations recover each frequency fiber of an arbitrary
absolutely summable logarithmic spectrum. -/
theorem tendsto_harmonicSpectrumMean {J : Type*}
    (a : J -> Complex) (f : J -> Real) (ha : Summable (fun j : J => norm (a j))) (w : Real) :
    Tendsto (harmonicSpectrumMean a f w) atTop
      (nhds (tsum (fun j : J => if f j = w then a j else 0))) := by
  have hId : harmonicSpectrumMean a f w =
      (fun N : Nat => tsum (fun j : J => a j * harmonicCharacterMean (f j - w) N)) :=
    funext (fun N => harmonicSpectrumMean_eq_tsum a f ha w N)
  rw [hId]
  simpa only [sub_eq_zero] using
    tendsto_tsum_harmonicCharacterMean a (fun j : J => f j - w) ha

end PrimeFactorOscillations

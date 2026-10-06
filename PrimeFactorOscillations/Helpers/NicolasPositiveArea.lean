/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.NicolasPowerPersistence

/-!
# A positive-area criterion equivalent to RH

The positive part of the actual Nicolas logarithm is integrated over [x,2x].
Under RH its late area is zero. Every off-line zeta zero instead forces
arbitrarily large power-log excesses through the maintained interval theorem.
Consequently an eventual x^(1/4) times fixed logarithmic-power upper bound
is equivalent to RH. Nonnegative integration keeps all inequalities valid
before a finite-area upper bound is assumed; no prime-gap input is required.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

open Filter MeasureTheory Set Robin1984

/-- Nonnegative Lebesgue area of the positive Nicolas error on [x,2x].
The conversion ofReal includes the positive-part truncation. -/
def nicolasPositiveArea (x : Real) : ENNReal :=
  lintegral (volume.restrict (Icc x (2 * x)))
    (fun y : Real => ENNReal.ofReal (nicolasLogMertensOscillation y))

theorem nicolasPositiveArea_lower_of_window
    (x A b d : Real) (hx : 1 <= x) (hA : 0 <= A) (hd : d <= 1)
    (hWindow : forall y : Real, x <= y -> y <= x + x ^ d ->
      A * x ^ (-b) <= nicolasLogMertensOscillation y) :
    ENNReal.ofReal (A * x ^ (d - b)) <= nicolasPositiveArea x := by
  have hxPos : 0 < x := by linarith
  have hLength : x ^ d <= x := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hx hd
  have hSet : Icc x (x + x ^ d) <= Icc x (2 * x) := by
    intro y hy
    exact And.intro hy.1 (by linarith [hy.2])
  have hPoint : Filter.Eventually
      (fun y : Real => ENNReal.ofReal (A * x ^ (-b)) <=
        ENNReal.ofReal (nicolasLogMertensOscillation y))
      (ae (volume.restrict (Icc x (x + x ^ d)))) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
    exact ENNReal.ofReal_le_ofReal (hWindow y hy.1 hy.2)
  have hIntegral := lintegral_mono_ae hPoint
  simp only [lintegral_const, Measure.restrict_apply_univ, Real.volume_Icc,
    add_sub_cancel_left] at hIntegral
  rw [<- ENNReal.ofReal_mul (by positivity : 0 <= A * x ^ (-b))] at hIntegral
  have hPower : A * x ^ (-b) * x ^ d = A * x ^ (d - b) := by
    rw [mul_assoc, <- Real.rpow_add hxPos]
    congr 1
    ring
  rw [hPower] at hIntegral
  exact hIntegral.trans (lintegral_mono_set hSet)

theorem nicolasPositiveArea_eq_zero_of_nonpos
    (x : Real)
    (hNonpos : forall y : Real, x <= y -> y <= 2 * x ->
      nicolasLogMertensOscillation y <= 0) :
    nicolasPositiveArea x = 0 := by
  have hEq : Filter.EventuallyEq (ae (volume.restrict (Icc x (2 * x))))
      (fun y : Real => ENNReal.ofReal (nicolasLogMertensOscillation y))
      (fun _ : Real => (0 : ENNReal)) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
    exact ENNReal.ofReal_eq_zero.mpr (hNonpos y hy.1 hy.2)
  exact (lintegral_congr_ae hEq).trans lintegral_zero

theorem eventually_nicolasPositiveArea_eq_zero_of_RH (hRH : RiemannHypothesis) :
    Filter.Eventually (fun x : Real => nicolasPositiveArea x = 0) atTop := by
  have hNegative := eventually_nicolasLog_lt_neg_div_of_RH hRH 0
  choose X hX using eventually_atTop.mp hNegative
  apply eventually_atTop.mpr
  refine Exists.intro X ?_
  intro x hx
  apply nicolasPositiveArea_eq_zero_of_nonpos
  intro y hyl _hyu
  have h := hX y (hx.trans hyl)
  simpa only [neg_zero, zero_div] using h.le

theorem exists_nicolasPositiveArea_excess_of_power_intervals
    (b d a C B X : Real) (ha : a < d - b) (hd : d <= 1) (hC : 0 < C)
    (hIntervals : forall Y : Real, exists n : Nat, Y < (n : Real) /\ 6 <= n /\
      forall y : Real, (n : Real) <= y -> y <= n + (n : Real) ^ d ->
        (n : Real) ^ (-b) < nicolasLogMertensOscillation y) :
    exists n : Nat, X < (n : Real) /\ 6 <= n /\
      ENNReal.ofReal (C * (n : Real) ^ a * (Real.log (n : Real)) ^ B) <
        nicolasPositiveArea (n : Real) := by
  let e : Real := d - b - a
  have he : 0 < e := by dsimp [e]; linarith
  have hDecay : Tendsto
      (fun x : Real => C * ((Real.log x) ^ B / x ^ e)) atTop (nhds 0) := by
    have h := ((isLittleO_log_rpow_rpow_atTop B he).tendsto_div_nhds_zero).const_mul C
    simpa only [mul_zero] using h
  choose Y hY using eventually_atTop.mp
    (hDecay.eventually_lt_const (by norm_num : (0 : Real) < 1))
  choose n hn hnSix hWindow using hIntervals (max X Y)
  have hnX : X < (n : Real) := (le_max_left X Y).trans_lt hn
  have hnY : Y <= (n : Real) := (le_max_right X Y).trans hn.le
  have hnPos : (0 : Real) < n := by
    have hSix : (6 : Real) <= n := by exact_mod_cast hnSix
    linarith
  have hPowerPos : 0 < (n : Real) ^ e := Real.rpow_pos_of_pos hnPos _
  have h := mul_lt_mul_of_pos_right (hY (n : Real) hnY) hPowerPos
  have hCancel :
      (C * ((Real.log (n : Real)) ^ B / (n : Real) ^ e)) * (n : Real) ^ e =
      C * (Real.log (n : Real)) ^ B := by field_simp [hPowerPos.ne']
  rw [hCancel, one_mul] at h
  have hScaled := mul_lt_mul_of_pos_left h (Real.rpow_pos_of_pos hnPos a)
  have hPowers : (n : Real) ^ a * (n : Real) ^ e = (n : Real) ^ (d - b) := by
    rw [<- Real.rpow_add hnPos]
    congr 1
    dsimp [e]
    ring
  rw [hPowers] at hScaled
  have hStrict : C * (n : Real) ^ a * (Real.log (n : Real)) ^ B <
      (n : Real) ^ (d - b) := by nlinarith only [hScaled]
  have hArea := nicolasPositiveArea_lower_of_window (n : Real) 1 b d
    (by exact_mod_cast (show 1 <= n by omega)) (by norm_num) hd
    (fun y hyl hyu => by simpa only [one_mul] using (hWindow y hyl hyu).le)
  simp only [one_mul] at hArea
  refine Exists.intro n (And.intro hnX (And.intro hnSix ?_))
  exact ((ENNReal.ofReal_lt_ofReal_iff (Real.rpow_pos_of_pos hnPos _)).mpr hStrict).trans_le hArea

theorem exists_nicolasPositiveArea_excess_of_zero
    {rho : Complex} (hZero : riemannZeta rho = 0)
    (hHalf : (1 / 2 : Real) < rho.re) (hOne : rho.re < 1)
    {b : Real} (hLower : 1 - rho.re < b) (hbHalf : b <= 1 / 2)
    (a C B X : Real) (ha : a < 1 - 3 * b / 2) (hC : 0 < C) :
    exists n : Nat, X < (n : Real) /\ 6 <= n /\
      ENNReal.ofReal (C * (n : Real) ^ a * (Real.log (n : Real)) ^ B) <
        nicolasPositiveArea (n : Real) := by
  let d : Real := ((a + b) + (1 - b / 2)) / 2
  have hb : 0 < b := by linarith
  have hd : d < 1 - b / 2 := by dsimp [d]; linarith
  apply exists_nicolasPositiveArea_excess_of_power_intervals b d a C B X
    (by dsimp [d]; linarith) (by linarith) hC
  intro Y
  choose n hn hnSix hWindow using nicolasLog_power_intervals_of_zero
    hZero hHalf hOne hLower hbHalf d 1 Y hd (by norm_num)
  exact Exists.intro n (And.intro hn (And.intro hnSix
    (fun y hyl hyu => by simpa only [one_mul] using hWindow y hyl hyu)))

/-- RH is equivalent to an eventual quarter-power, fixed-polylogarithmic
upper bound for the actual positive Nicolas area. All analytic inputs are
proved; the right-hand bound itself is not asserted unconditionally. -/
theorem riemannHypothesis_iff_nicolasPositiveArea_bound :
    RiemannHypothesis <->
      exists C B X : Real, 0 < C /\ forall x : Real, X <= x ->
        nicolasPositiveArea x <=
          ENNReal.ofReal (C * x ^ (1 / 4 : Real) * (Real.log x) ^ B) := by
  constructor
  . intro hRH
    choose X hX using eventually_atTop.mp (eventually_nicolasPositiveArea_eq_zero_of_RH hRH)
    refine Exists.intro 1 (Exists.intro 0 (Exists.intro X (And.intro (by norm_num) ?_)))
    intro x hx
    rw [hX x hx]
    exact bot_le
  . intro hArea
    by_contra hNotRH
    choose C B X hC hBound using hArea
    choose b hb hbHalf hIntervals using exists_nicolasLog_power_intervals_of_not_RH hNotRH
    have hSupply : forall Y : Real, exists n : Nat, Y < (n : Real) /\ 6 <= n /\
        forall y : Real, (n : Real) <= y -> y <= n + (n : Real) ^ (3 / 4 : Real) ->
          (n : Real) ^ (-b) < nicolasLogMertensOscillation y := by
      intro Y
      choose n hn hnSix hWindow using hIntervals (3 / 4) 1 Y
        (by linarith) (by norm_num)
      exact Exists.intro n (And.intro hn (And.intro hnSix
        (fun y hyl hyu => by simpa only [one_mul] using hWindow y hyl hyu)))
    choose n hn _hnSix hExcess using exists_nicolasPositiveArea_excess_of_power_intervals
      b (3 / 4) (1 / 4) C B X (by linarith) (by norm_num) hC hSupply
    exact (not_lt_of_ge (hBound (n : Real) hn.le)) hExcess

/-- A hypothesized positive-area power-log bound limits the real parts of
nontrivial zeros. This theorem does not prove the area bound. -/
theorem zeta_re_le_of_nicolasPositiveArea_bound
    (a C B X : Real) (ha : (1 / 4 : Real) <= a) (hC : 0 < C)
    (hBound : forall x : Real, X <= x ->
      nicolasPositiveArea x <= ENNReal.ofReal (C * x ^ a * (Real.log x) ^ B))
    {rho : Complex} (hZero : riemannZeta rho = 0)
    (hHalf : (1 / 2 : Real) < rho.re) (hOne : rho.re < 1) :
    rho.re <= (1 + 2 * a) / 3 := by
  by_contra hNot
  have hStrict : (1 + 2 * a) / 3 < rho.re := lt_of_not_ge hNot
  let b : Real := ((1 - rho.re) + 2 * (1 - a) / 3) / 2
  have hLower : 1 - rho.re < b := by dsimp [b]; linarith
  have hbHalf : b <= 1 / 2 := by dsimp [b]; linarith
  have hExponent : a < 1 - 3 * b / 2 := by dsimp [b]; linarith
  choose n hn _hnSix hExcess using exists_nicolasPositiveArea_excess_of_zero
    hZero hHalf hOne hLower hbHalf a C B X hExponent hC
  exact (not_lt_of_ge (hBound (n : Real) hn.le)) hExcess

/-- Bounds at every exponent above a imply the limiting zero restriction. -/
theorem zeta_re_le_of_nicolasPositiveArea_subpower_bound
    (a : Real) (ha : (1 / 4 : Real) <= a)
    (hBound : forall e : Real, 0 < e ->
      exists C X : Real, 0 < C /\ forall x : Real, X <= x ->
        nicolasPositiveArea x <= ENNReal.ofReal (C * x ^ (a + e)))
    {rho : Complex} (hZero : riemannZeta rho = 0)
    (hHalf : (1 / 2 : Real) < rho.re) (hOne : rho.re < 1) :
    rho.re <= (1 + 2 * a) / 3 := by
  by_contra hNot
  have hStrict : (1 + 2 * a) / 3 < rho.re := lt_of_not_ge hNot
  let e : Real := (3 * rho.re - 1 - 2 * a) / 4
  have he : 0 < e := by dsimp [e]; linarith
  choose C X hC hAt using hBound e he
  have hNew := zeta_re_le_of_nicolasPositiveArea_bound (a + e) C 0 X
    (by linarith) hC (fun x hx => by simpa only [Real.rpow_zero, mul_one] using hAt x hx)
    hZero hHalf hOne
  dsimp [e] at hNew
  linarith

end PrimeFactorOscillations

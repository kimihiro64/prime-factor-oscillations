/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import OAI.NumberTheory.DirichletL.Detector.EulerRegion
import OAI.NumberTheory.DirichletL.Detector.HighEulerRational
import OAI.NumberTheory.DirichletL.Hecke.Euler

/-!
# Unramified Euler correction in the extended region

Proves the exact marked cancellation and the uniform summable local defect.
The product is analytic along analytic paths satisfying the stated real-part
bounds. This does not supply the global signed packet estimate.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace PrimeFactorOscillations.FullEulerContinuation

def markedCorrection (t V W D R K : Complex) : Complex :=
  OAI.SevenEighths.ProbeEuler.markedFactor R V t K (-D + W * R) 1

def fullFactor (t V W D R K : Complex) : Complex :=
  OAI.SevenEighths.ProbeLocal.continuedCorrection V W D
    (markedCorrection t V W D R K)

theorem marked_cancellation (t V W D R K : Complex)
    (hV : Not (1 - V = 0)) (hR : Not (1 - R = 0)) :
    markedCorrection t V W D R K + D =
      (R * (1 - t) + (1 - V) * (W * R - D * R) - K * V) /
        ((1 - V) * (1 - R)) := by
  dsimp only [markedCorrection, OAI.SevenEighths.ProbeEuler.markedFactor]
  simp only [pow_one]
  field_simp [hV, hR]
  ring

theorem full_cancellation (t V W D R K : Complex)
    (hD : Not (1 - D = 0)) :
    fullFactor t V W D R K - 1 =
      (D * V + D * W - D * V * W - V * W +
        (1 - V) * (1 - W) * (markedCorrection t V W D R K + D)) / (1 - D) := by
  dsimp only [fullFactor, OAI.SevenEighths.ProbeLocal.continuedCorrection]
  field_simp [hD]
  ring

private theorem half_denominator (v : Complex) (hv : norm v <= 1 / 2) :
    1 / 2 <= norm (1 - v) := by
  have h := norm_sub_norm_le (1 : Complex) v
  simp only [norm_one] at h
  linarith

private theorem upper_denominator (v : Complex) (hv : norm v <= 1) :
    norm (1 - v) <= 2 := by
  have h := norm_sub_le (1 : Complex) v
  simp only [norm_one] at h
  linarith

private theorem norm_div_from_lower (a b : Complex) (c T : Real)
    (hc : 0 < c) (hb : c <= norm b) (ha : norm a <= c * T) :
    norm (a / b) <= T := by
  rw [norm_div]
  have hb0 : Not (norm b = 0) := ne_of_gt (lt_of_lt_of_le hc hb)
  have hcancel : norm a / norm b * norm b = norm a := by field_simp
  have hn : 0 <= norm a / norm b := div_nonneg (norm_nonneg _) (norm_nonneg _)
  have hprod := mul_nonneg hn (sub_nonneg.mpr hb)
  nlinarith

theorem full_factor_bound (t V W D R K : Complex) (T : Real)
    (ht : norm t <= 1) (hV : norm V <= 1 / 2) (hW : norm W <= 1 / 2)
    (hD : norm D <= 1 / 2) (hR : norm R <= 1 / 2)
    (hRT : norm R <= T) (hKV : norm (K * V) <= T)
    (hDV : norm (D * V) <= T) (hDW : norm (D * W) <= T)
    (hVW : norm (V * W) <= T) :
    norm (fullFactor t V W D R K - 1) <= 200 * T := by
  have hT : 0 <= T := (norm_nonneg R).trans hRT
  have hbV := half_denominator V hV
  have hbR := half_denominator R hR
  have hbD := half_denominator D hD
  have hnV : Not (1 - V = 0) := by
    intro h
    rw [h, norm_zero] at hbV
    linarith
  have hnR : Not (1 - R = 0) := by
    intro h
    rw [h, norm_zero] at hbR
    linarith
  have hnD : Not (1 - D = 0) := by
    intro h
    rw [h, norm_zero] at hbD
    linarith
  have huV : norm (1 - V) <= 2 := upper_denominator V (by linarith)
  have huW : norm (1 - W) <= 2 := upper_denominator W (by linarith)
  have hut : norm (1 - t) <= 2 := upper_denominator t ht
  have hWR : norm (W * R) <= T / 2 := by
    rw [norm_mul]
    calc
      norm W * norm R <= (1 / 2) * T :=
        mul_le_mul hW hRT (norm_nonneg _) (by norm_num)
      _ = T / 2 := by ring
  have hDR : norm (D * R) <= T / 2 := by
    rw [norm_mul]
    calc
      norm D * norm R <= (1 / 2) * T :=
        mul_le_mul hD hRT (norm_nonneg _) (by norm_num)
      _ = T / 2 := by ring
  have hdiff : norm (W * R - D * R) <= T :=
    (norm_sub_le _ _).trans (by linarith)
  have hfirst : norm (R * (1 - t)) <= 2 * T := by
    rw [norm_mul, mul_comm]
    exact mul_le_mul hut hRT (norm_nonneg _) (by norm_num)
  have hsecond : norm ((1 - V) * (W * R - D * R)) <= 2 * T := by
    rw [norm_mul]
    exact mul_le_mul huV hdiff (norm_nonneg _) (by norm_num)
  have hnum :
      norm (R * (1 - t) + (1 - V) * (W * R - D * R) - K * V) <= 5 * T := by
    have h1 := norm_add_le (R * (1 - t)) ((1 - V) * (W * R - D * R))
    have h2 := norm_sub_le
      (R * (1 - t) + (1 - V) * (W * R - D * R)) (K * V)
    linarith
  have hden : 1 / 4 <= norm ((1 - V) * (1 - R)) := by
    rw [norm_mul]
    nlinarith [mul_nonneg (show 0 <= norm (1 - V) - 1 / 2 by linarith)
      (show 0 <= norm (1 - R) - 1 / 2 by linarith)]
  have hE : norm (markedCorrection t V W D R K + D) <= 20 * T := by
    rw [marked_cancellation t V W D R K hnV hnR]
    exact norm_div_from_lower _ _ (1 / 4) (20 * T)
      (by norm_num) hden (by linarith)
  have hDVW : norm (D * V * W) <= T := by
    rw [norm_mul]
    exact (mul_le_of_le_one_right (norm_nonneg _) (show norm W <= 1 by linarith)).trans hDV
  have hpoly : norm (D * V + D * W - D * V * W - V * W) <= 4 * T := by
    have h1 := norm_add_le (D * V) (D * W)
    have h2 := norm_sub_le (D * V + D * W) (D * V * W)
    have h3 := norm_sub_le (D * V + D * W - D * V * W) (V * W)
    linarith
  have hmult : norm ((1 - V) * (1 - W)) <= 4 := by
    rw [norm_mul]
    nlinarith [mul_nonneg (show 0 <= 2 - norm (1 - V) by linarith)
      (show 0 <= 2 - norm (1 - W) by linarith)]
  have herror :
      norm ((1 - V) * (1 - W) * (markedCorrection t V W D R K + D)) <= 80 * T := by
    rw [norm_mul]
    calc
      _ <= 4 * (20 * T) := mul_le_mul hmult hE (norm_nonneg _) (by norm_num)
      _ = 80 * T := by ring
  rw [full_cancellation t V W D R K hnD]
  apply norm_div_from_lower _ _ (1 / 2) (200 * T) (by norm_num) hbD
  have h := norm_add_le (D * V + D * W - D * V * W - V * W)
    ((1 - V) * (1 - W) * (markedCorrection t V W D R K + D))
  linarith

private theorem rpow_half_bound (Q : Real) (hQ : 4 <= Q) :
    Q ^ (-(1 / 2) : Real) <= 1 / 2 := by
  exact OAI.SevenEighths.ProbeEuler.rpow_le_half Q _ hQ (by norm_num)

private theorem norm_mul_rpow (Q : Real) (hQ : 1 <= Q) (x y : Complex)
    (a b c : Real) (hx : norm x <= Q ^ a) (hy : norm y <= Q ^ b)
    (hab : a + b <= c) :
    norm (x * y) <= Q ^ c := by
  have hQpos : 0 < Q := by linarith
  rw [norm_mul]
  calc
    _ <= Q ^ a * Q ^ b :=
      mul_le_mul hx hy (norm_nonneg _) (Real.rpow_nonneg hQpos.le _)
    _ = Q ^ (a + b) := (Real.rpow_add hQpos _ _).symm
    _ <= Q ^ c := Real.rpow_le_rpow_of_exponent_le hQ hab

theorem unramified_uniform_defect (Q : Real) (A eta v s w z : Complex)
    (hQ : 4 <= Q) (hA : norm A <= 1)
    (heta : norm eta <= 1) (hv : norm v <= 1)
    (hs : 3 / 4 <= s.re) (hw : 19 / 20 <= w.re) (hz : 33 / 200 <= z.re) :
    norm (OAI.SevenEighths.ProbeEuler.unramifiedClosed Q A eta v s w z - 1) <=
      200 * Q ^ (-(149 / 100) : Real) := by
  have hQpos : 0 < Q := by linarith
  have hQ1 : 1 <= Q := by linarith
  let V := OAI.SevenEighths.ProbeEuler.coordV Q z
  let W := OAI.SevenEighths.ProbeEuler.coordW Q v w
  let D := OAI.SevenEighths.ProbeEuler.coordD Q eta v s
  let R := OAI.SevenEighths.ProbeEuler.coordR Q A s z
  let K := OAI.SevenEighths.ProbeEuler.coordK Q eta s w
  have hVN : norm V <= Q ^ (-6 * z.re) := by
    exact (OAI.SevenEighths.ProbeEuler.coordV_norm Q hQpos z).le
  have hWN : norm W <= Q ^ (-w.re) :=
    OAI.SevenEighths.ProbeEuler.coordW_norm_le Q hQpos v w hv
  have hDN : norm D <= Q ^ (-s.re) :=
    OAI.SevenEighths.ProbeEuler.coordD_norm_le Q hQpos eta v s heta hv
  have hRN : norm R <= Q ^ (4 - 6 * s.re - 6 * z.re) :=
    OAI.SevenEighths.ProbeEuler.coordR_norm_le Q hQpos A s z hA
  have hKN : norm K <= Q ^ (1 - s.re - w.re) :=
    OAI.SevenEighths.ProbeEuler.coordK_norm_le Q hQ1 eta s w heta
  have hbase := rpow_half_bound Q hQ
  have hVhalf : norm V <= 1 / 2 :=
    hVN.trans ((Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith)).trans hbase)
  have hWhalf : norm W <= 1 / 2 :=
    hWN.trans ((Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith)).trans hbase)
  have hDhalf : norm D <= 1 / 2 :=
    hDN.trans ((Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith)).trans hbase)
  have hRhalf : norm R <= 1 / 2 :=
    hRN.trans ((Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith)).trans hbase)
  have hRT : norm R <= Q ^ (-(149 / 100) : Real) :=
    hRN.trans (Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith))
  have hKVT : norm (K * V) <= Q ^ (-(149 / 100) : Real) :=
    norm_mul_rpow Q hQ1 K V _ _ _ hKN hVN (by linarith)
  have hDVT : norm (D * V) <= Q ^ (-(149 / 100) : Real) :=
    norm_mul_rpow Q hQ1 D V _ _ _ hDN hVN (by linarith)
  have hDWT : norm (D * W) <= Q ^ (-(149 / 100) : Real) :=
    norm_mul_rpow Q hQ1 D W _ _ _ hDN hWN (by linarith)
  have hVWT : norm (V * W) <= Q ^ (-(149 / 100) : Real) :=
    norm_mul_rpow Q hQ1 V W _ _ _ hVN hWN (by linarith)
  have ht : norm (Inv.inv (Q : Complex)) <= 1 := by
    simp only [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hQpos]
    have hc : Inv.inv Q * Q = 1 := by field_simp
    have hn : 0 <= Inv.inv Q := inv_nonneg.mpr hQpos.le
    nlinarith [mul_nonneg hn (sub_nonneg.mpr hQ1)]
  change norm (fullFactor (Inv.inv (Q : Complex)) V W D R K - 1) <= _
  exact full_factor_bound _ V W D R K _ ht hVhalf hWhalf hDhalf hRhalf
    hRT hKVT hDVT hDWT hVWT


theorem fullFactor_analyticAt
    (t V W D R K : Complex -> Complex) (x : Complex)
    (ht : AnalyticAt Complex t x) (hV : AnalyticAt Complex V x)
    (hW : AnalyticAt Complex W x) (hD : AnalyticAt Complex D x)
    (hR : AnalyticAt Complex R x) (hK : AnalyticAt Complex K x)
    (hnV : Not (1 - V x = 0)) (hnR : Not (1 - R x = 0))
    (hnD : Not (1 - D x = 0)) :
    AnalyticAt Complex
      (fun y => fullFactor (t y) (V y) (W y) (D y) (R y) (K y)) x := by
  have hnum : AnalyticAt Complex
      (fun y => R y * (1 - t y) - K y * V y) x := by fun_prop
  have hdenV : AnalyticAt Complex (fun y => 1 - V y) x := by fun_prop
  have hdenR : AnalyticAt Complex (fun y => 1 - R y) x := by fun_prop
  have hdenD : AnalyticAt Complex (fun y => 1 - D y) x := by fun_prop
  have hquot : AnalyticAt Complex
      (fun y => (R y * (1 - t y) - K y * V y) / (1 - V y)) x := by
    apply AnalyticAt.div
    . exact hnum
    . exact hdenV
    . exact hnV
  have hJ : AnalyticAt Complex (fun y => -D y + W y * R y) x := by fun_prop
  have hmarked : AnalyticAt Complex
      (fun y => markedCorrection (t y) (V y) (W y) (D y) (R y) (K y)) x := by
    dsimp only [markedCorrection, OAI.SevenEighths.ProbeEuler.markedFactor]
    simp only [pow_one]
    apply AnalyticAt.div
    . apply AnalyticAt.add
      . exact hquot
      . exact hJ
    . exact hdenR
    . exact hnR
  have htop : AnalyticAt Complex
      (fun y => 1 - V y * W y +
        (1 - V y) * (1 - W y) *
          markedCorrection (t y) (V y) (W y) (D y) (R y) (K y)) x := by fun_prop
  apply AnalyticAt.div
  . exact htop
  . exact hdenD
  . exact hnD

private theorem positive_cpow_eq_exp (Q : Real) (hQ : 0 < Q) (v : Complex) :
    (Q : Complex) ^ v = Complex.exp (v * (Real.log Q : Complex)) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (ne_of_gt hQ)),
    <- Complex.ofReal_log hQ.le, mul_comm]

theorem unramified_analyticAt (Q : Real) (A eta v : Complex)
    (s w z : Complex -> Complex) (x : Complex)
    (hQ : 4 <= Q) (hA : norm A <= 1)
    (heta : norm eta <= 1) (hv : norm v <= 1)
    (hs : AnalyticAt Complex s x) (hw : AnalyticAt Complex w x)
    (hz : AnalyticAt Complex z x)
    (hsRe : 3 / 4 <= (s x).re) (hzRe : 33 / 200 <= (z x).re) :
    AnalyticAt Complex
      (fun y => OAI.SevenEighths.ProbeEuler.unramifiedClosed Q A eta v
        (s y) (w y) (z y)) x := by
  have hQpos : 0 < Q := by linarith
  have hQ1 : 1 <= Q := by linarith
  have hpow (f : Complex -> Complex) (hf : AnalyticAt Complex f x) :
      AnalyticAt Complex (fun y => (Q : Complex) ^ (f y)) x := by
    have heq : (fun y => (Q : Complex) ^ (f y)) =
        (fun y => Complex.exp (f y * (Real.log Q : Complex))) := by
      funext y
      exact positive_cpow_eq_exp Q hQpos (f y)
    rw [heq]
    fun_prop
  let V := fun y => OAI.SevenEighths.ProbeEuler.coordV Q (z y)
  let W := fun y => OAI.SevenEighths.ProbeEuler.coordW Q v (w y)
  let D := fun y => OAI.SevenEighths.ProbeEuler.coordD Q eta v (s y)
  let R := fun y => OAI.SevenEighths.ProbeEuler.coordR Q A (s y) (z y)
  let K := fun y => OAI.SevenEighths.ProbeEuler.coordK Q eta (s y) (w y)
  have hV : AnalyticAt Complex V x := by
    exact hpow (fun y => -6 * z y) (by fun_prop)
  have hW : AnalyticAt Complex W x := by
    have h := hpow (fun y => -w y) (by fun_prop)
    change AnalyticAt Complex (fun y => v * (Q : Complex) ^ (-w y)) x
    apply AnalyticAt.mul
    . fun_prop
    . exact h
  have hD : AnalyticAt Complex D x := by
    have h := hpow (fun y => -s y) (by fun_prop)
    change AnalyticAt Complex (fun y => (eta * star v) * (Q : Complex) ^ (-s y)) x
    apply AnalyticAt.mul
    . fun_prop
    . exact h
  have hR : AnalyticAt Complex R x := by
    have h := hpow (fun y => 4 - 6 * s y - 6 * z y) (by fun_prop)
    change AnalyticAt Complex
      (fun y => A * (Q : Complex) ^ (4 - 6 * s y - 6 * z y)) x
    apply AnalyticAt.mul
    . fun_prop
    . exact h
  have hK : AnalyticAt Complex K x := by
    have h := hpow (fun y => -s y - w y) (by fun_prop)
    change AnalyticAt Complex
      (fun y => (eta * ((Q : Complex) - 1)) * (Q : Complex) ^ (-s y - w y)) x
    apply AnalyticAt.mul
    . fun_prop
    . exact h
  have hbase := rpow_half_bound Q hQ
  have hVhalf : norm (V x) <= 1 / 2 := by
    have h := (OAI.SevenEighths.ProbeEuler.coordV_norm Q hQpos (z x)).le
    exact h.trans ((Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith)).trans hbase)
  have hDhalf : norm (D x) <= 1 / 2 := by
    have h := OAI.SevenEighths.ProbeEuler.coordD_norm_le Q hQpos eta v (s x) heta hv
    exact h.trans ((Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith)).trans hbase)
  have hRhalf : norm (R x) <= 1 / 2 := by
    have h := OAI.SevenEighths.ProbeEuler.coordR_norm_le Q hQpos A (s x) (z x) hA
    exact h.trans ((Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith)).trans hbase)
  have hnonzero (b : Complex) (hb : norm b <= 1 / 2) : Not (1 - b = 0) := by
    have hden := half_denominator b hb
    intro h
    rw [h, norm_zero] at hden
    linarith
  exact fullFactor_analyticAt (fun _ => Inv.inv (Q : Complex)) V W D R K x
    (by fun_prop) hV hW hD hR hK
    (hnonzero _ hVhalf) (hnonzero _ hRhalf) (hnonzero _ hDhalf)

theorem analyticOnNhd_unramifiedProduct {I : Type*}
    (Q : I -> Real) (A eta v : I -> Complex)
    (s w z : Complex -> Complex) (U : Set Complex)
    (hQ : forall i, 4 <= Q i)
    (hA : forall i, norm (A i) <= 1)
    (heta : forall i, norm (eta i) <= 1) (hv : forall i, norm (v i) <= 1)
    (hsum : Summable (fun i => Q i ^ (-(149 / 100) : Real)))
    (hU : IsOpen U) (hs : AnalyticOnNhd Complex s U)
    (hw : AnalyticOnNhd Complex w U) (hz : AnalyticOnNhd Complex z U)
    (hRe : forall x, Membership.mem U x ->
      3 / 4 <= (s x).re /\ 19 / 20 <= (w x).re /\ 33 / 200 <= (z x).re) :
    AnalyticOnNhd Complex
      (fun x => tprod (fun i =>
        OAI.SevenEighths.ProbeEuler.unramifiedClosed (Q i) (A i) (eta i) (v i)
          (s x) (w x) (z x))) U := by
  apply DifferentiableOn.analyticOnNhd _ hU
  intro x hx
  classical
  have hb := Metric.mem_nhds_iff.mp (hU.mem_nhds hx)
  let r0 : Real := Classical.choose hb
  have hr0 : 0 < r0 := (Classical.choose_spec hb).1
  have hball : Set.Subset (Metric.ball x r0) U := (Classical.choose_spec hb).2
  let r : Real := r0 / 2
  have hr : 0 < r := by dsimp [r]; linarith
  let K0 : Set Complex := Metric.closedBall x r
  have hKU : Set.Subset K0 U := by
    intro y hy
    apply hball
    change dist y x < r0
    have hd : dist y x <= r := Metric.mem_closedBall.mp hy
    dsimp [r] at hd
    linarith
  let f : I -> Complex -> Complex := fun i y =>
    OAI.SevenEighths.ProbeEuler.unramifiedClosed (Q i) (A i) (eta i) (v i)
      (s y) (w y) (z y)
  have hana (i : I) (y : Complex) (hy : Membership.mem U y) :
      AnalyticAt Complex (f i) y :=
    unramified_analyticAt (Q i) (A i) (eta i) (v i) s w z y
      (hQ i) (hA i) (heta i) (hv i) (hs y hy) (hw y hy) (hz y hy)
      (hRe y hy).1 (hRe y hy).2.2
  have hbound : forall i, forall y, Membership.mem K0 y ->
      norm (f i y - 1) <= 200 * Q i ^ (-(149 / 100) : Real) := by
    intro i y hy
    have h := hRe y (hKU hy)
    exact unramified_uniform_defect (Q i) (A i) (eta i) (v i) (s y) (w y) (z y)
      (hQ i) (hA i) (heta i) (hv i) h.1 h.2.1 h.2.2
  have hcts : forall i, ContinuousOn (fun y => f i y - 1) K0 := by
    intro i y hy
    exact ((hana i y (hKU hy)).continuousAt.sub continuousAt_const).continuousWithinAt
  have hp : HasProdUniformlyOn f (fun y => tprod (fun i => f i y)) K0 := by
    have h := Summable.hasProdUniformlyOn_one_add
      (f := fun i y => f i y - 1) (isCompact_closedBall x r)
      (hsum.mul_left 200) (Filter.Eventually.of_forall hbound) hcts
    simpa only [add_sub_cancel] using h
  have hlim : TendstoLocallyUniformlyOn
      (fun F : Finset I => fun y => F.prod (fun i => f i y))
      (fun y => tprod (fun i => f i y)) Filter.atTop (Metric.ball x r) :=
    (hp.mono Metric.ball_subset_closedBall).hasProdLocallyUniformlyOn
  have hfin : forall F : Finset I,
      DifferentiableOn Complex (fun y => F.prod (fun i => f i y)) (Metric.ball x r) := by
    intro F y hy
    have hyU : Membership.mem U y := hKU (Metric.ball_subset_closedBall hy)
    have hprod : DifferentiableAt Complex (fun a => F.prod (fun i => f i a)) y := by
      induction F using Finset.induction_on with
      | empty =>
        simp only [Finset.prod_empty]
        fun_prop
      | @insert i F hi ih =>
        simp only [Finset.prod_insert hi]
        apply DifferentiableAt.mul
        . exact (hana i y hyU).differentiableAt
        . exact ih
    exact hprod.differentiableWithinAt
  have hd := hlim.differentiableOn (Filter.Eventually.of_forall hfin) Metric.isOpen_ball
  have hcenter : Membership.mem (Metric.ball x r) x := by simpa using hr
  exact ((hd x hcenter).differentiableAt
    (Metric.isOpen_ball.mem_nhds hcenter)).differentiableWithinAt

abbrev SourcePrime := OAI.SmoothMobiusCorrection.PrimeIdeal
abbrev SourceCharacter := OAI.SevenEighths.HeckeFamily.Character

def sourceNorm (P : SourcePrime) : Real := (Ideal.absNorm P.val : Real)

def HighSourcePrime (S : Finset SourcePrime) : Type :=
  {P : SourcePrime // Real.exp 2 <= sourceNorm P /\ Not (Membership.mem S P)}

theorem source_norm_majorant_summable :
    Summable (fun P : SourcePrime => sourceNorm P ^ (-(149 / 100) : Real)) := by
  have hfull := OAI.CubicEisenstein.fullIdealWeight_summable_norm
    (149 / 100 : Complex) (by norm_num)
  have hprime : Summable (fun P : SourcePrime =>
      norm (OAI.CubicEisenstein.fullIdealWeight (149 / 100 : Complex) P.val)) :=
    hfull.comp_injective Subtype.val_injective
  apply hprime.congr
  intro P
  have hPpos := OAI.SmoothMobiusCorrection.prime_norm_pos P
  rw [OAI.CubicEisenstein.fullIdealWeight, ite_eq_right P.property.ne_zero]
  rw [<- Complex.ofReal_natCast (Ideal.absNorm P.val),
    Complex.norm_cpow_eq_rpow_re_of_pos hPpos]
  have hre : (-(149 / 100 : Complex)).re = (-(149 / 100) : Real) := by norm_num
  rw [hre]
  rfl

theorem analyticOnNhd_sourceUnramifiedProduct
    (S : Finset SourcePrime) (eta : SourceCharacter)
    (v : HighSourcePrime S -> Complex) (hv : forall P, norm (v P) <= 1)
    (s w z : Complex -> Complex) (U : Set Complex)
    (hU : IsOpen U) (hs : AnalyticOnNhd Complex s U)
    (hw : AnalyticOnNhd Complex w U) (hz : AnalyticOnNhd Complex z U)
    (hRe : forall x, Membership.mem U x ->
      3 / 4 <= (s x).re /\ 19 / 20 <= (w x).re /\ 33 / 200 <= (z x).re) :
    AnalyticOnNhd Complex (fun x => tprod (fun P : HighSourcePrime S =>
      OAI.SevenEighths.ProbeEuler.unramifiedClosed (sourceNorm P.val)
        (OAI.SevenEighths.ProbeEuler.actualAPhase eta
          (OAI.CompletedGauss.primaryGenerator P.val.val))
        (OAI.SevenEighths.HeckeFamily.idealCoeff eta P.val.val) (v P)
        (s x) (w x) (z x))) U :=
  analyticOnNhd_unramifiedProduct
    (fun P : HighSourcePrime S => sourceNorm P.val)
    (fun P => OAI.SevenEighths.ProbeEuler.actualAPhase eta
      (OAI.CompletedGauss.primaryGenerator P.val.val))
    (fun P => OAI.SevenEighths.HeckeFamily.idealCoeff eta P.val.val) v
    s w z U (fun P => (show (4 : Real) <= Real.exp 2 by
      have he := Real.add_one_le_exp (1 : Real)
      rw [show (2 : Real) = 1 + 1 by norm_num, Real.exp_add]
      nlinarith [sq_nonneg (Real.exp 1 - 2)]).trans P.property.1)
    (fun P => OAI.SevenEighths.ProbeEuler.actualAPhase_norm_le_one eta
      (OAI.CompletedGauss.primaryGenerator P.val.val))
    (fun P => OAI.SevenEighths.HeckeFamily.idealCoeff_norm_le_one eta P.val.val) hv
    (source_norm_majorant_summable.comp_injective Subtype.val_injective)
    hU hs hw hz hRe
end PrimeFactorOscillations.FullEulerContinuation

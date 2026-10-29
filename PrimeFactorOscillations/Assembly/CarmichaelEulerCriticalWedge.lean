/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.CarmichaelUnitEulerRenormalization

/-!
# Convex geometry of the signed Euler numerator

The exact numerator has positive real part when its two coordinates lie
inside the unit disk. The resulting bounds retain all angular phases.
The full signed high packet and its reciprocal L-function are not bounded here.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 800000

noncomputable section
namespace PrimeFactorOscillations.CarmichaelEulerCriticalWedge
open scoped Classical
open OAI OAI.SevenEighths ProbeEuler
open CarmichaelUnitEulerRenormalization

def safetyMargin (delta : Real) : Real := 1 - (2 : Real) ^ (-delta)

theorem convex_numerator_re_lower (t b : Real) (D R : Complex)
    (ht0 : 0 <= t) (ht1 : t <= 1) (hD : D.re <= b) (hR : R.re <= b) :
    1 - b <= (1 - ((1 - t : Real) : Complex) * D - (t : Complex) * R).re := by
  have h1 := mul_nonneg (sub_nonneg.mpr ht1) (sub_nonneg.mpr hD)
  have h2 := mul_nonneg ht0 (sub_nonneg.mpr hR)
  simp only [Complex.sub_re, Complex.one_re, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  nlinarith

theorem convex_numerator_re_pos (t : Real) (D R : Complex)
    (ht0 : 0 <= t) (ht1 : t <= 1) (hD : norm D < 1) (hR : norm R < 1) :
    0 < (1 - ((1 - t : Real) : Complex) * D - (t : Complex) * R).re := by
  have hb : max (norm D) (norm R) < 1 := max_lt hD hR
  have hl := convex_numerator_re_lower t (max (norm D) (norm R)) D R ht0 ht1
    ((Complex.re_le_norm D).trans (le_max_left _ _))
    ((Complex.re_le_norm R).trans (le_max_right _ _))
  linarith

private theorem decay_lt_one (delta : Real) (hd : 0 < delta) :
    (2 : Real) ^ (-delta) < 1 := by
  rw [Real.rpow_def_of_pos (by norm_num)]
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  calc
    Real.exp (Real.log 2 * (-delta)) < Real.exp 0 := by
      apply Real.exp_lt_exp.mpr
      nlinarith [mul_pos hd hlog]
    _ = 1 := Real.exp_zero

private theorem margin_pos (delta : Real) (hd : 0 < delta) :
    0 < safetyMargin delta := by
  dsimp [safetyMargin]
  linarith [decay_lt_one delta hd]

private theorem decay_comparison (Q delta : Real) (hQ : 2 <= Q) (hd : 0 < delta) :
    Q ^ (-delta) <= (2 : Real) ^ (-delta) := by
  have hQ0 : 0 < Q := by linarith
  have hlog : Real.log 2 <= Real.log Q := Real.log_le_log (by norm_num) hQ
  rw [Real.rpow_def_of_pos hQ0, Real.rpow_def_of_pos (by norm_num)]
  apply Real.exp_le_exp.mpr
  nlinarith [mul_nonneg hd.le (sub_nonneg.mpr hlog)]

private theorem coordinate_decay (Q : Real) (A eta s z : Complex) (delta : Real)
    (hQ : 2 <= Q) (hA : norm A <= 1) (heta : norm eta <= 1)
    (hs : delta <= s.re) (hsz : delta <= 6 * s.re + 6 * z.re - 4) :
    norm (coordD Q eta 1 s) <= Q ^ (-delta) /\
      norm (coordR Q A s z) <= Q ^ (-delta) := by
  have hQ0 : 0 < Q := by linarith
  have hQ1 : 1 <= Q := by linarith
  exact And.intro
    ((coordD_norm_le Q hQ0 eta 1 s heta (by simp)).trans
      (Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith)))
    ((coordR_norm_le Q hQ0 A s z hA).trans
      (Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith)))

private theorem coordinate_D_ne_one (Q : Real) (A eta s z : Complex) (delta : Real)
    (hQ : 2 <= Q) (hA : norm A <= 1) (heta : norm eta <= 1)
    (hd : 0 < delta) (hs : delta <= s.re)
    (hsz : delta <= 6 * s.re + 6 * z.re - 4) :
    Not (1 - coordD Q eta 1 s = 0) := by
  have hn := (coordinate_decay Q A eta s z delta hQ hA heta hs hsz).1
  have hlt := (hn.trans (decay_comparison Q delta hQ hd)).trans_lt
    (decay_lt_one delta hd)
  intro h
  have he : (1 : Complex) = coordD Q eta 1 s := sub_eq_zero.mp h
  rw [<- he, norm_one] at hlt
  exact (lt_irrefl (1 : Real)) hlt

private theorem remainder_numerator (Q : Real) (A eta s z : Complex)
    (hD : Not (1 - coordD Q eta 1 s = 0)) :
    localRemainder Q A eta s z * (1 - coordD Q eta 1 s) =
      1 - ((1 - 1 / Q : Real) : Complex) * coordD Q eta 1 s -
        ((1 / Q : Real) : Complex) * coordR Q A s z := by
  simp only [localRemainder, Complex.ofReal_sub, Complex.ofReal_div, Complex.ofReal_one]
  field_simp [hD] <;> ring

theorem local_remainder_lower_wedge (Q : Real) (A eta s z : Complex) (delta : Real)
    (hQ : 2 <= Q) (hA : norm A <= 1) (heta : norm eta <= 1)
    (hd : 0 < delta) (hs : delta <= s.re)
    (hsz : delta <= 6 * s.re + 6 * z.re - 4) :
    safetyMargin delta / 2 <= norm (localRemainder Q A eta s z) := by
  have hQ0 : 0 < Q := by linarith
  have ht0 : 0 <= 1 / Q := by positivity
  have ht1 : 1 / Q <= 1 := (div_le_one hQ0).mpr (by linarith)
  have hc := coordinate_decay Q A eta s z delta hQ hA heta hs hsz
  have hD := hc.1.trans (decay_comparison Q delta hQ hd)
  have hR := hc.2.trans (decay_comparison Q delta hQ hd)
  have hnum := convex_numerator_re_lower (1 / Q) ((2 : Real) ^ (-delta))
    (coordD Q eta 1 s) (coordR Q A s z) ht0 ht1
    ((Complex.re_le_norm _).trans hD) ((Complex.re_le_norm _).trans hR)
  have hnorm := hnum.trans (Complex.re_le_norm _)
  rw [<- remainder_numerator Q A eta s z
    (coordinate_D_ne_one Q A eta s z delta hQ hA heta hd hs hsz), norm_mul] at hnorm
  have hden : norm (1 - coordD Q eta 1 s) <= 2 := by
    have h := norm_sub_le (1 : Complex) (coordD Q eta 1 s)
    rw [norm_one] at h
    linarith [decay_lt_one delta hd]
  have hm := mul_le_mul_of_nonneg_left hden (norm_nonneg (localRemainder Q A eta s z))
  dsimp [safetyMargin]
  nlinarith

theorem local_remainder_defect_wedge (Q : Real) (A eta s z : Complex) (delta : Real)
    (hQ : 2 <= Q) (hA : norm A <= 1) (heta : norm eta <= 1)
    (hd : 0 < delta) (hs : delta <= s.re)
    (hsz : delta <= 6 * s.re + 6 * z.re - 4) :
    norm (localRemainder Q A eta s z - 1) <=
      (2 / safetyMargin delta) * Q ^ (-(1 + delta)) := by
  have hQ0 : 0 < Q := by linarith
  have hm : 0 < safetyMargin delta := margin_pos delta hd
  have hc := coordinate_decay Q A eta s z delta hQ hA heta hs hsz
  have hD := hc.1.trans (decay_comparison Q delta hQ hd)
  have hden : safetyMargin delta <= norm (1 - coordD Q eta 1 s) := by
    have h := norm_sub_norm_le (1 : Complex) (coordD Q eta 1 s)
    rw [norm_one] at h
    dsimp [safetyMargin]
    linarith
  have hsum : norm (coordD Q eta 1 s - coordR Q A s z) <= 2 * Q ^ (-delta) :=
    (norm_sub_le _ _).trans (by linarith [hc.1, hc.2])
  have ht : norm (Inv.inv (Q : Complex)) = Q ^ (-(1 : Real)) := by
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hQ0, Real.rpow_neg_one]
  have hn : norm (Inv.inv (Q : Complex) *
      (coordD Q eta 1 s - coordR Q A s z)) <= 2 * Q ^ (-(1 + delta)) := by
    rw [norm_mul, ht]
    calc
      _ <= Q ^ (-(1 : Real)) * (2 * Q ^ (-delta)) :=
        mul_le_mul_of_nonneg_left hsum (Real.rpow_nonneg hQ0.le _)
      _ = 2 * Q ^ (-(1 + delta)) := by
        rw [mul_left_comm, <- Real.rpow_add hQ0]
        congr 2 <;> ring
  unfold localRemainder
  rw [add_sub_cancel_left, norm_div]
  calc
    _ <= norm (Inv.inv (Q : Complex) *
        (coordD Q eta 1 s - coordR Q A s z)) / safetyMargin delta :=
      div_le_div_of_nonneg_left (norm_nonneg _) hm hden
    _ <= (2 * Q ^ (-(1 + delta))) / safetyMargin delta :=
      div_le_div_of_nonneg_right hn hm.le
    _ = _ := by ring


theorem local_remainder_analyticAt_wedge (Q : Real) (A eta : Complex)
    (s z : Complex -> Complex) (x : Complex) (delta : Real)
    (hQ : 2 <= Q) (hA : norm A <= 1) (heta : norm eta <= 1)
    (hd : 0 < delta) (hs : AnalyticAt Complex s x) (hz : AnalyticAt Complex z x)
    (hsRe : delta <= (s x).re)
    (hszRe : delta <= 6 * (s x).re + 6 * (z x).re - 4) :
    AnalyticAt Complex (fun y => localRemainder Q A eta (s y) (z y)) x := by
  have hQ0 : 0 < Q := by linarith
  have hpow (f : Complex -> Complex) (hf : AnalyticAt Complex f x) :
      AnalyticAt Complex (fun y => (Q : Complex) ^ (f y)) x := by
    have heq : (fun y => (Q : Complex) ^ (f y)) =
        (fun y => Complex.exp (f y * (Real.log Q : Complex))) := by
      funext y
      exact PrincipalEulerContinuation.positive_cpow_eq_exp Q hQ0 (f y)
    rw [heq]
    fun_prop
  have hD : AnalyticAt Complex (fun y => coordD Q eta 1 (s y)) x := by
    have h := hpow (fun y => -s y) (by fun_prop)
    simp only [coordD, star_one, mul_one]
    apply AnalyticAt.mul
    . fun_prop
    . exact h
  have hR : AnalyticAt Complex (fun y => coordR Q A (s y) (z y)) x := by
    have h := hpow (fun y => 4 - 6 * s y - 6 * z y) (by fun_prop)
    exact analyticAt_const.mul h
  have hden := coordinate_D_ne_one Q A eta (s x) (z x) delta
    hQ hA heta hd hsRe hszRe
  apply AnalyticAt.add analyticAt_const
  apply AnalyticAt.div
  . exact analyticAt_const.mul (hD.sub hR)
  . exact analyticAt_const.sub hD
  . exact hden

private theorem product_ne_zero_of_defect {I : Type*} (f : I -> Complex)
    (u : I -> Real) (c : Real) (hc : 0 < c) (hu : Summable u)
    (hbound : forall i, norm (f i - 1) <= u i)
    (hlower : forall i, c <= norm (f i)) :
    Not (tprod f = 0) := by
  have hzero (i : I) : Not (f i = 0) :=
    norm_pos_iff.mp (hc.trans_le (hlower i))
  have hf : Summable (fun i => norm (f i - 1)) :=
    hu.of_nonneg_of_le (fun _ => norm_nonneg _) hbound
  have hmf : Multipliable f := by
    simpa only [add_sub_cancel] using multipliable_one_add_of_summable hf
  have hi (i : I) : norm (Inv.inv (f i) - 1) <= (1 / c) * norm (f i - 1) := by
    have hn : norm (Inv.inv (f i)) <= 1 / c := by
      rw [norm_inv, inv_eq_one_div]
      exact div_le_div_of_nonneg_left (by norm_num) hc (hlower i)
    have he : Inv.inv (f i) - 1 = -(f i - 1) * Inv.inv (f i) := by
      field_simp [hzero i] <;> ring
    rw [he, norm_mul, norm_neg]
    simpa only [mul_comm] using
      mul_le_mul_of_nonneg_left hn (norm_nonneg (f i - 1))
  have hif : Summable (fun i => norm (Inv.inv (f i) - 1)) :=
    (hf.mul_left (1 / c)).of_nonneg_of_le (fun _ => norm_nonneg _) hi
  have hmif : Multipliable (fun i => Inv.inv (f i)) := by
    simpa only [add_sub_cancel] using multipliable_one_add_of_summable hif
  have hp := hmf.tprod_mul hmif
  have heq : (fun i => f i * Inv.inv (f i)) = (fun _ : I => (1 : Complex)) := by
    funext i
    field_simp [hzero i]
  rw [heq, tprod_one] at hp
  intro h
  rw [h, zero_mul] at hp
  exact one_ne_zero hp

theorem remainderProduct_ne_zero_wedge {I : Type*}
    (Q : I -> Real) (A eta : I -> Complex) (s z : Complex) (delta : Real)
    (hQ : forall i, 2 <= Q i) (hA : forall i, norm (A i) <= 1)
    (heta : forall i, norm (eta i) <= 1) (hd : 0 < delta)
    (hs : delta <= s.re) (hsz : delta <= 6 * s.re + 6 * z.re - 4)
    (hsum : Summable (fun i => Q i ^ (-(1 + delta)))) :
    Not (tprod (fun i => localRemainder (Q i) (A i) (eta i) s z) = 0) := by
  apply product_ne_zero_of_defect _
    (fun i => (2 / safetyMargin delta) * Q i ^ (-(1 + delta)))
    (safetyMargin delta / 2) (div_pos (margin_pos delta hd) (by norm_num))
    (hsum.mul_left _)
  . intro i
    exact local_remainder_defect_wedge _ _ _ _ _ delta (hQ i) (hA i) (heta i) hd hs hsz
  . intro i
    exact local_remainder_lower_wedge _ _ _ _ _ delta (hQ i) (hA i) (heta i) hd hs hsz

theorem analyticOnNhd_remainderProduct_wedge {I : Type*}
    (Q : I -> Real) (A eta : I -> Complex)
    (s z : Complex -> Complex) (U : Set Complex) (delta : Real)
    (hQ : forall i, 2 <= Q i) (hA : forall i, norm (A i) <= 1)
    (heta : forall i, norm (eta i) <= 1) (hd : 0 < delta)
    (hsum : Summable (fun i => Q i ^ (-(1 + delta))))
    (hU : IsOpen U) (hs : AnalyticOnNhd Complex s U)
    (hz : AnalyticOnNhd Complex z U)
    (hRe : forall x, Membership.mem U x ->
      delta <= (s x).re /\ delta <= 6 * (s x).re + 6 * (z x).re - 4) :
    AnalyticOnNhd Complex
      (fun x => tprod (fun i => localRemainder (Q i) (A i) (eta i) (s x) (z x))) U := by
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
    have hdy : dist y x <= r := Metric.mem_closedBall.mp hy
    dsimp [r] at hdy
    linarith
  let f : I -> Complex -> Complex :=
    fun i y => localRemainder (Q i) (A i) (eta i) (s y) (z y)
  have hana (i : I) (y : Complex) (hy : Membership.mem U y) :
      AnalyticAt Complex (f i) y :=
    local_remainder_analyticAt_wedge _ _ _ s z y delta (hQ i) (hA i) (heta i)
      hd (hs y hy) (hz y hy) (hRe y hy).1 (hRe y hy).2
  have hbound : forall i, forall y, Membership.mem K0 y ->
      norm (f i y - 1) <= (2 / safetyMargin delta) * Q i ^ (-(1 + delta)) := by
    intro i y hy
    have h := hRe y (hKU hy)
    exact local_remainder_defect_wedge _ _ _ _ _ delta
      (hQ i) (hA i) (heta i) hd h.1 h.2
  have hcts : forall i, ContinuousOn (fun y => f i y - 1) K0 := by
    intro i y hy
    exact ((hana i y (hKU hy)).continuousAt.sub continuousAt_const).continuousWithinAt
  have hp : HasProdUniformlyOn f (fun y => tprod (fun i => f i y)) K0 := by
    have h := Summable.hasProdUniformlyOn_one_add
      (f := fun i y => f i y - 1) (isCompact_closedBall x r)
      (hsum.mul_left (2 / safetyMargin delta)) (Filter.Eventually.of_forall hbound) hcts
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
        exact (hana i y hyU).differentiableAt.mul ih
    exact hprod.differentiableWithinAt
  have hdiff := hlim.differentiableOn (Filter.Eventually.of_forall hfin) Metric.isOpen_ball
  have hcenter : Membership.mem (Metric.ball x r) x := by simpa using hr
  exact ((hdiff x hcenter).differentiableAt
    (Metric.isOpen_ball.mem_nhds hcenter)).differentiableWithinAt


open FullEulerContinuation

private theorem high_source_norm_two {S : Finset SourcePrime} (P : HighSourcePrime S) :
    2 <= sourceNorm P.val := by
  dsimp [sourceNorm]
  exact_mod_cast OAI.SmoothMobiusCorrection.prime_norm_two_le P.val

private theorem source_summable_delta (S : Finset SourcePrime) (delta : Real)
    (hd : 0 < delta) :
    Summable (fun P : HighSourcePrime S => sourceNorm P.val ^ (-(1 + delta))) := by
  have hfull := OAI.CubicEisenstein.fullIdealWeight_summable_norm
    (((1 + delta : Real) : Complex)) (by simp only [Complex.ofReal_re]; linarith)
  have hprime : Summable (fun P : SourcePrime =>
      norm (OAI.CubicEisenstein.fullIdealWeight (((1 + delta : Real) : Complex)) P.val)) :=
    hfull.comp_injective Subtype.val_injective
  have hmajor : Summable (fun P : SourcePrime => sourceNorm P ^ (-(1 + delta))) := by
    apply hprime.congr
    intro P
    have hP := OAI.SmoothMobiusCorrection.prime_norm_pos P
    rw [OAI.CubicEisenstein.fullIdealWeight, ite_eq_right P.property.ne_zero,
      <- Complex.ofReal_natCast (Ideal.absNorm P.val),
      Complex.norm_cpow_eq_rpow_re_of_pos hP]
    simp only [Complex.neg_re, Complex.ofReal_re]
    rfl
  exact hmajor.comp_injective Subtype.val_injective

theorem source_remainderProduct_ne_zero_wedge
    (S : Finset SourcePrime) (eta : SourceCharacter) (s z : Complex)
    (hs : 0 < s.re) (hsz : (2 / 3 : Real) < s.re + z.re) :
    Not (sourceRemainderProduct S eta s z = 0) := by
  let delta : Real := min s.re (6 * s.re + 6 * z.re - 4)
  have hd : 0 < delta := by
    dsimp [delta]
    exact lt_min hs (by linarith)
  exact remainderProduct_ne_zero_wedge
    (fun P : HighSourcePrime S => sourceNorm P.val)
    (fun P => actualAPhase eta (OAI.CompletedGauss.primaryGenerator P.val.val))
    (fun P => HeckeFamily.idealCoeff eta P.val.val) s z delta
    high_source_norm_two
    (fun P => actualAPhase_norm_le_one eta
      (OAI.CompletedGauss.primaryGenerator P.val.val))
    (fun P => HeckeFamily.idealCoeff_norm_le_one eta P.val.val)
    hd (min_le_left _ _) (min_le_right _ _) (source_summable_delta S delta hd)

theorem analyticOnNhd_sourceRemainderProduct_wedge
    (S : Finset SourcePrime) (eta : SourceCharacter)
    (s z : Complex -> Complex) (U : Set Complex) (delta : Real)
    (hd : 0 < delta) (hU : IsOpen U)
    (hs : AnalyticOnNhd Complex s U) (hz : AnalyticOnNhd Complex z U)
    (hRe : forall x, Membership.mem U x ->
      delta <= (s x).re /\ delta <= 6 * (s x).re + 6 * (z x).re - 4) :
    AnalyticOnNhd Complex (fun x => sourceRemainderProduct S eta (s x) (z x)) U :=
  analyticOnNhd_remainderProduct_wedge
    (fun P : HighSourcePrime S => sourceNorm P.val)
    (fun P => actualAPhase eta (OAI.CompletedGauss.primaryGenerator P.val.val))
    (fun P => HeckeFamily.idealCoeff eta P.val.val) s z U delta
    high_source_norm_two
    (fun P => actualAPhase_norm_le_one eta
      (OAI.CompletedGauss.primaryGenerator P.val.val))
    (fun P => HeckeFamily.idealCoeff_norm_le_one eta P.val.val)
    hd (source_summable_delta S delta hd) hU hs hz hRe

theorem source_principal_remainder_analytic (S : Finset SourcePrime)
    (eta : SourceCharacter) :
    AnalyticOnNhd Complex (fun s => sourceRemainderProduct S eta s (1 / 6))
      {s : Complex | (1 / 2 : Real) < s.re} := by
  intro x hx
  change (1 / 2 : Real) < x.re at hx
  let delta : Real := min (x.re / 2) ((6 * x.re - 3) / 2)
  have hd : 0 < delta := by
    dsimp [delta]
    exact lt_min (by linarith) (by linarith)
  let sigma : Real := max delta ((delta + 3) / 6)
  have hsig : sigma < x.re := by
    have h1 : delta <= x.re / 2 := min_le_left _ _
    have h2 : delta <= (6 * x.re - 3) / 2 := min_le_right _ _
    exact max_lt_iff.mpr (And.intro (by linarith) (by linarith))
  have hr : forall y : Complex, Membership.mem {y : Complex | sigma < y.re} y ->
      delta <= y.re /\ delta <= 6 * y.re + 6 * (1 / 6 : Complex).re - 4 := by
    intro y hy
    change sigma < y.re at hy
    have h1 : delta <= sigma := le_max_left _ _
    have h2 : (delta + 3) / 6 <= sigma := le_max_right _ _
    norm_num
    exact And.intro (by linarith) (by linarith)
  exact analyticOnNhd_sourceRemainderProduct_wedge S eta
    (fun s => s) (fun _ => (1 / 6 : Complex))
    {s : Complex | sigma < s.re} delta hd
    (isOpen_lt continuous_const Complex.continuous_re)
    (by intro y hy; exact analyticAt_id)
    (by intro y hy; exact analyticAt_const) hr x hsig

theorem source_principal_remainder_ne_zero (S : Finset SourcePrime)
    (eta : SourceCharacter) (s : Complex) (hs : (1 / 2 : Real) < s.re) :
    Not (sourceRemainderProduct S eta s (1 / 6) = 0) := by
  apply source_remainderProduct_ne_zero_wedge S eta s (1 / 6) (by linarith)
  norm_num
  linarith

theorem principal_factor_ne_zero_critical (Q : Real) (eta a s : Complex)
    (hQ : 2 <= Q) (heta : norm eta <= 1) (ha : norm a <= 1)
    (hs : (1 / 2 : Real) < s.re) :
    Not (PrincipalEulerContinuation.principalFactor Q eta a s = 0) := by
  have hQ0 : 0 < Q := by linarith
  have hlog : 0 < Real.log Q := Real.log_pos (by linarith)
  have hD : norm (PrincipalEulerContinuation.localD Q eta s) < 1 := by
    apply (PrincipalEulerContinuation.localD_norm_le Q eta s heta).trans_lt
    calc
      Real.exp (-s.re * Real.log Q) < Real.exp 0 := by
        apply Real.exp_lt_exp.mpr
        nlinarith only [mul_pos (show 0 < s.re by linarith) hlog]
      _ = 1 := Real.exp_zero
  have hR : norm (PrincipalEulerContinuation.localR Q a s) < 1 := by
    apply (PrincipalEulerContinuation.localR_norm_le Q a s ha).trans_lt
    calc
      Real.exp ((3 - 6 * s.re) * Real.log Q) < Real.exp 0 := by
        apply Real.exp_lt_exp.mpr
        nlinarith only [mul_pos (show 0 < 6 * s.re - 3 by linarith) hlog]
      _ = 1 := Real.exp_zero
  have ht0 : 0 <= 1 / Q := by positivity
  have ht1 : 1 / Q < 1 := (div_lt_one hQ0).mpr (by linarith)
  have hn := convex_numerator_re_pos (1 / Q)
    (PrincipalEulerContinuation.localD Q eta s)
    (PrincipalEulerContinuation.localR Q a s) ht0 ht1.le hD hR
  have hnum : Not ((1 - PrincipalEulerContinuation.localD Q eta s) +
      (1 / (Q : Complex)) * (PrincipalEulerContinuation.localD Q eta s -
        PrincipalEulerContinuation.localR Q a s) = 0) := by
    intro h
    have he : 1 - ((1 - 1 / Q : Real) : Complex) *
        PrincipalEulerContinuation.localD Q eta s - ((1 / Q : Real) : Complex) *
          PrincipalEulerContinuation.localR Q a s = 0 := by
      simp only [Complex.ofReal_sub, Complex.ofReal_div, Complex.ofReal_one]
      linear_combination h
    rw [he, Complex.zero_re] at hn
    exact (lt_irrefl (0 : Real)) hn
  have htReal : Not ((1 : Real) - (1 / Q) ^ 2 = 0) := by
    intro he
    nlinarith only [ht0, ht1, he]
  have ht : Not ((1 : Complex) - (1 / (Q : Complex)) ^ 2 = 0) := by
    exact_mod_cast htReal
  have hden := PrincipalEulerContinuation.moving_denominators Q eta a s hQ heta ha hs
  exact div_ne_zero (mul_ne_zero ht hnum) (mul_ne_zero hden.2 hden.1)

theorem source_principal_factor_ne_zero_critical
    (eta : PrincipalEulerContinuation.SourceCharacter)
    (P : PrincipalEulerContinuation.SourcePrime) (s : Complex)
    (hs : (1 / 2 : Real) < s.re) :
    Not (ProbePhysical.idealClosedCorrection eta P s 1 (1 / 6) = 0) := by
  rw [PrincipalEulerContinuation.idealClosedCorrection_principal_eq eta P s hs]
  have hQ : 2 <= PrincipalEulerContinuation.sourceNorm P := by
    dsimp [PrincipalEulerContinuation.sourceNorm]
    exact_mod_cast OAI.SmoothMobiusCorrection.prime_norm_two_le P
  exact principal_factor_ne_zero_critical _ _ _ _ hQ
    (PrincipalEulerContinuation.source_eta_norm_le eta P)
    (PrincipalEulerContinuation.source_root_norm_le eta P) hs

end PrimeFactorOscillations.CarmichaelEulerCriticalWedge

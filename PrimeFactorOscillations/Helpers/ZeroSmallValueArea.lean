/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Analysis.Analytic.Order
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Small-value area and simple complex zeros

The geometric threshold uses planar Lebesgue measure. A local linear
lower bound gives quadratic sublevel area. A quadratic upper bound forces
sublevel area of at least first order and rules out area o(epsilon).
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

open MeasureTheory
open scoped Topology

def sublevelArea (f : Complex -> Complex) (w : Complex) (R eps : Real) : Real :=
  (volume {z : Complex | And (Membership.mem (Metric.ball w R) z) (norm (f z) <= eps)}).toReal

def SublevelAreaVanishingAt (f : Complex -> Complex) (w : Complex) : Prop :=
  exists R : Real, And (0 < R) (forall c : Real, 0 < c ->
    exists delta : Real, And (0 < delta) (forall eps : Real, 0 < eps -> eps < delta ->
      sublevelArea f w R eps <= c * eps))

theorem complex_ball_area (w : Complex) (r : Real) (hr : 0 <= r) :
    (volume (Metric.ball w r)).toReal = Real.pi * r ^ 2 := by
  simp [Complex.volume_ball, ENNReal.toReal_mul, ENNReal.toReal_pow,
    ENNReal.toReal_ofReal hr, mul_comm]

theorem complex_closedBall_area (w : Complex) (r : Real) (hr : 0 <= r) :
    (volume (Metric.closedBall w r)).toReal = Real.pi * r ^ 2 := by
  simp [Complex.volume_closedBall, ENNReal.toReal_mul, ENNReal.toReal_pow,
    ENNReal.toReal_ofReal hr, mul_comm]

theorem sublevelArea_measure_ne_top (f : Complex -> Complex) (w : Complex) (R eps : Real) :
    Not (volume {z : Complex | And (Membership.mem (Metric.ball w R) z)
      (norm (f z) <= eps)} = Top.top) := by
  have hb : Not (volume (Metric.ball w R) = Top.top) := by
    rw [Complex.volume_ball, pow_two]
    exact ENNReal.mul_ne_top (ENNReal.mul_ne_top (by simp) (by simp)) (by simp)
  have hm : volume {z : Complex | And (Membership.mem (Metric.ball w R) z)
      (norm (f z) <= eps)} <= volume (Metric.ball w R) :=
    measure_mono (fun _ hz => hz.1)
  intro ht
  rw [ht] at hm
  exact hb (le_antisymm le_top hm)

theorem sublevelArea_le_of_linear_lower (f : Complex -> Complex) (w : Complex)
    (R c eps : Real) (hc : 0 < c) (heps : 0 <= eps)
    (hlin : forall z : Complex, Membership.mem (Metric.ball w R) z ->
      c * norm (z - w) <= norm (f z)) :
    sublevelArea f w R eps <= Real.pi * (eps / c) ^ 2 := by
  have hsub : {z : Complex | And (Membership.mem (Metric.ball w R) z) (norm (f z) <= eps)} <=
      Metric.closedBall w (eps / c) := by
    intro z hz
    apply Metric.mem_closedBall.mpr
    have hh := div_le_div_of_nonneg_right ((hlin z hz.1).trans hz.2) hc.le
    have he : c * norm (z - w) / c = norm (z - w) := by field_simp [hc.ne']
    rw [he] at hh
    simpa only [dist_eq_norm] using hh
  have hm : volume {z : Complex | And (Membership.mem (Metric.ball w R) z) (norm (f z) <= eps)} <=
      volume (Metric.closedBall w (eps / c)) := measure_mono hsub
  have hf : Not (volume (Metric.closedBall w (eps / c)) = Top.top) := by
    rw [Complex.volume_closedBall, pow_two]
    exact ENNReal.mul_ne_top (ENNReal.mul_ne_top (by simp) (by simp)) (by simp)
  have hh := ENNReal.toReal_mono hf hm
  rw [complex_closedBall_area w (eps / c) (div_nonneg heps hc.le)] at hh
  exact hh

theorem sublevelAreaVanishingAt_of_linear_lower (f : Complex -> Complex) (w : Complex)
    (R c : Real) (hR : 0 < R) (hc : 0 < c)
    (hlin : forall z : Complex, Membership.mem (Metric.ball w R) z ->
      c * norm (z - w) <= norm (f z)) : SublevelAreaVanishingAt f w := by
  refine Exists.intro R (And.intro hR ?_)
  intro c0 hc0
  let delta : Real := c0 * c ^ 2 / Real.pi
  have hd : 0 < delta := div_pos (mul_pos hc0 (sq_pos_of_pos hc)) Real.pi_pos
  refine Exists.intro delta (And.intro hd ?_)
  intro eps heps hepsd
  have harea := sublevelArea_le_of_linear_lower f w R c eps hc heps.le hlin
  have hh := mul_le_mul_of_nonneg_right hepsd.le Real.pi_pos.le
  have hcancel : delta * Real.pi = c0 * c ^ 2 := by
    dsimp only [delta]
    field_simp [Real.pi_ne_zero]
  rw [hcancel] at hh
  have hmul := mul_le_mul_of_nonneg_right hh heps.le
  have hdiv := div_le_div_of_nonneg_right hmul (sq_nonneg c)
  have hleft : (eps * Real.pi * eps) / c ^ 2 = Real.pi * (eps / c) ^ 2 := by
    field_simp [hc.ne'] <;> ring
  have hright : (c0 * c ^ 2 * eps) / c ^ 2 = c0 * eps := by field_simp [hc.ne']
  rw [hleft, hright] at hdiv
  exact harea.trans hdiv

theorem not_sublevelAreaVanishingAt_of_quadratic_upper (f : Complex -> Complex) (w : Complex)
    (rho C : Real) (hrho : 0 < rho) (hC : 0 < C)
    (hquad : forall z : Complex, Membership.mem (Metric.ball w rho) z ->
      norm (f z) <= C * norm (z - w) ^ 2) : Not (SublevelAreaVanishingAt f w) := by
  intro hvan
  let R : Real := Classical.choose hvan
  have hR := Classical.choose_spec hvan
  let c0 : Real := Real.pi / (2 * C)
  have hc0 : 0 < c0 := div_pos Real.pi_pos (mul_pos (by norm_num) hC)
  have hdelta := hR.2 c0 hc0
  let delta : Real := Classical.choose hdelta
  have hd := Classical.choose_spec hdelta
  let a : Real := min R rho
  have ha : 0 < a := lt_min hR.1 hrho
  let eps : Real := min (delta / 2) (C * a ^ 2 / 4)
  have heps : 0 < eps := lt_min (div_pos hd.1 (by norm_num))
    (div_pos (mul_pos hC (sq_pos_of_pos ha)) (by norm_num))
  have hepsd : eps < delta := (min_le_left _ _).trans_lt (by linarith only [hd.1])
  have hepsa : eps <= C * a ^ 2 / 4 := min_le_right _ _
  let r : Real := Real.sqrt (eps / C)
  have hr : 0 < r := Real.sqrt_pos.mpr (div_pos heps hC)
  have hrsq : r ^ 2 = eps / C := Real.sq_sqrt (div_nonneg heps.le hC.le)
  have hdiv : eps / C <= a ^ 2 / 4 := by
    have hh := div_le_div_of_nonneg_right hepsa hC.le
    convert hh using 1 <;> field_simp [hC.ne'] <;> ring
  have hra : r < a := by nlinarith only [hrsq, hdiv, ha, hr]
  have hrR : r < R := hra.trans_le (min_le_left _ _)
  have hrrho : r < rho := hra.trans_le (min_le_right _ _)
  have he : C * r ^ 2 = eps := by rw [hrsq]; field_simp [hC.ne']
  have hsub : Metric.ball w r <=
      {z : Complex | And (Membership.mem (Metric.ball w R) z) (norm (f z) <= eps)} := by
    intro z hz
    have hdist : norm (z - w) < r := by simpa only [Metric.mem_ball, dist_eq_norm] using hz
    have hzrho : Membership.mem (Metric.ball w rho) z :=
      Metric.mem_ball.mpr (by simpa only [dist_eq_norm] using hdist.trans hrrho)
    have hzR : Membership.mem (Metric.ball w R) z :=
      Metric.mem_ball.mpr (by simpa only [dist_eq_norm] using hdist.trans hrR)
    have hs : norm (z - w) ^ 2 <= r ^ 2 := by nlinarith only [hdist, norm_nonneg (z - w), hr]
    have hbound := (hquad z hzrho).trans (mul_le_mul_of_nonneg_left hs hC.le)
    rw [he] at hbound
    exact And.intro hzR hbound
  have hmeasure := ENNReal.toReal_mono (sublevelArea_measure_ne_top f w R eps) (measure_mono hsub)
  rw [complex_ball_area w r hr.le] at hmeasure
  change Real.pi * r ^ 2 <= sublevelArea f w R eps at hmeasure
  have hsmall := hd.2 eps heps hepsd
  have hcancel : c0 * eps = (Real.pi / 2) * r ^ 2 := by
    dsimp only [c0]
    rw [<- he]
    field_simp [hC.ne'] <;> ring
  rw [hcancel] at hsmall
  have hpos : 0 < Real.pi * r ^ 2 := mul_pos Real.pi_pos (sq_pos_of_pos hr)
  linarith only [hmeasure, hsmall, hpos]

theorem real_self_le_pow_of_nat_le_one (r : Real) (m : Nat)
    (hr : r <= 1) (hm : m <= 1) : r <= r ^ m := by
  cases m with
  | zero => simpa only [pow_zero] using hr
  | succ n =>
    have hn : n = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_succ_le_succ hm)
    subst n
    simp

theorem real_pow_le_sq_of_nat_ge_two (r : Real) (m : Nat)
    (hr0 : 0 <= r) (hr1 : r <= 1) (hm : 2 <= m) : r ^ m <= r ^ 2 := by
  have hp : forall k : Nat, r ^ k <= 1 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ]
      exact (mul_le_mul_of_nonneg_right ih hr0).trans (by simpa using hr1)
  have he : m = (m - 2) + 2 := (Nat.sub_add_cancel hm).symm
  rw [he, pow_add]
  exact (mul_le_mul_of_nonneg_right (hp (m - 2)) (sq_nonneg r)).trans (by simp)

theorem analytic_linear_lower_of_order_le_one (f : Complex -> Complex) (w : Complex)
    (hf : AnalyticAt Complex f w) (hfinite : Not (analyticOrderAt f w = Top.top))
    (hm : analyticOrderNatAt f w <= 1) :
    exists R : Real, exists c : Real, And (0 < R) (And (0 < c)
      (forall z : Complex, Membership.mem (Metric.ball w R) z ->
        c * norm (z - w) <= norm (f z))) := by
  have hfac := (hf.analyticOrderNatAt_eq_iff hfinite
    (n := analyticOrderNatAt f w)).mp rfl
  let g : Complex -> Complex := Classical.choose hfac
  have hg := Classical.choose_spec hfac
  let c : Real := norm (g w) / 2
  have hgw : 0 < norm (g w) := norm_pos_iff.mpr hg.2.1
  have hc : 0 < c := div_pos hgw (by norm_num)
  have hcw : c < norm (g w) := by dsimp only [c]; linarith only [hgw]
  have hcont : Filter.Tendsto (fun z => norm (g z)) (nhds w) (nhds (norm (g w))) :=
    hg.1.continuousAt.norm
  have hbound := hcont.eventually (eventually_gt_nhds hcw)
  have hevent := hg.2.2.and hbound
  have hball := Metric.eventually_nhds_iff_ball.mp hevent
  let delta : Real := Classical.choose hball
  have hd := Classical.choose_spec hball
  let R : Real := min delta 1
  have hR : 0 < R := lt_min hd.1 (by norm_num)
  refine Exists.intro R (Exists.intro c (And.intro hR (And.intro hc ?_)))
  intro z hz
  have hzdist : norm (z - w) < R := by
    simpa only [Metric.mem_ball, dist_eq_norm] using hz
  have hzdelta : Membership.mem (Metric.ball w delta) z :=
    Metric.mem_ball.mpr (by simpa only [dist_eq_norm] using hzdist.trans_le (min_le_left _ _))
  have hh := hd.2 z hzdelta
  have heq : norm (f z) = norm (z - w) ^ analyticOrderNatAt f w * norm (g z) := by
    rw [hh.1, smul_eq_mul, norm_mul, norm_pow]
  rw [heq]
  have hp := real_self_le_pow_of_nat_le_one (norm (z - w))
    (analyticOrderNatAt f w) (hzdist.le.trans (min_le_right _ _)) hm
  calc
    c * norm (z - w) <= c * norm (z - w) ^ analyticOrderNatAt f w :=
      mul_le_mul_of_nonneg_left hp hc.le
    _ <= norm (g z) * norm (z - w) ^ analyticOrderNatAt f w :=
      mul_le_mul_of_nonneg_right hh.2.le (pow_nonneg (norm_nonneg _) _)
    _ = _ := mul_comm _ _

theorem analytic_quadratic_upper_of_order_ge_two (f : Complex -> Complex) (w : Complex)
    (hf : AnalyticAt Complex f w) (hfinite : Not (analyticOrderAt f w = Top.top))
    (hm : 2 <= analyticOrderNatAt f w) :
    exists R : Real, exists C : Real, And (0 < R) (And (0 < C)
      (forall z : Complex, Membership.mem (Metric.ball w R) z ->
        norm (f z) <= C * norm (z - w) ^ 2)) := by
  have hfac := (hf.analyticOrderNatAt_eq_iff hfinite
    (n := analyticOrderNatAt f w)).mp rfl
  let g : Complex -> Complex := Classical.choose hfac
  have hg := Classical.choose_spec hfac
  let C : Real := norm (g w) + 1
  have hC : 0 < C := by dsimp only [C]; positivity
  have hcw : norm (g w) < C := by dsimp only [C]; linarith
  have hcont : Filter.Tendsto (fun z => norm (g z)) (nhds w) (nhds (norm (g w))) :=
    hg.1.continuousAt.norm
  have hbound := hcont.eventually (eventually_lt_nhds hcw)
  have hevent := hg.2.2.and hbound
  have hball := Metric.eventually_nhds_iff_ball.mp hevent
  let delta : Real := Classical.choose hball
  have hd := Classical.choose_spec hball
  let R : Real := min delta 1
  have hR : 0 < R := lt_min hd.1 (by norm_num)
  refine Exists.intro R (Exists.intro C (And.intro hR (And.intro hC ?_)))
  intro z hz
  have hzdist : norm (z - w) < R := by
    simpa only [Metric.mem_ball, dist_eq_norm] using hz
  have hzdelta : Membership.mem (Metric.ball w delta) z :=
    Metric.mem_ball.mpr (by simpa only [dist_eq_norm] using hzdist.trans_le (min_le_left _ _))
  have hh := hd.2 z hzdelta
  have heq : norm (f z) = norm (z - w) ^ analyticOrderNatAt f w * norm (g z) := by
    rw [hh.1, smul_eq_mul, norm_mul, norm_pow]
  rw [heq]
  have hp := real_pow_le_sq_of_nat_ge_two (norm (z - w)) (analyticOrderNatAt f w)
    (norm_nonneg _) (hzdist.le.trans (min_le_right _ _)) hm
  calc
    norm (z - w) ^ analyticOrderNatAt f w * norm (g z) <=
        norm (z - w) ^ analyticOrderNatAt f w * C :=
      mul_le_mul_of_nonneg_left hh.2.le (pow_nonneg (norm_nonneg _) _)
    _ <= norm (z - w) ^ 2 * C := mul_le_mul_of_nonneg_right hp hC.le
    _ = _ := mul_comm _ _

theorem analyticOrderNatAt_le_one_iff_sublevelAreaVanishingAt (f : Complex -> Complex)
    (w : Complex) (hf : AnalyticAt Complex f w)
    (hfinite : Not (analyticOrderAt f w = Top.top)) :
    analyticOrderNatAt f w <= 1 <-> SublevelAreaVanishingAt f w := by
  constructor
  case mp =>
    intro hm
    have hlin := analytic_linear_lower_of_order_le_one f w hf hfinite hm
    let R := Classical.choose hlin
    have hR := Classical.choose_spec hlin
    let c := Classical.choose hR
    have hc := Classical.choose_spec hR
    exact sublevelAreaVanishingAt_of_linear_lower f w R c hc.1 hc.2.1 hc.2.2
  case mpr =>
    intro hvan
    by_contra hm
    have hm2 : 2 <= analyticOrderNatAt f w := Nat.succ_le_of_lt (lt_of_not_ge hm)
    have hquad := analytic_quadratic_upper_of_order_ge_two f w hf hfinite hm2
    let R := Classical.choose hquad
    have hR := Classical.choose_spec hquad
    let C := Classical.choose hR
    have hc := Classical.choose_spec hR
    exact not_sublevelAreaVanishingAt_of_quadratic_upper f w R C hc.1 hc.2.1 hc.2.2 hvan

end PrimeFactorOscillations

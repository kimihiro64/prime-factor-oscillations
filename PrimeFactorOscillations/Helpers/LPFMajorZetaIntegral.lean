/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.MellinTransform
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.LSeries.SumCoeff
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# A numerical bound for pole-filled zeta

The fractional-part Mellin integral identifies the actual pole-filled Riemann
zeta function throughout the positive half-plane. Its norm is at most 4*T^2
when the real part is at least seven eighths and both s and s-1 have norm at
most T. This supplies the principal-character growth input; contour and
prime-prefix estimates are separate consumers.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.QRH

noncomputable def lpfFractionalTail (t : Real) : Complex :=
  (Set.Ioi (1 : Real)).indicator (fun u : Real => Complex.ofReal (Int.fract u)) t

theorem lpf_fractional_tail_norm (t : Real) : norm (lpfFractionalTail t) <= 1 := by
  by_cases ht : 1 < t
  next =>
    have hm : Membership.mem (Set.Ioi (1 : Real)) t := ht
    rw [lpfFractionalTail, Set.indicator_of_mem hm, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (Int.fract_nonneg t)]
    exact (Int.fract_lt_one t).le
  next =>
    have hm : Not (Membership.mem (Set.Ioi (1 : Real)) t) := ht
    rw [lpfFractionalTail, Set.indicator_of_notMem hm, norm_zero]
    norm_num

theorem lpf_fractional_tail_locallyIntegrable :
    MeasureTheory.LocallyIntegrable lpfFractionalTail MeasureTheory.volume := by
  have hm0 : Measurable (fun t : Real => Complex.ofReal (Int.fract t)) :=
    Complex.continuous_ofReal.measurable.comp measurable_fract
  have hm : Measurable lpfFractionalTail := hm0.indicator measurableSet_Ioi
  have hOne : MeasureTheory.LocallyIntegrable (fun _ : Real => (1 : Real))
      MeasureTheory.volume := MeasureTheory.locallyIntegrable_const 1
  apply hOne.mono hm.aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun t => by simpa using lpf_fractional_tail_norm t)

theorem lpf_fractional_tail_bigO_top :
    Asymptotics.IsBigO Filter.atTop lpfFractionalTail
      (fun t : Real => t ^ (-(0 : Real))) := by
  apply Asymptotics.IsBigO.of_bound 1
  exact Filter.Eventually.of_forall (fun t => by simpa using lpf_fractional_tail_norm t)

theorem lpf_fractional_tail_bigO_zero (b : Real) :
    Asymptotics.IsBigO (nhdsWithin (0 : Real) (Set.Ioi 0)) lpfFractionalTail
      (fun t : Real => t ^ (-b)) := by
  apply Asymptotics.IsBigO.of_bound 0
  have hlt : Filter.Eventually (fun t : Real => t < 1)
      (nhdsWithin (0 : Real) (Set.Ioi 0)) :=
    (eventually_lt_nhds (by norm_num : (0 : Real) < 1)).filter_mono
      nhdsWithin_le_nhds
  filter_upwards [hlt] with t ht
  have hn : Not (1 < t) := by linarith
  have hz : lpfFractionalTail t = 0 := by simp [lpfFractionalTail, hn]
  simp [hz]

noncomputable def lpfFractionalMellin (s : Complex) : Complex :=
  mellin lpfFractionalTail (-s)

theorem lpf_fractional_mellin_differentiableAt (s : Complex) (hs : 0 < s.re) :
    DifferentiableAt Complex lpfFractionalMellin s := by
  have hm := mellin_differentiableAt_of_isBigO_rpow
    (a := (0 : Real)) (b := -s.re - 1) (s := -s)
    (lpf_fractional_tail_locallyIntegrable.locallyIntegrableOn (Set.Ioi 0))
    lpf_fractional_tail_bigO_top (by simp only [Complex.neg_re]; linarith)
    (lpf_fractional_tail_bigO_zero (-s.re - 1)) (by simp only [Complex.neg_re]; linarith)
  exact hm.comp s (hasDerivAt_id s).neg.differentiableAt

theorem lpf_fractional_mellin_analyticOnNhd :
    AnalyticOnNhd Complex lpfFractionalMellin {s : Complex | 0 < s.re} := by
  have ho : IsOpen {s : Complex | 0 < s.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  apply DifferentiableOn.analyticOnNhd ?_ ho
  intro s hs
  exact (lpf_fractional_mellin_differentiableAt s hs).differentiableWithinAt


theorem lpf_fractional_mellin_eq_integral (s : Complex) :
    lpfFractionalMellin s =
      MeasureTheory.integral (MeasureTheory.volume.restrict (Set.Ioi (1 : Real)))
        (fun t : Real => (t : Complex) ^ (-(s + 1)) * Complex.ofReal (Int.fract t)) := by
  have he : -s - 1 = -(s + 1) := by ring
  have hf : (fun t : Real => (t : Complex) ^ (-s - 1) * lpfFractionalTail t) =
      (Set.Ioi (1 : Real)).indicator (fun t : Real =>
        (t : Complex) ^ (-(s + 1)) * Complex.ofReal (Int.fract t)) := by
    funext t
    by_cases ht : Membership.mem (Set.Ioi (1 : Real)) t
    next => simp only [lpfFractionalTail, Set.indicator_of_mem ht, he]
    next => simp only [lpfFractionalTail, Set.indicator_of_notMem ht, mul_zero]
  have hi : Inter.inter (Set.Ioi (0 : Real)) (Set.Ioi (1 : Real)) = Set.Ioi 1 := by
    ext t
    simp only [Set.mem_inter_iff, Set.mem_Ioi]
    constructor
    next => exact fun h => h.2
    next => intro h; exact And.intro (by linarith) h
  unfold lpfFractionalMellin mellin
  simp only [smul_eq_mul]
  rw [hf, MeasureTheory.setIntegral_indicator measurableSet_Ioi, hi]

theorem lpf_fractional_mellin_norm_bound (s : Complex) (hs : 0 < s.re) :
    norm (lpfFractionalMellin s) <= 1 / s.re := by
  have hg : MeasureTheory.IntegrableOn
      (fun t : Real => t ^ (-(s.re + 1))) (Set.Ioi (1 : Real))
      MeasureTheory.volume :=
    integrableOn_Ioi_rpow_of_lt (by linarith) (by norm_num : (0 : Real) < 1)
  have hb : norm (lpfFractionalMellin s) <=
      MeasureTheory.integral (MeasureTheory.volume.restrict (Set.Ioi (1 : Real)))
        (fun t : Real => t ^ (-(s.re + 1))) := by
    rw [lpf_fractional_mellin_eq_integral]
    apply MeasureTheory.norm_integral_le_of_norm_le hg
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
    have ht1 : 1 < t := Set.mem_Ioi.mp ht
    have ht0 : 0 < t := by linarith
    have ha : norm (Complex.ofReal (Int.fract t)) <= 1 := by
      simpa only [lpfFractionalTail, Set.indicator_of_mem ht] using lpf_fractional_tail_norm t
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht0]
    simp only [Complex.neg_re, Complex.add_re, Complex.one_re]
    simpa using mul_le_mul_of_nonneg_left ha (Real.rpow_nonneg ht0.le (-(s.re + 1)))
  have hi := integral_Ioi_rpow_of_lt (a := -(s.re + 1))
    (by linarith) (by norm_num : (0 : Real) < 1)
  have he : -(s.re + 1) + 1 = -s.re := by ring
  rw [he, Real.one_rpow, neg_div_neg_eq] at hi
  rwa [hi] at hb


noncomputable def lpfPoleFilledZeta (s : Complex) : Complex :=
  s - s * (s - 1) * lpfFractionalMellin s

theorem lpf_poleFilledZeta_one : lpfPoleFilledZeta 1 = 1 := by
  simp [lpfPoleFilledZeta]

theorem lpf_poleFilledZeta_analyticOnNhd :
    AnalyticOnNhd Complex lpfPoleFilledZeta {s : Complex | 0 < s.re} := by
  exact analyticOnNhd_id.sub
    ((analyticOnNhd_id.mul (analyticOnNhd_id.sub analyticOnNhd_const)).mul
      lpf_fractional_mellin_analyticOnNhd)

theorem lpf_poleFilledZeta_norm_bound (s : Complex) (T : Real)
    (hs : 7 / 8 <= s.re) (hT : 1 <= T)
    (hsNorm : norm s <= T) (hsOne : norm (s - 1) <= T) :
    norm (lpfPoleFilledZeta s) <= 4 * T ^ 2 := by
  have hs0 : 0 < s.re := by linarith
  have hI := lpf_fractional_mellin_norm_bound s hs0
  have hInv : 1 / s.re <= (8 / 7 : Real) := by
    calc
      _ <= 1 / (7 / 8 : Real) := div_le_div_of_nonneg_left
        (by norm_num : (0 : Real) <= 1) (by norm_num : (0 : Real) < 7 / 8) hs
      _ = _ := by norm_num
  have hI0 : 0 <= norm (lpfFractionalMellin s) := norm_nonneg _
  have hT0 : 0 <= T := by linarith
  have h1 := norm_sub_le s (s * (s - 1) * lpfFractionalMellin s)
  rw [norm_mul, norm_mul] at h1
  have hProd : norm s * norm (s - 1) <= T ^ 2 := by
    simpa only [pow_two] using mul_le_mul hsNorm hsOne (norm_nonneg _) hT0
  have hTerm := mul_le_mul hProd (hI.trans hInv) hI0 (sq_nonneg T)
  dsimp [lpfPoleFilledZeta]
  have hSq : T <= T ^ 2 := by nlinarith [sq_nonneg (T - 1)]
  nlinarith only [h1, hTerm, hsNorm, hSq]


noncomputable def lpfZetaPoleFill (s : Complex) : Complex := by
  classical
  exact if s = 1 then 1 else (s - 1) * riemannZeta s

theorem lpf_zetaPoleFill_one : lpfZetaPoleFill 1 = 1 := by
  simp [lpfZetaPoleFill]

theorem lpf_zetaPoleFill_differentiableAt_of_ne_one (s : Complex) (hs : Not (s = 1)) :
    DifferentiableAt Complex lpfZetaPoleFill s := by
  have hd : DifferentiableAt Complex (fun w => (w - 1) * riemannZeta w) s :=
    (differentiableAt_id.sub_const 1).mul (differentiableAt_riemannZeta hs)
  apply hd.congr_of_eventuallyEq
  filter_upwards [eventually_ne_nhds hs] with w hw
  simp [lpfZetaPoleFill, hw]

theorem lpf_zetaPoleFill_continuousAt_one :
    ContinuousAt lpfZetaPoleFill 1 := by
  have hSingle : ContinuousWithinAt lpfZetaPoleFill ({1} : Set Complex) 1 :=
    (continuousOn_singleton lpfZetaPoleFill 1) 1 (by simp)
  have hPunct : ContinuousWithinAt lpfZetaPoleFill (Set.compl ({1} : Set Complex)) 1 := by
    change Filter.Tendsto lpfZetaPoleFill _ (nhds (lpfZetaPoleFill 1))
    rw [lpf_zetaPoleFill_one]
    apply riemannZeta_residue_one.congr'
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hn : Not (s = 1) := by
      simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hs
    simp [lpfZetaPoleFill, hn]
  have hAll := hSingle.union hPunct
  have hu : Union.union ({1} : Set Complex) (Set.compl ({1} : Set Complex)) = Set.univ := by
    ext z
    simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_univ]
    exact iff_true_intro (Classical.em (z = 1))
  rw [hu] at hAll
  simpa only [continuousWithinAt_univ] using hAll

theorem lpf_zetaPoleFill_analyticAt_one :
    AnalyticAt Complex lpfZetaPoleFill 1 := by
  apply Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt
    ?_ lpf_zetaPoleFill_continuousAt_one
  filter_upwards [self_mem_nhdsWithin] with s hs
  apply lpf_zetaPoleFill_differentiableAt_of_ne_one
  simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hs

theorem lpf_zetaPoleFill_differentiable : Differentiable Complex lpfZetaPoleFill := by
  intro s
  by_cases hs : s = 1
  next =>
    subst s
    exact lpf_zetaPoleFill_analyticAt_one.differentiableAt
  next => exact lpf_zetaPoleFill_differentiableAt_of_ne_one s hs


private theorem fractional_nat_floor (t : Real) (ht : 1 < t) :
    (Nat.floor t : Complex) = (t : Complex) - Complex.ofReal (Int.fract t) := by
  have hi : Int.floor t = (Nat.floor t : Int) := by
    apply Int.floor_eq_iff.mpr
    constructor
    next => simpa using (Nat.floor_le (by linarith : (0 : Real) <= t))
    next => simpa using (Nat.lt_floor_add_one t)
  have hr : (Nat.floor t : Real) = t - Int.fract t := by
    unfold Int.fract
    rw [hi]
    simp
  exact_mod_cast hr

private theorem fractional_integrable_kernel (s : Complex) (hs : 0 < s.re) :
    MeasureTheory.IntegrableOn (fun t : Real =>
      (t : Complex) ^ (-(s + 1)) * Complex.ofReal (Int.fract t))
      (Set.Ioi (1 : Real)) MeasureTheory.volume := by
  have hc : MellinConvergent lpfFractionalTail (-s) :=
    mellinConvergent_of_isBigO_rpow
      (a := (0 : Real)) (b := -s.re - 1)
      (lpf_fractional_tail_locallyIntegrable.locallyIntegrableOn (Set.Ioi 0))
      lpf_fractional_tail_bigO_top (by simp only [Complex.neg_re]; linarith)
      (lpf_fractional_tail_bigO_zero (-s.re - 1)) (by simp only [Complex.neg_re]; linarith)
  have hc0 : MeasureTheory.IntegrableOn (fun t : Real =>
      (t : Complex) ^ (-s - 1) * lpfFractionalTail t)
      (Set.Ioi (0 : Real)) MeasureTheory.volume := by
    simpa only [MellinConvergent, smul_eq_mul] using hc
  have hSub : Set.Ioi (1 : Real) <= Set.Ioi (0 : Real) := by
    intro t ht
    have h := Set.mem_Ioi.mp ht
    change 0 < t
    linarith
  apply (hc0.mono_set hSub).congr_fun ?_ measurableSet_Ioi
  intro t ht
  simp only [lpfFractionalTail, Set.indicator_of_mem ht]
  congr 1
  ring

private theorem zeta_LSeries_one (s : Complex) (hs : 1 < s.re) :
    riemannZeta s = LSeries (fun _ : Nat => (1 : Complex)) s := by
  have hn : Not (s = 0) := by intro h; subst s; norm_num at hs
  rw [zeta_eq_tsum_one_div_nat_cpow hs]
  unfold LSeries
  apply tsum_congr
  intro n
  by_cases hn0 : n = 0
  next => subst n; simp [LSeries.term, Complex.zero_cpow hn]
  next => rw [LSeries.term_of_ne_zero hn0]

theorem lpf_poleFilledZeta_eq_of_one_lt_re (s : Complex) (hs : 1 < s.re) :
    lpfPoleFilledZeta s = (s - 1) * riemannZeta s := by
  have hCoeff : Asymptotics.IsBigO Filter.atTop
      (fun n : Nat => Finset.sum (Finset.Icc 1 n) (fun _ => norm (1 : Complex)))
      (fun n : Nat => (n : Real) ^ (1 : Real)) := by
    apply Asymptotics.IsBigO.of_bound 1
    exact Filter.Eventually.of_forall (fun n => by simp)
  have hAbel := LSeries_eq_mul_integral' (fun _ : Nat => (1 : Complex))
    (r := (1 : Real)) (by norm_num) hs hCoeff
  have hz : riemannZeta s = s * MeasureTheory.integral
      (MeasureTheory.volume.restrict (Set.Ioi (1 : Real)))
      (fun t : Real => (Nat.floor t : Complex) * (t : Complex) ^ (-(s + 1))) := by
    rw [zeta_LSeries_one s hs]
    simpa using hAbel
  have hJ : MeasureTheory.IntegrableOn (fun t : Real => (t : Complex) ^ (-s))
      (Set.Ioi (1 : Real)) MeasureTheory.volume :=
    integrableOn_Ioi_cpow_of_lt (by simp only [Complex.neg_re]; linarith)
      (by norm_num : (0 : Real) < 1)
  have hI := fractional_integrable_kernel s (by linarith)
  have hDecomp : MeasureTheory.integral
      (MeasureTheory.volume.restrict (Set.Ioi (1 : Real)))
      (fun t : Real => (Nat.floor t : Complex) * (t : Complex) ^ (-(s + 1))) =
      MeasureTheory.integral (MeasureTheory.volume.restrict (Set.Ioi (1 : Real)))
        (fun t : Real => (t : Complex) ^ (-s)) - lpfFractionalMellin s := by
    rw [lpf_fractional_mellin_eq_integral]
    rw [<- MeasureTheory.integral_sub hJ hI]
    apply MeasureTheory.integral_congr_ae
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
    have ht1 : 1 < t := Set.mem_Ioi.mp ht
    have ht0 : Not ((t : Complex) = 0) := by
      exact_mod_cast (show Not (t = 0) by linarith)
    rw [fractional_nat_floor t ht1, sub_mul]
    congr 1
    calc
      (t : Complex) * (t : Complex) ^ (-(s + 1)) =
          Complex.exp (Complex.log (t : Complex)) *
            Complex.exp (Complex.log (t : Complex) * (-(s + 1))) := by
              rw [Complex.exp_log ht0, Complex.cpow_def_of_ne_zero ht0]
      _ = Complex.exp (Complex.log (t : Complex) * (-s)) := by
        rw [<- Complex.exp_add]
        congr 1
        ring
      _ = _ := (Complex.cpow_def_of_ne_zero ht0 (-s)).symm
    ring
  have hJval := integral_Ioi_cpow_of_lt (a := -s)
    (by simp only [Complex.neg_re]; linarith) (by norm_num : (0 : Real) < 1)
  have he : -s + 1 = -(s - 1) := by ring
  rw [he] at hJval
  simp only [Complex.ofReal_one, Complex.one_cpow, neg_div_neg_eq] at hJval
  rw [hDecomp, hJval] at hz
  have hs1 : Not (s - 1 = 0) := by
    intro h
    have hr := congrArg Complex.re h
    simp only [Complex.sub_re, Complex.one_re, Complex.zero_re] at hr
    linarith
  unfold lpfPoleFilledZeta
  rw [hz]
  field_simp [hs1]


theorem lpf_poleFilledZeta_eq_poleFill (s : Complex) (hs : 0 < s.re) :
    lpfPoleFilledZeta s = lpfZetaPoleFill s := by
  let U : Set Complex := {z | 0 < z.re}
  have ho : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hg : AnalyticOnNhd Complex lpfZetaPoleFill U :=
    lpf_zetaPoleFill_differentiable.differentiableOn.analyticOnNhd ho
  have hConv : Convex Real U :=
    (convex_Ioi (0 : Real)).linear_preimage Complex.reCLM.toLinearMap
  have hNear : Filter.Eventually
      (fun z : Complex => lpfPoleFilledZeta z = lpfZetaPoleFill z) (nhds (2 : Complex)) := by
    have hOpen : IsOpen {z : Complex | 1 < z.re} :=
      isOpen_lt continuous_const Complex.continuous_re
    filter_upwards [hOpen.mem_nhds (show (2 : Complex).re > 1 by norm_num)] with z hz
    have hn : Not (z = 1) := by intro h; subst z; norm_num at hz
    simpa only [lpfZetaPoleFill, ite_eq_right hn] using lpf_poleFilledZeta_eq_of_one_lt_re z hz
  have hAll := lpf_poleFilledZeta_analyticOnNhd.eqOn_of_preconnected_of_eventuallyEq
    hg hConv.isPreconnected (show Membership.mem U (2 : Complex) by norm_num [U]) hNear
  apply hAll
  exact hs

theorem lpf_zetaPoleFill_norm_bound (s : Complex) (T : Real)
    (hs : 7 / 8 <= s.re) (hT : 1 <= T)
    (hsNorm : norm s <= T) (hsOne : norm (s - 1) <= T) :
    norm (lpfZetaPoleFill s) <= 4 * T ^ 2 := by
  rw [<- lpf_poleFilledZeta_eq_poleFill s (by linarith)]
  exact lpf_poleFilledZeta_norm_bound s T hs hT hsNorm hsOne

end PrimeFactorOscillations.QRH


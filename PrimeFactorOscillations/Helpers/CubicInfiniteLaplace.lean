/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.NumberTheory.LSeries.MellinEqDirichlet
import PrimeFactorOscillations.Helpers.CubicCompensatedWindow
import PrimeFactorOscillations.Helpers.CubicGaussianUnit
import PrimeFactorOscillations.Helpers.DirichletPacketMellin

/-!
# Infinite Dirichlet packets as convergent Laplace Mellin transforms

Proves actual exponential summability, L1 interchange and the gamma Mellin
identity, retaining arbitrary complex coefficients. The initial hypotheses
include LSeriesSummable at 2 and at the evaluated s. The existing character
coefficient comparison supplies these on Re(s)>1. No absolute convergence in
the zero-detection strip or arithmetic exponent improvement is assumed.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace PrimeFactorOscillations.CubicInfiniteLaplace
open MeasureTheory

private theorem integrable_tsum_from_norm_integrals
    (F : Nat -> Real -> Complex) (mu : Measure Real)
    (hF : forall n : Nat, Integrable (F n) mu)
    (hpoint : Filter.Eventually
      (fun t : Real => Summable (fun n : Nat => norm (F n t))) (ae mu))
    (hsum : Summable (fun n : Nat => integral mu (fun t : Real => norm (F n t)))) :
    Integrable (fun t : Real => tsum (fun n : Nat => F n t)) mu := by
  constructor
  . exact AEStronglyMeasurable.tsum (fun n => (hF n).aestronglyMeasurable)
  . apply (hasFiniteIntegral_iff_norm _).mpr
    calc
      lintegral mu (fun t : Real =>
          ENNReal.ofReal (norm (tsum (fun n : Nat => F n t)))) <=
        lintegral mu (fun t : Real =>
          tsum (fun n : Nat => ENNReal.ofReal (norm (F n t)))) := by
        apply lintegral_mono_ae
        exact hpoint.mono (fun t ht =>
          (ENNReal.ofReal_le_ofReal (norm_tsum_le_tsum_norm ht)).trans_eq
            (ENNReal.ofReal_tsum_of_nonneg (fun n => norm_nonneg (F n t)) ht))
      _ = tsum (fun n : Nat =>
          lintegral mu (fun t : Real => ENNReal.ofReal (norm (F n t)))) :=
        lintegral_tsum (fun n => (hF n).norm.aemeasurable.ennreal_ofReal)
      _ = tsum (fun n : Nat =>
          ENNReal.ofReal (integral mu (fun t : Real => norm (F n t)))) := by
        apply tsum_congr
        intro n
        exact (ofReal_integral_eq_lintegral_ofReal (hF n).norm
          (Filter.Eventually.of_forall (fun t => norm_nonneg (F n t)))).symm
      _ < Top.top := hsum.tsum_ofReal_lt_top

theorem lseries_summable {q : Nat} (chi : DirichletCharacter Complex q)
    (a : Nat -> Complex) (C : Real)
    (herror : forall n : Nat, Not (n = 0) ->
      norm (a n - DirichletPacketMellin.coefficient chi n) <= C / (n : Real))
    (s : Complex) (hs : 1 < s.re) : LSeriesSummable a s := by
  let e : Nat -> Complex := fun n => a n - DirichletPacketMellin.coefficient chi n
  have he : LSeriesSummable e s := by
    apply LSeriesSummable_of_abscissaOfAbsConv_lt_re
    exact (DirichletPacketMellin.correction_abscissa_le_zero chi a C herror).trans_lt
      (by exact_mod_cast (zero_lt_one.trans hs))
  have hf : LSeriesSummable (DirichletPacketMellin.coefficient chi) s :=
    DirichletCharacter.LSeriesSummable_twist_vonMangoldt chi hs
  have ha : a = DirichletPacketMellin.coefficient chi + e := by
    funext n
    simp only [Pi.add_apply, e]
    ring
  rw [ha]
  exact hf.add he

theorem norm_weights_summable (a : Nat -> Complex) (ha0 : a 0 = 0)
    (s : Complex) (ha : LSeriesSummable a s) :
    Summable (fun n : Nat => norm (a n) / (n : Real) ^ s.re) := by
  have hn := ha.norm
  apply hn.congr
  intro n
  rw [LSeries.norm_term_eq]
  by_cases hz : n = 0
  . subst n
    simp [ha0]
  . simp only [if_neg hz]

def laplace (a : Nat -> Complex) (K t : Real) : Complex :=
  tsum (fun n : Nat => a n * ((Real.exp (-(K * (n : Real)) * t) : Real) : Complex))

theorem laplace_summable (a : Nat -> Complex) (ha0 : a 0 = 0)
    (ha2 : LSeriesSummable a 2) (K t : Real) (hK : 0 < K) (ht : 0 < t) :
    Summable (fun n : Nat =>
      a n * ((Real.exp (-(K * (n : Real)) * t) : Real) : Complex)) := by
  let c : Real := K * t
  have hc : 0 < c := mul_pos hK ht
  have hc2 : 0 < c ^ 2 := sq_pos_of_pos hc
  have hbase : Summable (fun n : Nat => norm (a n) / (n : Real) ^ 2) := by
    have hh := norm_weights_summable a ha0 2 ha2
    change Summable (fun n : Nat => norm (a n) / (n : Real) ^ (2 : Real)) at hh
    simpa only [Real.rpow_two] using hh
  have hb (n : Nat) :
      norm (a n * ((Real.exp (-(K * (n : Real)) * t) : Real) : Complex)) <=
        (2 / c ^ 2) * (norm (a n) / (n : Real) ^ 2) := by
    by_cases hn : n = 0
    . subst n
      simp [ha0]
    . have hn0 : 0 < (n : Real) := by exact_mod_cast Nat.pos_of_ne_zero hn
      have hn2 : Not ((n : Real) ^ 2 = 0) := pow_ne_zero 2 hn0.ne'
      let u : Real := c * (n : Real)
      have hu : 0 <= u := mul_nonneg hc.le hn0.le
      have hh := Real.pow_div_factorial_le_exp u hu 2
      norm_num at hh
      have he : Real.exp u * Real.exp (-u) = 1 := by
        rw [<- Real.exp_add, add_neg_cancel, Real.exp_zero]
      have hm := mul_le_mul_of_nonneg_right hh (Real.exp_pos (-u)).le
      rw [he] at hm
      have hscale : ((n : Real) ^ 2 * Real.exp (-u)) * c ^ 2 <= 2 := by
        dsimp [u] at hm
        dsimp [u]
        nlinarith only [hm]
      have hval : (n : Real) ^ 2 * Real.exp (-u) <= 2 / c ^ 2 := by
        apply le_of_not_gt
        intro h
        have hlt := mul_lt_mul_of_pos_right h hc2
        have heq : (2 / c ^ 2) * c ^ 2 = 2 := by field_simp
        rw [heq] at hlt
        exact not_lt_of_ge hscale hlt
      have hexp : -(K * (n : Real)) * t = -u := by dsimp [u, c]; ring
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (Real.exp_pos _), hexp]
      calc
        _ = (norm (a n) / (n : Real) ^ 2) *
              ((n : Real) ^ 2 * Real.exp (-u)) := by field_simp
        _ <= (norm (a n) / (n : Real) ^ 2) * (2 / c ^ 2) :=
          mul_le_mul_of_nonneg_left hval (by positivity)
        _ = _ := by ring
  exact (Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hb
    (hbase.mul_left (2 / c ^ 2))).of_norm

theorem scaled_norm_weights_summable (a : Nat -> Complex) (ha0 : a 0 = 0)
    (s : Complex) (ha : LSeriesSummable a s) (K : Real) (hK : 0 < K) :
    Summable (fun n : Nat => norm (a n) / (K * (n : Real)) ^ s.re) := by
  have hh := (norm_weights_summable a ha0 s ha).mul_left (1 / K ^ s.re)
  apply hh.congr
  intro n
  rw [Real.mul_rpow hK.le (Nat.cast_nonneg n), div_mul_eq_div_div]
  ring

theorem mellin_term_integrable (a : Nat -> Complex) (ha0 : a 0 = 0)
    (K : Real) (hK : 0 < K) (s : Complex) (hs : 0 < s.re) (n : Nat) :
    Integrable (fun t : Real => (t : Complex) ^ (s - 1) *
      (a n * ((Real.exp (-(K * (n : Real)) * t) : Real) : Complex)))
      (volume.restrict (Set.Ioi (0 : Real))) := by
  by_cases hn : n = 0
  . subst n
    simp only [ha0, zero_mul, mul_zero]
    exact integrable_zero _ _ _
  . have hp : 0 < K * (n : Real) :=
      mul_pos hK (by exact_mod_cast Nat.pos_of_ne_zero hn)
    have hc : MellinConvergent
        (fun t : Real => CubicCompensatedWindow.expWindow ((K * (n : Real)) * t)) s :=
      (MellinConvergent.comp_mul_left hp).2
        (CubicCompensatedWindow.expWindow_convergent s hs)
    have hh := (hasMellin_const_smul hc (a n)).1
    have he : (fun t : Real =>
        a n * ((Real.exp (-(K * (n : Real)) * t) : Real) : Complex)) =
        (fun t : Real => a n *
          CubicCompensatedWindow.expWindow ((K * (n : Real)) * t)) := by
      funext t
      unfold CubicCompensatedWindow.expWindow
      rw [Complex.ofReal_exp]
      congr 2
      push_cast
      ring
    have hf : MellinConvergent (fun t : Real =>
        a n * ((Real.exp (-(K * (n : Real)) * t) : Real) : Complex)) s := by
      rw [he]
      simpa only [smul_eq_mul] using hh
    simpa only [MellinConvergent, IntegrableOn, smul_eq_mul] using hf

theorem integral_norm_mellin_term (a : Nat -> Complex) (ha0 : a 0 = 0)
    (K : Real) (hK : 0 < K) (s : Complex) (hs : 0 < s.re) (n : Nat) :
    integral (volume.restrict (Set.Ioi (0 : Real))) (fun t : Real =>
      norm ((t : Complex) ^ (s - 1) *
        (a n * ((Real.exp (-(K * (n : Real)) * t) : Real) : Complex)))) =
      Real.Gamma s.re * (norm (a n) / (K * (n : Real)) ^ s.re) := by
  by_cases hn : n = 0
  . subst n
    simp [ha0]
  . have hp : 0 < K * (n : Real) :=
      mul_pos hK (by exact_mod_cast Nat.pos_of_ne_zero hn)
    calc
      _ = norm (a n) * integral (volume.restrict (Set.Ioi (0 : Real)))
          (fun t : Real => t ^ (s.re - 1) * Real.exp (-((K * (n : Real)) * t))) := by
        rw [<- integral_const_mul]
        apply setIntegral_congr_fun measurableSet_Ioi
        intro t ht
        dsimp only
        rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht,
          Complex.norm_real, Real.norm_eq_abs, Real.abs_exp]
        simp only [Complex.sub_re, Complex.one_re]
        rw [show -(K * (n : Real)) * t = -((K * (n : Real)) * t) by ring]
        ring
      _ = norm (a n) * ((1 / (K * (n : Real))) ^ s.re * Real.Gamma s.re) := by
        rw [Real.integral_rpow_mul_exp_neg_mul_Ioi hs hp]
      _ = _ := by
        rw [one_div, Real.inv_rpow hp.le]
        ring

theorem laplace_convergent (a : Nat -> Complex) (ha0 : a 0 = 0)
    (ha2 : LSeriesSummable a 2) (K : Real) (hK : 0 < K)
    (s : Complex) (hs : 0 < s.re) (ha : LSeriesSummable a s) :
    MellinConvergent (laplace a K) s := by
  let F : Nat -> Real -> Complex := fun n t =>
    (t : Complex) ^ (s - 1) *
      (a n * ((Real.exp (-(K * (n : Real)) * t) : Real) : Complex))
  have hF (n : Nat) : Integrable (F n) (volume.restrict (Set.Ioi (0 : Real))) :=
    mellin_term_integrable a ha0 K hK s hs n
  have hsum : Summable (fun n : Nat =>
      integral (volume.restrict (Set.Ioi (0 : Real))) (fun t : Real => norm (F n t))) := by
    apply ((scaled_norm_weights_summable a ha0 s ha K hK).mul_left
      (Real.Gamma s.re)).congr
    intro n
    exact (integral_norm_mellin_term a ha0 K hK s hs n).symm
  have hpoint : Filter.Eventually
      (fun t : Real => Summable (fun n : Nat => norm (F n t)))
      (ae (volume.restrict (Set.Ioi (0 : Real)))) := by
    apply (ae_restrict_mem measurableSet_Ioi).mono
    intro t ht
    exact ((laplace_summable a ha0 ha2 K t hK ht).mul_left
      ((t : Complex) ^ (s - 1))).norm
  have hi := integrable_tsum_from_norm_integrals F
    (volume.restrict (Set.Ioi (0 : Real))) hF hpoint hsum
  have he : (fun t : Real => tsum (fun n : Nat => F n t)) =
      (fun t : Real => (t : Complex) ^ (s - 1) * laplace a K t) := by
    funext t
    exact tsum_mul_left
  rw [he] at hi
  simpa only [MellinConvergent, IntegrableOn, smul_eq_mul] using hi

theorem laplace_hasMellin (a : Nat -> Complex) (ha0 : a 0 = 0)
    (ha2 : LSeriesSummable a 2) (K : Real) (hK : 0 < K)
    (s : Complex) (hs : 0 < s.re) (ha : LSeriesSummable a s) :
    HasMellin (laplace a K) s
      ((K : Complex) ^ (-s) * Complex.Gamma s * LSeries a s) := by
  refine And.intro (laplace_convergent a ha0 ha2 K hK s hs ha) ?_
  have hp (n : Nat) : a n = 0 \/ 0 < K * (n : Real) := by
    by_cases hn : n = 0
    . exact Or.inl (by simpa only [hn] using ha0)
    . exact Or.inr (mul_pos hK (by exact_mod_cast Nat.pos_of_ne_zero hn))
  have hh := hasSum_mellin (a := a) (p := fun n : Nat => K * (n : Real))
    (F := laplace a K) hp hs
    (fun t ht => (laplace_summable a ha0 ha2 K t hK ht).hasSum)
    (scaled_norm_weights_summable a ha0 s ha K hK)
  have hterms : (fun n : Nat => Complex.Gamma s * a n /
        (((K * (n : Real)) : Real) : Complex) ^ s) =
      (fun n : Nat => ((K : Complex) ^ (-s) * Complex.Gamma s) *
        LSeries.term a s n) := by
    funext n
    by_cases hn : n = 0
    . simp [hn, ha0, LSeries.term]
    . rw [Complex.ofReal_mul,
        Complex.mul_cpow_ofReal_nonneg hK.le (Nat.cast_nonneg n)]
      simp only [Complex.ofReal_natCast, LSeries.term, if_neg hn,
        Complex.cpow_neg, div_eq_mul_inv, mul_inv]
      ring
  rw [hterms] at hh
  exact hh.unique (ha.hasSum.mul_left ((K : Complex) ^ (-s) * Complex.Gamma s))

end PrimeFactorOscillations.CubicInfiniteLaplace

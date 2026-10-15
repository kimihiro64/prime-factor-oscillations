/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.NumberTheory.LSeries.Basic
import PrimeFactorOscillations.Helpers.LPFMajorNormalizedLog
import PrimeFactorOscillations.Helpers.LPFOverlapEulerNumeric

/-!
# Numerical logarithmic-derivative estimate for nonprincipal characters

The convergent series supplies a uniform center lower bound. The cached
BV polynomial growth estimate and audited seven-eighths nonvanishing theorem
then discharge every input of the normalized-log disk bound.
The principal-character pole and numerical contour transfer remain separate.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.QRH

private theorem inverse_square_Icc_tail_quarter (N : Nat) :
    Finset.sum (Finset.Icc 2 N) (fun n => 1 / (n : Real) ^ 2) <= 3 / 4 := by
  by_cases hN : 2 <= N
  next =>
    have he : Finset.Icc 2 N = insert 2 (Finset.Ioc 2 N) := by
      ext n
      simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_Ioc]
      omega
    have hn : Not (Membership.mem (Finset.Ioc 2 N) 2) := by simp
    rw [he, Finset.sum_insert hn]
    have ht := LPF.lpf_overlap_inverse_square_Ioc_tail 2 N (by omega) hN
    norm_num at ht
    norm_num
    have hz : 0 <= 1 / (N : Real) := by positivity
    rw [one_div] at hz
    linarith
  next =>
    have hz : Finset.sum (Finset.Icc 2 N)
        (fun n => 1 / (n : Real) ^ 2) = 0 := by
      apply Finset.sum_eq_zero
      intro n hn
      have h := Finset.mem_Icc.mp hn
      omega
    rw [hz]
    norm_num

theorem lpf_LSeries_center_lower (a : Nat -> Complex) (s : Complex)
    (ha : forall n, norm (a n) <= 1) (ha1 : a 1 = 1) (hs : s.re = 2) :
    1 / 4 <= norm (LSeries a s) := by
  have ht0 : LSeries.term a s 0 = 0 := by simp [LSeries.term]
  have ht1 : LSeries.term a s 1 = 1 := by
    rw [LSeries.term_of_ne_zero (by norm_num : Not ((1 : Nat) = 0))]
    simp [ha1]
  have hterm (n : Nat) (hn : 2 <= n) :
      norm (LSeries.term a s n) <= 1 / (n : Real) ^ 2 := by
    rw [LSeries.norm_term_eq]
    simp only [show Not (n = 0) by omega, ite_false, hs, Real.rpow_two]
    exact div_le_div_of_nonneg_right (ha n) (sq_nonneg _)
  have hfinite (N : Nat) (hN : 2 <= N) :
      norm (Finset.sum (Finset.range N) (LSeries.term a s) - 1) <= 3 / 4 := by
    have he : Finset.range N =
        insert 0 (insert 1 (Finset.Icc 2 (N - 1))) := by
      ext n
      simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
      omega
    have h0 : Not (Membership.mem (insert 1 (Finset.Icc 2 (N - 1))) 0) := by simp
    have h1 : Not (Membership.mem (Finset.Icc 2 (N - 1)) 1) := by simp
    rw [he, Finset.sum_insert h0, Finset.sum_insert h1, ht0, ht1]
    simp only [zero_add, add_sub_cancel_left]
    calc
      _ <= Finset.sum (Finset.Icc 2 (N - 1))
          (fun n => norm (LSeries.term a s n)) := norm_sum_le _ _
      _ <= Finset.sum (Finset.Icc 2 (N - 1))
          (fun n => 1 / (n : Real) ^ 2) := by
        apply Finset.sum_le_sum
        intro n hn
        exact hterm n (Finset.mem_Icc.mp hn).1
      _ <= _ := inverse_square_Icc_tail_quarter (N - 1)
  have hsum : LSeriesSummable a s :=
    LSeriesSummable_of_bounded_of_one_lt_re (fun n _ => ha n) (by rw [hs]; norm_num)
  have hhas : HasSum (LSeries.term a s) (LSeries a s) := hsum.LSeriesHasSum
  have hlimit := (hhas.tendsto_sum_nat.sub_const (1 : Complex)).norm
  have hd : norm (LSeries a s - 1) <= 3 / 4 := by
    apply le_of_tendsto hlimit
    filter_upwards [Filter.eventually_ge_atTop (2 : Nat)] with N hN
    exact hfinite N hN
  have hr := norm_sub_norm_le (1 : Complex) (LSeries a s)
  rw [norm_one, norm_sub_rev] at hr
  linarith


theorem lpf_LFunction_center_lower {N : Nat} [NeZero N]
    (chi : DirichletCharacter Complex N) (t : Real) :
    1 / 4 <= norm (chi.LFunction (2 + Complex.I * (t : Complex))) := by
  have hs : (2 + Complex.I * (t : Complex)).re = 2 := by simp
  rw [chi.LFunction_eq_LSeries (by rw [hs]; norm_num)]
  exact lpf_LSeries_center_lower _ _
    (fun n => chi.norm_le_one (n : ZMod N)) (by simp) hs

theorem lpf_nonprincipal_log_deriv_numeric
    {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N)
    (hchi : Not (chi = 1)) (t : Real) (z : Complex)
    (hz : dist z (2 + Complex.I * (t : Complex)) <= 17 / 16) :
    norm (deriv chi.LFunction z / chi.LFunction z) <=
      13312 * (1 + Real.log (N : Real) + Real.log (abs t + 8)) := by
  let c : Complex := 2 + Complex.I * (t : Complex)
  let T : Real := abs t + 8
  let B0 : Real := 1 + Real.log (N : Real) + Real.log T
  have hN : 1 <= (N : Real) := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (NeZero.ne N))
  have hT : 1 <= T := by dsimp [T]; linarith [abs_nonneg t]
  have hLogN : 0 <= Real.log (N : Real) := Real.log_nonneg hN
  have hLogT : 0 <= Real.log T := Real.log_nonneg hT
  have hB : 0 < 4 * B0 := by dsimp [B0]; linarith
  have hcRe : c.re = 2 := by simp [c]
  have hRe (w : Complex) (hw : Membership.mem (Metric.ball c (9 / 8)) w) :
      7 / 8 < w.re := by
    have hd := Metric.mem_ball.mp hw
    rw [dist_eq_norm] at hd
    have hl := (abs_le.mp (Complex.abs_re_le_norm (w - c))).1
    simp only [Complex.sub_re, hcRe] at hl
    linarith
  have hAnalytic : AnalyticOnNhd Complex chi.LFunction (Metric.ball c (9 / 8)) :=
    (DirichletCharacter.differentiable_LFunction hchi).differentiableOn.analyticOnNhd
      Metric.isOpen_ball
  have hNonzero : forall w, Membership.mem (Metric.ball c (9 / 8)) w ->
      Not (chi.LFunction w = 0) := by
    intro w hw
    exact OAI.DirichletCharacter.LFunction_ne_zero_of_seven_eighths_lt_re
      chi (hRe w hw) (fun h => hchi h.1)
  have hcBound : norm c <= 2 + abs t := by
    have h := norm_add_le (2 : Complex) (Complex.I * (t : Complex))
    simpa [c, norm_mul, Complex.norm_I, Complex.norm_real,
      Real.norm_eq_abs] using h
  have hLogEight : Real.log (8 : Real) <= 3 := by
    have hTwo := Real.log_le_sub_one_of_pos (by norm_num : (0 : Real) < 2)
    have he : Real.log (8 : Real) = 3 * Real.log (2 : Real) := by
      rw [show (8 : Real) = 2 ^ (3 : Nat) by norm_num, Real.log_pow]
      norm_num
    rw [he]
    linarith
  have hProdPos : 0 < 8 * (N : Real) * T := by positivity
  have hExp : 8 * (N : Real) * T <= Real.exp (4 * B0) := by
    calc
      _ = Real.exp (Real.log (8 * (N : Real) * T)) := (Real.exp_log hProdPos).symm
      _ <= _ := by
        apply Real.exp_le_exp.mpr
        rw [Real.log_mul (by positivity) (by positivity),
          Real.log_mul (by norm_num) (by positivity)]
        dsimp [B0]
        linarith
  have hCenter : 1 / 4 <= norm (chi.LFunction c) :=
    lpf_LFunction_center_lower chi t
  have hGrowth : forall w, Membership.mem (Metric.ball c (9 / 8)) w ->
      norm (chi.LFunction w) <= Real.exp (4 * B0) * norm (chi.LFunction c) := by
    intro w hw
    have hd := Metric.mem_ball.mp hw
    rw [dist_eq_norm] at hd
    have hwNorm : norm w <= T := by
      have h := norm_add_le (w - c) c
      rw [sub_add_cancel] at h
      dsimp [T]
      linarith
    have hRaw : norm (chi.LFunction w) <= 2 * (N : Real) * norm w :=
      BombieriVinogradov.norm_LFunction_le_two_mul_modulus_mul_norm
        chi hchi (by have h := hRe w hw; linarith)
    calc
      _ <= 2 * (N : Real) * T :=
        hRaw.trans (mul_le_mul_of_nonneg_left hwNorm (by positivity))
      _ <= Real.exp (4 * B0) * (1 / 4) := by linarith only [hExp]
      _ <= _ := mul_le_mul_of_nonneg_left hCenter (Real.exp_pos _).le
  have h := lpf_log_deriv_disc_growth_bound chi.LFunction c z (4 * B0)
    hB hAnalytic hNonzero hGrowth hz
  dsimp [B0, T] at h
  linarith only [h]

end PrimeFactorOscillations.QRH

/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import PrimeFactorOscillations.Helpers.XiEffectiveBounds

/-!
# Effective real Euler bounds at half-integer abscissae

The logarithmic Dirichlet series is bounded with its complete infinite tail.
No finite sampling of zeros or heights is used.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

open MeasureTheory
open scoped Interval Topology BigOperators ComplexOrder

def eulerLogProfile (x : Real) : Real := Real.log x * x ^ (-(5 / 2) : Real)

def eulerLogPrimitive (x : Real) : Real :=
  -(x ^ (-(3 / 2) : Real) * ((2 / 3) * Real.log x + 4 / 9))

theorem eulerLogPrimitive_hasDerivAt (x : Real) (hx : 0 < x) :
    HasDerivAt eulerLogPrimitive (eulerLogProfile x) x := by
  have hp := Real.hasDerivAt_rpow_const (x := x) (p := -(3 / 2)) (Or.inl hx.ne')
  have hl := Real.hasDerivAt_log hx.ne'
  have hh := (hp.mul ((hl.const_mul (2 / 3)).add_const (4 / 9))).neg
  have he : x ^ (-(3 / 2) : Real) = x ^ (-(5 / 2) : Real) * x := by
    calc
      x ^ (-(3 / 2) : Real) = x ^ ((-(5 / 2) : Real) + 1) := by norm_num
      _ = x ^ (-(5 / 2) : Real) * x ^ (1 : Real) := Real.rpow_add hx _ _
      _ = x ^ (-(5 / 2) : Real) * x := by rw [Real.rpow_one]
  convert hh using 1 <;> first
  | rfl
  | (norm_num [eulerLogProfile]; rw [he]; field_simp [hx.ne']; ring)

theorem eulerLogProfile_hasDerivAt (x : Real) (hx : 0 < x) :
    HasDerivAt eulerLogProfile
      (x ^ (-(7 / 2) : Real) * (1 - (5 / 2) * Real.log x)) x := by
  have hh := (Real.hasDerivAt_log hx.ne').mul
    (Real.hasDerivAt_rpow_const (x := x) (p := -(5 / 2)) (Or.inl hx.ne'))
  have he : x ^ (-(5 / 2) : Real) = x ^ (-(7 / 2) : Real) * x := by
    calc
      x ^ (-(5 / 2) : Real) = x ^ ((-(7 / 2) : Real) + 1) := by norm_num
      _ = x ^ (-(7 / 2) : Real) * x ^ (1 : Real) := Real.rpow_add hx _ _
      _ = x ^ (-(7 / 2) : Real) * x := by rw [Real.rpow_one]
  convert hh using 1 <;> first
  | rfl
  | (norm_num [eulerLogProfile]; rw [he]; field_simp [hx.ne']; ring)

theorem eulerLogProfile_antitone : AntitoneOn eulerLogProfile (Set.Ici (6 : Real)) := by
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici (6 : Real))
  next =>
    intro x hx
    have hm : (6 : Real) <= x := hx
    exact (eulerLogProfile_hasDerivAt x (by linarith only [hm])).continuousAt.continuousWithinAt
  next =>
    intro x hx
    have hm : (6 : Real) <= x := interior_subset hx
    exact (eulerLogProfile_hasDerivAt x (by linarith only [hm])).hasDerivWithinAt
  next =>
    intro x hx
    have hm : (6 : Real) <= x := interior_subset hx
    have hl := Real.log_le_log (by norm_num : (0 : Real) < 2)
      (by linarith only [hm] : (2 : Real) <= x)
    have hlog := Real.log_two_gt_d9
    exact mul_nonpos_of_nonneg_of_nonpos (Real.rpow_nonneg (by linarith only [hm]) _)
      (by linarith only [hl, hlog])

theorem eulerLogProfile_sum_tail_upper (M : Nat) :
    Finset.sum (Finset.range M) (fun n : Nat => eulerLogProfile (n + 7 : Nat)) <=
      -eulerLogPrimitive 6 := by
  have ha : AntitoneOn eulerLogProfile (Set.Icc (6 : Real) (6 + (M : Real))) :=
    eulerLogProfile_antitone.mono (fun _ hx => hx.1)
  have hc := ha.sum_le_integral
  have hd : forall x : Real, Membership.mem (Set.uIcc (6 : Real) (6 + (M : Real))) x ->
      HasDerivAt eulerLogPrimitive (eulerLogProfile x) x := by
    intro x hx
    have hh : And (6 <= x) (x <= 6 + (M : Real)) := by
      simpa only [Set.uIcc_of_le (show (6 : Real) <= 6 + (M : Real) from
        by have hm : (0 : Real) <= (M : Real) := Nat.cast_nonneg M; linarith only [hm]),
        Set.mem_Icc] using hx
    exact eulerLogPrimitive_hasDerivAt x (by linarith only [hh.1])
  have hi : IntervalIntegrable eulerLogProfile volume (6 : Real) (6 + (M : Real)) := by
    apply ContinuousOn.intervalIntegrable
    intro x hx
    have hh : And (6 <= x) (x <= 6 + (M : Real)) := by
      simpa only [Set.uIcc_of_le (show (6 : Real) <= 6 + (M : Real) from
        by have hm : (0 : Real) <= (M : Real) := Nat.cast_nonneg M; linarith only [hm]),
        Set.mem_Icc] using hx
    exact (eulerLogProfile_hasDerivAt x (by linarith only [hh.1])).continuousAt.continuousWithinAt
  have hv := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi
  have hn : eulerLogPrimitive (6 + (M : Real)) <= 0 := by
    dsimp only [eulerLogPrimitive]
    have hl : 0 <= Real.log (6 + (M : Real)) :=
      Real.log_nonneg (by have hm : (0 : Real) <= (M : Real) := Nat.cast_nonneg M; linarith only [hm])
    have hp := Real.rpow_nonneg (by positivity : (0 : Real) <= 6 + (M : Real)) (-(3 / 2) : Real)
    nlinarith only [hl, hp]
  rw [hv] at hc
  have hsum : Finset.sum (Finset.range M) (fun n : Nat => eulerLogProfile (n + 7 : Nat)) =
      Finset.sum (Finset.range M) (fun n : Nat => eulerLogProfile (6 + (n + 1 : Nat))) := by
    apply Finset.sum_congr rfl
    intro n _
    congr 1
    push_cast
    ring
  rw [hsum]
  have hsum2 : Finset.sum (Finset.range M) (fun n : Nat => eulerLogProfile (6 + (n + 1 : Nat))) =
      Finset.sum (Finset.range M) (fun n : Nat => eulerLogProfile ((6 : Real) + ((n + 1 : Nat) : Real))) := by
    apply Finset.sum_congr rfl
    intro n _
    simp only [Nat.cast_add, Nat.cast_ofNat]
  rw [hsum2]
  linarith only [hc, hn]

theorem eulerHalfPower_eq (x : Real) (hx : 0 <= x) :
    x ^ (-(5 / 2) : Real) = 1 / (x ^ 2 * Real.sqrt x) := by
  rcases eq_or_lt_of_le hx with h | h
  next => subst x; norm_num
  next =>
    rw [Real.rpow_neg hx, one_div]
    congr 1
    calc
      x ^ (5 / 2 : Real) = x ^ ((2 : Real) + 1 / 2) := by norm_num
      _ = x ^ (2 : Real) * x ^ (1 / 2 : Real) := Real.rpow_add h _ _
      _ = x ^ 2 * Real.sqrt x := by rw [Real.rpow_two, Real.sqrt_eq_rpow]

theorem eulerThreeHalfPower_eq (x : Real) (hx : 0 <= x) :
    x ^ (-(3 / 2) : Real) = 1 / (x * Real.sqrt x) := by
  rcases eq_or_lt_of_le hx with h | h
  next => subst x; norm_num
  next =>
    rw [Real.rpow_neg hx, one_div]
    congr 1
    calc
      x ^ (3 / 2 : Real) = x ^ ((1 : Real) + 1 / 2) := by norm_num
      _ = x ^ (1 : Real) * x ^ (1 / 2 : Real) := Real.rpow_add h _ _
      _ = x * Real.sqrt x := by rw [Real.rpow_one, Real.sqrt_eq_rpow]

theorem eulerSqrt_lower (x a : Real) (hx : 0 <= x) (ha : 0 <= a) (hs : a ^ 2 <= x) :
    a <= Real.sqrt x := by
  nlinarith only [Real.sq_sqrt hx, Real.sqrt_nonneg x, ha, hs]

theorem eulerSqrt_upper (x a : Real) (hx : 0 <= x) (ha : 0 <= a) (hs : x <= a ^ 2) :
    Real.sqrt x <= a := by
  nlinarith only [Real.sq_sqrt hx, Real.sqrt_nonneg x, ha, hs]

theorem eulerLogProfile_le (x a l : Real) (hx : 0 < x) (ha : 0 < a)
    (hl : Real.log x <= l) (hl0 : 0 <= l) (hroot : a <= Real.sqrt x) :
    eulerLogProfile x <= l / (x ^ 2 * a) := by
  rw [eulerLogProfile, eulerHalfPower_eq x hx.le, mul_one_div]
  calc
    Real.log x / (x ^ 2 * Real.sqrt x) <= l / (x ^ 2 * Real.sqrt x) :=
      div_le_div_of_nonneg_right hl (mul_nonneg (sq_nonneg x) (Real.sqrt_nonneg x))
    _ <= _ := div_le_div_of_nonneg_left hl0 (mul_pos (sq_pos_of_pos hx) ha)
      (mul_le_mul_of_nonneg_left hroot (sq_nonneg x))

theorem eulerLogProfile_head_tail_certificate :
    Finset.sum (Finset.range 7) (fun n : Nat => eulerLogProfile n) -
      eulerLogPrimitive 6 <= 159 / 400 := by
  have h2 : Real.log 2 <= 693148 / 1000000 := le_of_lt (lt_trans Real.log_two_lt_d9 (by norm_num))
  have h3 : Real.log 3 <= 1098613 / 1000000 := le_of_lt (lt_trans Real.log_three_lt_d9 (by norm_num))
  have he6 : Real.log 6 = Real.log 2 + Real.log 3 := by
    rw [show (6 : Real) = 2 * 3 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
  have h6 : Real.log 6 <= 1791761 / 1000000 := by linarith only [h2, h3, he6]
  have he4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : Real) = 2 ^ (2 : Nat) by norm_num, Real.log_pow]
    norm_num
  have h4 : Real.log 4 <= 1386296 / 1000000 := by linarith only [h2, he4]
  have h5 : Real.log 5 <= 1791761 / 1000000 - 1 / 6 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : Real) < 5 / 6)
    rw [Real.log_div (by norm_num) (by norm_num)] at hh
    linarith only [hh, h6]
  have sr2 : (707 / 500 : Real) <= Real.sqrt 2 := eulerSqrt_lower 2 _ (by norm_num) (by norm_num) (by norm_num)
  have sr3 : (433 / 250 : Real) <= Real.sqrt 3 := eulerSqrt_lower 3 _ (by norm_num) (by norm_num) (by norm_num)
  have sr5 : (559 / 250 : Real) <= Real.sqrt 5 := eulerSqrt_lower 5 _ (by norm_num) (by norm_num) (by norm_num)
  have sr6 : (2449 / 1000 : Real) <= Real.sqrt 6 := eulerSqrt_lower 6 _ (by norm_num) (by norm_num) (by norm_num)
  have a2 := eulerLogProfile_le 2 _ _ (by norm_num) (by norm_num) h2 (by norm_num) sr2
  have a3 := eulerLogProfile_le 3 _ _ (by norm_num) (by norm_num) h3 (by norm_num) sr3
  have a4 := eulerLogProfile_le 4 2 _ (by norm_num) (by norm_num) h4 (by norm_num)
    (eulerSqrt_lower 4 2 (by norm_num) (by norm_num) (by norm_num))
  have a5 := eulerLogProfile_le 5 _ _ (by norm_num) (by norm_num) h5 (by norm_num) sr5
  have a6 := eulerLogProfile_le 6 _ _ (by norm_num) (by norm_num) h6 (by norm_num) sr6
  have ht : -eulerLogPrimitive 6 <=
      ((2 / 3) * (1791761 / 1000000) + 4 / 9) / (6 * (2449 / 1000)) := by
    have hd : -eulerLogPrimitive 6 = ((2 / 3) * Real.log 6 + 4 / 9) / (6 * Real.sqrt 6) := by
      rw [eulerLogPrimitive, neg_neg, eulerThreeHalfPower_eq 6 (by norm_num)]
      ring
    rw [hd]
    calc
      _ <= ((2 / 3) * (1791761 / 1000000) + 4 / 9) / (6 * Real.sqrt 6) :=
        div_le_div_of_nonneg_right (by linarith only [h6]) (by positivity)
      _ <= _ := div_le_div_of_nonneg_left (by norm_num) (by norm_num)
        (by linarith only [sr6])
  have hs : Finset.sum (Finset.range 7) (fun n : Nat => eulerLogProfile n) =
      eulerLogProfile 2 + eulerLogProfile 3 + eulerLogProfile 4 +
        eulerLogProfile 5 + eulerLogProfile 6 := by
    norm_num [Finset.sum_range_succ, eulerLogProfile]
  rw [hs]
  norm_num at a2 a3 a4 a5 a6 ht
  linarith only [a2, a3, a4, a5, a6, ht]

theorem eulerHalfPower_ge (x b : Real) (hx : 0 < x) (hb : 0 < b)
    (hroot : Real.sqrt x <= b) :
    1 / (x ^ 2 * b) <= x ^ (-(5 / 2) : Real) := by
  rw [eulerHalfPower_eq x hx.le]
  exact one_div_le_one_div_of_le
    (mul_pos (sq_pos_of_pos hx) (Real.sqrt_pos.mpr hx))
    (mul_le_mul_of_nonneg_left hroot (sq_nonneg x))

theorem eulerZeta_head_certificate :
    53 / 40 <= Finset.sum (Finset.range 13) (fun n : Nat =>
      (n : Real) ^ (-(5 / 2) : Real)) := by
  have h2 := eulerHalfPower_ge 2 (283 / 200) (by norm_num) (by norm_num)
    (eulerSqrt_upper 2 _ (by norm_num) (by norm_num) (by norm_num))
  have h3 := eulerHalfPower_ge 3 (1733 / 1000) (by norm_num) (by norm_num)
    (eulerSqrt_upper 3 _ (by norm_num) (by norm_num) (by norm_num))
  have h4 := eulerHalfPower_ge 4 (2) (by norm_num) (by norm_num)
    (eulerSqrt_upper 4 _ (by norm_num) (by norm_num) (by norm_num))
  have h5 := eulerHalfPower_ge 5 (2237 / 1000) (by norm_num) (by norm_num)
    (eulerSqrt_upper 5 _ (by norm_num) (by norm_num) (by norm_num))
  have h6 := eulerHalfPower_ge 6 (49 / 20) (by norm_num) (by norm_num)
    (eulerSqrt_upper 6 _ (by norm_num) (by norm_num) (by norm_num))
  have h7 := eulerHalfPower_ge 7 (1323 / 500) (by norm_num) (by norm_num)
    (eulerSqrt_upper 7 _ (by norm_num) (by norm_num) (by norm_num))
  have h8 := eulerHalfPower_ge 8 (283 / 100) (by norm_num) (by norm_num)
    (eulerSqrt_upper 8 _ (by norm_num) (by norm_num) (by norm_num))
  have h9 := eulerHalfPower_ge 9 (3) (by norm_num) (by norm_num)
    (eulerSqrt_upper 9 _ (by norm_num) (by norm_num) (by norm_num))
  have h10 := eulerHalfPower_ge 10 (3163 / 1000) (by norm_num) (by norm_num)
    (eulerSqrt_upper 10 _ (by norm_num) (by norm_num) (by norm_num))
  have h11 := eulerHalfPower_ge 11 (3317 / 1000) (by norm_num) (by norm_num)
    (eulerSqrt_upper 11 _ (by norm_num) (by norm_num) (by norm_num))
  have h12 := eulerHalfPower_ge 12 (1733 / 500) (by norm_num) (by norm_num)
    (eulerSqrt_upper 12 _ (by norm_num) (by norm_num) (by norm_num))
  norm_num at h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
  norm_num [Finset.sum_range_succ]
  linarith only [h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12]

theorem eulerLogProfile_tsum_bound
    (hs : Summable (fun n : Nat => eulerLogProfile n)) :
    tsum (fun n : Nat => eulerLogProfile n) <= 159 / 400 := by
  have ht : Summable (fun n : Nat => eulerLogProfile (n + 7 : Nat)) :=
    hs.comp_injective (fun _ _ h => Nat.add_right_cancel h)
  have hb : tsum (fun n : Nat => eulerLogProfile (n + 7 : Nat)) <=
      -eulerLogPrimitive 6 :=
    le_of_tendsto ht.hasSum.tendsto_sum_nat
      (Filter.Eventually.of_forall eulerLogProfile_sum_tail_upper)
  have he := hs.sum_add_tsum_nat_add 7
  have hc := eulerLogProfile_head_tail_certificate
  linarith only [hb, he, hc]

theorem eulerLogProfile_term_norm (n : Nat) :
    norm (LSeries.term (fun n : Nat => Complex.log n) (5 / 2 : Complex) n) =
      eulerLogProfile n := by
  by_cases hn : n = 0
  next => subst n; norm_num [LSeries.term_zero, eulerLogProfile]
  next =>
    rw [LSeries.norm_term_eq, if_neg hn]
    simp only [<- Complex.natCast_log, Complex.norm_real,
      abs_of_nonneg (Real.log_natCast_nonneg n)]
    norm_num
    rw [abs_of_nonneg (Real.log_natCast_nonneg n), eulerLogProfile,
      Real.rpow_neg (Nat.cast_nonneg n), div_eq_mul_inv]

theorem eulerLogSeries_norm_bound :
    norm (LSeries (fun n : Nat => Complex.log n) (5 / 2 : Complex)) <= 159 / 400 := by
  have hlog := LSeriesSummable_logMul_of_lt_re
    (f := (1 : Nat -> Complex)) (s := (5 / 2 : Complex))
    (by rw [LSeries.abscissaOfAbsConv_one]; norm_num;
        exact_mod_cast (by norm_num : (1 : Real) < 5 / 2))
  have hcoeff : LSeries.logMul (1 : Nat -> Complex) = (fun n : Nat => Complex.log n) := by
    funext n
    simp [LSeries.logMul]
  rw [hcoeff] at hlog
  have hs : Summable (LSeries.term (fun n : Nat => Complex.log n) (5 / 2 : Complex)) := hlog
  have hf : Summable (fun n : Nat => eulerLogProfile n) :=
    hs.norm.congr eulerLogProfile_term_norm
  calc
    norm (LSeries (fun n : Nat => Complex.log n) (5 / 2 : Complex)) <=
        tsum (fun n : Nat => norm (LSeries.term (fun n : Nat => Complex.log n)
          (5 / 2 : Complex) n)) := norm_tsum_le_tsum_norm hs.norm
    _ = tsum (fun n : Nat => eulerLogProfile n) := tsum_congr eulerLogProfile_term_norm
    _ <= 159 / 400 := eulerLogProfile_tsum_bound hf

theorem eulerOne_term_norm (n : Nat) :
    norm (LSeries.term (1 : Nat -> Complex) (5 / 2 : Complex) n) =
      (n : Real) ^ (-(5 / 2) : Real) := by
  by_cases hn : n = 0
  next => subst n; norm_num [LSeries.term_zero]
  next =>
    rw [LSeries.norm_term_eq, if_neg hn]
    norm_num
    simp only [Real.rpow_neg (Nat.cast_nonneg n), one_div]

theorem eulerZeta_norm_lower : 53 / 40 <= norm (riemannZeta (5 / 2 : Complex)) := by
  have hs : LSeriesSummable (1 : Nat -> Complex) (5 / 2 : Complex) :=
    LSeriesSummable_one_iff.mpr (by norm_num)
  let f : Nat -> Complex := LSeries.term (1 : Nat -> Complex) (5 / 2 : Complex)
  have hp (n : Nat) : 0 <= f n := by
    have hh := LSeries.term_nonneg (a := (1 : Nat -> Complex)) (n := n)
      (by norm_num) (5 / 2 : Real)
    have he : ((5 / 2 : Real) : Complex) = (5 / 2 : Complex) := by norm_num
    rw [he] at hh
    exact hh
  have ht : 0 <= tsum f := tsum_nonneg hp
  have he : norm (LSeries (1 : Nat -> Complex) (5 / 2 : Complex)) =
      tsum (fun n : Nat => norm (f n)) := by
    calc
      _ = (tsum f).re := (Complex.re_eq_norm.mpr ht).symm
      _ = tsum (fun n : Nat => (f n).re) := Complex.re_tsum hs
      _ = _ := tsum_congr (fun n => Complex.re_eq_norm.mpr (hp n))
  have hh : Finset.sum (Finset.range 13) (fun n : Nat => norm (f n)) >= 53 / 40 := by
    simpa only [f, eulerOne_term_norm] using eulerZeta_head_certificate
  have hsplit := hs.norm.sum_add_tsum_nat_add 13
  have htail : 0 <= tsum (fun n : Nat => norm (f (n + 13))) := tsum_nonneg (fun n => norm_nonneg _)
  rw [LSeries_one_eq_riemannZeta (by norm_num)] at he
  change Finset.sum (Finset.range 13) (fun n : Nat => norm (f n)) +
    tsum (fun n : Nat => norm (f (n + 13))) = _ at hsplit
  linarith only [he, hh, hsplit, htail]

theorem xiEulerBound_five_halves : xiEulerBound (5 / 2) <= 3 / 10 := by
  have hLambda := ArithmeticFunction.LSeriesSummable_vonMangoldt
    (s := (5 / 2 : Complex)) (by norm_num)
  have hOne : LSeriesSummable (1 : Nat -> Complex) (5 / 2 : Complex) :=
    LSeriesSummable_one_iff.mpr (by norm_num)
  have hc := LSeries_convolution' hLambda hOne
  rw [ArithmeticFunction.convolution_vonMangoldt_const_one] at hc
  have hn := congrArg norm hc
  rw [norm_mul, LSeries_one_eq_riemannZeta (by norm_num),
    ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div (by norm_num)] at hn
  have hlog := eulerLogSeries_norm_bound
  have hz := eulerZeta_norm_lower
  have he : norm (-deriv riemannZeta (5 / 2 : Complex) / riemannZeta (5 / 2 : Complex)) =
      xiEulerBound (5 / 2) := by
    simp [xiEulerBound, zetaEulerLogDeriv, neg_div, norm_neg]
  rw [he] at hn
  have hp := xiEulerBound_nonneg (5 / 2)
  nlinarith only [hn, hz, hlog, hp]

theorem eulerTerm_successor (f : Nat -> Complex) (s : Complex) (n : Nat)
    (hn : Not (n = 0)) :
    LSeries.term f (s + 1) n = LSeries.term f s n / (n : Complex) := by
  have hnC : Not ((n : Complex) = 0) := by exact_mod_cast hn
  rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn,
    Complex.cpow_add s 1 hnC, Complex.cpow_one, div_div]

theorem xiEulerBound_as_norm_tsum (a : Real) (ha : 1 < a) :
    xiEulerBound a = tsum (fun n : Nat => norm (LSeries.term
      (fun n : Nat => (ArithmeticFunction.vonMangoldt n : Complex)) (a : Complex) n)) := by
  let f : Nat -> Complex := fun n => (ArithmeticFunction.vonMangoldt n : Complex)
  have hs : LSeriesSummable f (a : Complex) :=
    ArithmeticFunction.LSeriesSummable_vonMangoldt (by simpa only [Complex.ofReal_re] using ha)
  have hp (n : Nat) : 0 <= LSeries.term f (a : Complex) n := by
    apply LSeries.term_nonneg
    change (0 : Complex) <= (ArithmeticFunction.vonMangoldt n : Complex)
    exact_mod_cast (show (0 : Real) <= ArithmeticFunction.vonMangoldt n from
      ArithmeticFunction.vonMangoldt_nonneg)
  have ht : 0 <= tsum (LSeries.term f (a : Complex)) := tsum_nonneg hp
  have he : xiEulerBound a = norm (LSeries f (a : Complex)) := by
    rw [ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div (by simpa using ha)]
    simp [xiEulerBound, zetaEulerLogDeriv, neg_div, norm_neg]
  rw [he]
  calc
    _ = (tsum (LSeries.term f (a : Complex))).re := (Complex.re_eq_norm.mpr ht).symm
    _ = tsum (fun n : Nat => (LSeries.term f (a : Complex) n).re) := Complex.re_tsum hs
    _ = _ := tsum_congr (fun n => Complex.re_eq_norm.mpr (hp n))

set_option maxHeartbeats 800000 in
theorem zetaEulerLogDeriv_compensated_bound (s : Complex) (lam : Real)
    (hs : 1 < s.re) (hl0 : 0 <= lam) (hl1 : lam <= 1) :
    norm (zetaEulerLogDeriv s - (lam : Complex) * zetaEulerLogDeriv (s + 1)) <=
      xiEulerBound s.re := by
  let f : Nat -> Complex := fun n => (ArithmeticFunction.vonMangoldt n : Complex)
  have hb : 1 < (s + 1).re := by simp only [Complex.add_re, Complex.one_re]; linarith only [hs]
  have hsa : LSeriesSummable f s := ArithmeticFunction.LSeriesSummable_vonMangoldt hs
  have hsb : LSeriesSummable f (s + 1) := ArithmeticFunction.LSeriesSummable_vonMangoldt hb
  have hsr : LSeriesSummable f (s.re : Complex) :=
    ArithmeticFunction.LSeriesSummable_vonMangoldt (by simpa only [Complex.ofReal_re] using hs)
  have hd : Summable (fun n : Nat => LSeries.term f s n -
      (lam : Complex) * LSeries.term f (s + 1) n) := hsa.sub (hsb.mul_left (lam : Complex))
  have hpoint (n : Nat) : norm (LSeries.term f s n -
      (lam : Complex) * LSeries.term f (s + 1) n) <=
      norm (LSeries.term f (s.re : Complex) n) := by
    by_cases hn : n = 0
    next => subst n; simp only [LSeries.term_zero, mul_zero, sub_self, norm_zero, le_refl]
    next =>
      have hn1 : (1 : Real) <= (n : Real) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
      have hn0 : 0 < (n : Real) := by linarith only [hn1]
      have hnC : Not ((n : Complex) = 0) := by exact_mod_cast hn
      have hd0 : 0 <= lam / (n : Real) := div_nonneg hl0 hn0.le
      have hd1 : lam / (n : Real) <= 1 := by
        calc
          _ <= 1 / (n : Real) := div_le_div_of_nonneg_right hl1 hn0.le
          _ <= 1 := by simpa only [div_one] using one_div_le_one_div_of_le (by norm_num : (0 : Real) < 1) hn1
      have hw0 : 0 <= 1 - lam / (n : Real) := sub_nonneg.mpr hd1
      have hw1 : 1 - lam / (n : Real) <= 1 := by linarith only [hd0]
      have he : LSeries.term f s n - (lam : Complex) * LSeries.term f (s + 1) n =
          ((1 - lam / (n : Real) : Real) : Complex) * LSeries.term f s n := by
        rw [eulerTerm_successor f s n hn]
        push_cast
        field_simp [hnC]
      have hnorm : norm (LSeries.term f s n) = norm (LSeries.term f (s.re : Complex) n) := by
        simp only [LSeries.norm_term_eq, Complex.ofReal_re]
      rw [he, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hw0, <- hnorm]
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hw1 (norm_nonneg (LSeries.term f s n))
  have hLa : LSeries f s = -zetaEulerLogDeriv s := by
    simpa only [zetaEulerLogDeriv, neg_div] using
      ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs
  have hLb : LSeries f (s + 1) = -zetaEulerLogDeriv (s + 1) := by
    simpa only [zetaEulerLogDeriv, neg_div] using
      ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hb
  have he : LSeries f s - (lam : Complex) * LSeries f (s + 1) =
      tsum (fun n : Nat => LSeries.term f s n - (lam : Complex) * LSeries.term f (s + 1) n) := by
    unfold LSeries
    rw [hsa.tsum_sub (hsb.mul_left (lam : Complex)), tsum_mul_left]
  have hsign : norm (zetaEulerLogDeriv s - (lam : Complex) * zetaEulerLogDeriv (s + 1)) =
      norm (LSeries f s - (lam : Complex) * LSeries f (s + 1)) := by
    rw [hLa, hLb]
    have hn : -zetaEulerLogDeriv s - (lam : Complex) * -zetaEulerLogDeriv (s + 1) =
        -(zetaEulerLogDeriv s - (lam : Complex) * zetaEulerLogDeriv (s + 1)) := by ring
    rw [hn, norm_neg]
  rw [hsign, he, xiEulerBound_as_norm_tsum s.re hs]
  exact (norm_tsum_le_tsum_norm hd.norm).trans (hd.norm.tsum_le_tsum hpoint hsr.norm)

end PrimeFactorOscillations

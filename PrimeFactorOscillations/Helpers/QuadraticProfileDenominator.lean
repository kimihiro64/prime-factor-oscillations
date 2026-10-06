/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.QuadraticProfileSeries
import PrimeFactorOscillations.Mathlib.Analysis.Analytic.FactorialSeries

/-!
# Positive normalized prime-profile coefficients

The actual entire scalar series and uniform factorial approximation give a
single positive lower bound on every fixed compact nonnegative interval once
the rank is large enough.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.QuadraticPrimeLaw

theorem abs_profile_secondMoment_le (law : QuadraticPrimeLaw) (b t : Real)
    (hb : 0 <= b) (ht : 0 <= t) (htb : t <= b) :
    abs (tsum (fun j : Nat => law.realCoefficient j * t ^ j *
      ((j : Real) * (j - 1)))) <=
        tsum (fun j : Nat => (j : Real) ^ 2 * abs (law.realCoefficient j) * b ^ j) := by
  let bn : NNReal := { val := b, property := hb }
  have hrad : (bn : ENNReal) <
      (FormalMultilinearSeries.ofScalars Real law.realCoefficient).radius := by
    simp only [law.realCoefficient_radius_eq_top, ENNReal.coe_lt_top]
  have hs : Summable (fun j : Nat => (j : Real) ^ 2 *
      abs (law.realCoefficient j) * b ^ j) :=
    FormalMultilinearSeries.summable_nat_pow_mul_abs_of_lt_radius
      law.realCoefficient bn hrad 2
  have hmajor : forall j : Nat,
      norm (law.realCoefficient j * t ^ j * ((j : Real) * (j - 1))) <=
        (j : Real) ^ 2 * abs (law.realCoefficient j) * b ^ j := by
    intro j
    have hj : abs ((j : Real) * (j - 1)) <= (j : Real) ^ 2 := by
      cases j with
      | zero => simp
      | succ j =>
        simp only [Nat.cast_succ, add_sub_cancel_right]
        rw [abs_of_nonneg (by positivity)]
        nlinarith [sq_nonneg (j : Real)]
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (pow_nonneg ht j)]
    calc
      abs (law.realCoefficient j) * t ^ j *
          abs ((j : Real) * (j - 1)) <=
          abs (law.realCoefficient j) * b ^ j * (j : Real) ^ 2 := by
        gcongr
      _ = (j : Real) ^ 2 * abs (law.realCoefficient j) * b ^ j := by ring
  simpa only [Real.norm_eq_abs] using tsum_of_norm_bounded hs.hasSum hmajor

theorem exists_profile_normalized_coefficient_lower_bound (law : QuadraticPrimeLaw)
    (b : Real) (hb : 0 <= b) :
    exists r0 : Nat, 0 < r0 /\ forall (r : Nat), r0 <= r ->
      forall (t : Real), 0 <= t -> t <= b ->
        law.positiveLowerBound b / 2 <=
            (Finset.range (r + 1)).sum (fun j =>
              law.realCoefficient j * t ^ j *
                ((r.descFactorial j : Real) / (r : Real) ^ j)) := by
  let bn : NNReal := { val := b, property := hb }
  have hrad : (bn : ENNReal) <
      (FormalMultilinearSeries.ofScalars Real law.realCoefficient).radius := by
    simp only [law.realCoefficient_radius_eq_top, ENNReal.coe_lt_top]
  obtain h := Nat.descFactorial_coefficient_uniform_error_of_radius
    law.realCoefficient bn hrad
  choose C hC herror using h
  let J := tsum (fun j : Nat => (j : Real) ^ 2 *
    abs (law.realCoefficient j) * b ^ j)
  have hJ : 0 <= J := tsum_nonneg (fun j => by positivity)
  let m := law.positiveLowerBound b
  have hm : 0 < m := Real.exp_pos _
  choose r0 hr0 using exists_nat_gt ((2 * C + J) / m)
  refine Exists.intro (r0 + 1) (And.intro (Nat.zero_lt_succ r0) ?_)
  intro r hr t ht htb
  have hrpos : 0 < r := (Nat.zero_lt_succ r0).trans_le hr
  have hrR : (0 : Real) < r := by exact_mod_cast hrpos
  have hr1 : (1 : Real) <= r := by exact_mod_cast hrpos
  have hr0R : (r0 : Real) <= r := by exact_mod_cast (Nat.le_succ r0).trans hr
  have hallow : 2 * C + J <= m * r := by
    have hc := mul_lt_mul_of_pos_right hr0 hm
    have hcancel : (2 * C + J) / m * m = 2 * C + J := by
      field_simp
    rw [hcancel] at hc
    nlinarith
  let tn : NNReal := { val := t, property := ht }
  have htn : tn <= bn := htb
  have he := herror r hrpos tn htn
  have hsum := (law.hasSum_realCoefficient t).tsum_eq
  have hmom := law.abs_profile_secondMoment_le b t hb ht htb
  have hprofile := law.complexProfile_re_lower_bound b t hb ht htb
  change m <= (law.complexProfile (t : Complex)).re at hprofile
  have hsmall : C / (r : Real) ^ 2 <= C / r := by
    apply div_le_div_of_nonneg_left hC hrR
    nlinarith
  have hmargin : C / (r : Real) + J / (2 * r) <= m / 2 := by
    have hc : C / (r : Real) * r = C := by field_simp
    have hj : J / (2 * (r : Real)) * (2 * r) = J := by field_simp
    apply le_of_mul_le_mul_right ?_ hrR
    nlinarith
  have hmom' : (tsum (fun j : Nat => law.realCoefficient j * t ^ j *
      ((j : Real) * (j - 1)))) / (2 * r) <= J / (2 * r) := by
    apply div_le_div_of_nonneg_right ((le_abs_self _).trans hmom)
    positivity
  change abs ((Finset.range (r + 1)).sum (fun j =>
      law.realCoefficient j * t ^ j *
        ((r.descFactorial j : Real) / (r : Real) ^ j)) -
      tsum (fun j : Nat => law.realCoefficient j * t ^ j) +
      (tsum (fun j : Nat => law.realCoefficient j * t ^ j *
        ((j : Real) * (j - 1)))) / (2 * r)) <= C / (r : Real) ^ 2 at he
  rw [hsum] at he
  have helow := (abs_le.mp he).1
  change m / 2 <= _
  linarith

end PrimeFactorOscillations.QuadraticPrimeLaw

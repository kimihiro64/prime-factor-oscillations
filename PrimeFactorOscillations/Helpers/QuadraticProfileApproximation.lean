/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.QuadraticProfileDenominator
import PrimeFactorOscillations.Mathlib.Analysis.Analytic.FactorialCoefficientBound
import PrimeFactorOscillations.Mathlib.Analysis.Analytic.FactorialPolynomial

/-!
# Uniform finite-prefix coefficient errors

The actual Taylor error and geometric factorial weights control both the
normalized finite coefficient sum and its first-derivative sum, with constants
independent of the rank and the prime cutoff.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.QuadraticPrimeLaw

open BombieriVinogradov.ComplexAnalysis

theorem exists_prefixProfile_normalized_errors (law : QuadraticPrimeLaw) (b : Real) (hb : 0 <= b) :
    exists C D : Real, 0 <= C /\ 0 <= D /\
      forall N : Nat, 1 <= N -> forall r : Nat, 0 < r ->
      forall t : Real, 0 <= t -> t <= b ->
        norm ((Finset.range (r + 1)).sum (fun j =>
          (taylorCoefficient (law.complexPrefix N) 0 j -
            taylorCoefficient law.complexProfile 0 j) * (t : Complex) ^ j *
              ((r.descFactorial j : Complex) / (r : Complex) ^ j))) <= C / (N : Real) /\
        norm ((Finset.range (r + 1)).sum (fun j => (j : Complex) *
          (taylorCoefficient (law.complexPrefix N) 0 j -
            taylorCoefficient law.complexProfile 0 j) * (t : Complex) ^ (j - 1) *
              ((r.descFactorial j : Complex) / (r : Complex) ^ j))) <= D / (N : Real) := by
  let R := b + 1
  have hR : 0 < R := by dsimp [R]; linarith
  have hbR : b < R := by dsimp [R]; linarith
  have hden : 0 < 1 - b / R := sub_pos.mpr ((div_lt_one hR).mpr hbR)
  obtain h := law.exists_prefixProfile_taylor_error R hR
  choose A hA using h
  refine Exists.intro (A / (1 - b / R))
    (Exists.intro (A / (R * (1 - b / R) ^ 2)) ?_)
  refine And.intro (div_nonneg hA.1 hden.le)
    (And.intro (div_nonneg hA.1 (by positivity)) ?_)
  intro N hN r hr t ht htb
  let c : Nat -> Complex := fun j =>
    taylorCoefficient (law.complexPrefix N) 0 j - taylorCoefficient law.complexProfile 0 j
  have hc : forall j, norm (c j) <= (A / (N : Real)) / R ^ j := by
    intro j
    simpa only [div_div] using hA.2 N hN j
  have hAN : 0 <= A / (N : Real) := div_nonneg hA.1 (Nat.cast_nonneg N)
  have hv := Nat.norm_descFactorial_coefficient_le_geometric r hr c
    (A / (N : Real)) b R t hAN ht htb hbR hc
  have hd := Nat.norm_descFactorial_coefficient_deriv_le_geometric r hr c
    (A / (N : Real)) b R t hAN ht htb hbR hc
  have hvEq : (A / (N : Real)) / (1 - b / R) =
      (A / (1 - b / R)) / (N : Real) := by ring
  have hdEq : (A / (N : Real)) / (R * (1 - b / R) ^ 2) =
      (A / (R * (1 - b / R) ^ 2)) / (N : Real) := by ring
  rw [hvEq] at hv
  rw [hdEq] at hd
  exact And.intro hv hd

theorem exists_prefixProfile_real_normalized_errors (law : QuadraticPrimeLaw) (b : Real) (hb : 0 <= b) :
    exists C D : Real, 0 <= C /\ 0 <= D /\
      forall N : Nat, 1 <= N -> forall r : Nat, 0 < r ->
      forall t : Real, 0 <= t -> t <= b ->
        abs (Nat.normalizedDescFactorialPolynomial
          (fun j => (taylorCoefficient (law.complexPrefix N) 0 j).re) r t -
            Nat.normalizedDescFactorialPolynomial law.realCoefficient r t) <=
              C / (N : Real) /\
        abs (deriv (Nat.normalizedDescFactorialPolynomial
          (fun j => (taylorCoefficient (law.complexPrefix N) 0 j).re) r) t -
            deriv (Nat.normalizedDescFactorialPolynomial law.realCoefficient r) t) <=
              D / (N : Real) := by
  obtain h := law.exists_prefixProfile_normalized_errors b hb
  choose C D hC hD hbound using h
  refine Exists.intro C (Exists.intro D (And.intro hC (And.intro hD ?_)))
  intro N hN r hr t ht htb
  have hc := hbound N hN r hr t ht htb
  let c : Nat -> Complex := fun j =>
    taylorCoefficient (law.complexPrefix N) 0 j - taylorCoefficient law.complexProfile 0 j
  have hreal (w : Complex) (m j : Nat) :
      (w * (t : Complex) ^ m *
        ((r.descFactorial j : Complex) / (r : Complex) ^ j)).re =
          w.re * t ^ m * ((r.descFactorial j : Real) / (r : Real) ^ j) := by
    have hw : ((r.descFactorial j : Complex) / (r : Complex) ^ j) =
        Complex.ofReal ((r.descFactorial j : Real) / (r : Real) ^ j) := by
      simp only [Complex.ofReal_div, Complex.ofReal_pow, Complex.ofReal_natCast]
    rw [hw, <- Complex.ofReal_pow]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  have hv : ((Finset.range (r + 1)).sum (fun j => c j * (t : Complex) ^ j *
      ((r.descFactorial j : Complex) / (r : Complex) ^ j))).re =
        Nat.normalizedDescFactorialPolynomial
          (fun j => (taylorCoefficient (law.complexPrefix N) 0 j).re) r t -
          Nat.normalizedDescFactorialPolynomial law.realCoefficient r t := by
    unfold Nat.normalizedDescFactorialPolynomial
    rw [Complex.re_sum, <- Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    rw [hreal]
    simp only [c, Complex.sub_re, realCoefficient]
    ring
  have hd : ((Finset.range (r + 1)).sum (fun j => (j : Complex) * c j *
      (t : Complex) ^ (j - 1) *
        ((r.descFactorial j : Complex) / (r : Complex) ^ j))).re =
        deriv (Nat.normalizedDescFactorialPolynomial
          (fun j => (taylorCoefficient (law.complexPrefix N) 0 j).re) r) t -
          deriv (Nat.normalizedDescFactorialPolynomial law.realCoefficient r) t := by
    rw [Nat.deriv_normalizedDescFactorialPolynomial,
      Nat.deriv_normalizedDescFactorialPolynomial,
      Complex.re_sum, <- Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    rw [hreal]
    simp only [c, Complex.mul_re, Complex.natCast_re, Complex.natCast_im,
      Complex.sub_re, realCoefficient, zero_mul, sub_zero]
    ring
  have hvBound := (Complex.abs_re_le_norm
    ((Finset.range (r + 1)).sum (fun j => c j * (t : Complex) ^ j *
      ((r.descFactorial j : Complex) / (r : Complex) ^ j)))).trans hc.1
  have hdBound := (Complex.abs_re_le_norm
    ((Finset.range (r + 1)).sum (fun j => (j : Complex) * c j *
      (t : Complex) ^ (j - 1) *
        ((r.descFactorial j : Complex) / (r : Complex) ^ j)))).trans hc.2
  rw [hv] at hvBound
  rw [hd] at hdBound
  exact And.intro hvBound hdBound


end PrimeFactorOscillations.QuadraticPrimeLaw

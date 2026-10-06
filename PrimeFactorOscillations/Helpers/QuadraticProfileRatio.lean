/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.QuadraticProfileApproximation
import PrimeFactorOscillations.Helpers.QuadraticProfileDerivative

/-!
# Uniform finite-prefix ratio comparison

Actual coefficient and derivative errors, positive denominators, and the exact
ratio identity give a uniform inverse-rank improvement after cancellation.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.QuadraticPrimeLaw

open BombieriVinogradov.ComplexAnalysis

theorem exists_prefixProfile_factorialConvolution_ratio_error (law : QuadraticPrimeLaw)
    (b : Real) (hb : 0 <= b) :
    exists r0 N0 : Nat, exists K : Real,
      0 < r0 /\ 1 <= N0 /\ 0 <= K /\
      forall r : Nat, r0 <= r -> forall N : Nat, N0 <= N ->
      forall u : Real, 0 < u -> (r : Real) / u <= b ->
        0 < Nat.factorialConvolution
          (fun j => (taylorCoefficient (law.complexPrefix N) 0 j).re) r u /\
        0 < Nat.factorialConvolution law.realCoefficient r u /\
        abs (Nat.factorialConvolution
            (fun j => (taylorCoefficient (law.complexPrefix N) 0 j).re) (r - 1) u /
          Nat.factorialConvolution
            (fun j => (taylorCoefficient (law.complexPrefix N) 0 j).re) r u -
          Nat.factorialConvolution law.realCoefficient (r - 1) u /
            Nat.factorialConvolution law.realCoefficient r u) <=
          K / ((r : Real) * (N : Real)) := by
  obtain he := law.exists_prefixProfile_real_normalized_errors b hb
  choose C D hC hD herror using he
  obtain hd := law.exists_profile_normalized_derivative_bounds b hb
  choose M hM hderiv using hd
  obtain hl := law.exists_profile_normalized_coefficient_lower_bound b hb
  choose r0 hr0 hlower using hl
  let m := law.positiveLowerBound b
  let d := m / 4
  have hm : 0 < m := Real.exp_pos _
  have hd : 0 < d := by dsimp [d]; positivity
  let Q := D / d + M * C / (d * d)
  have hQ : 0 <= Q := by dsimp [Q]; positivity
  choose n0 hn0 using exists_nat_gt (C / d)
  refine Exists.intro r0 (Exists.intro (n0 + 1) (Exists.intro (b ^ 2 * Q)
    (And.intro hr0 (And.intro (Nat.succ_le_succ (Nat.zero_le n0))
      (And.intro (mul_nonneg (sq_nonneg b) hQ) ?_)))))
  intro r hr N hN u hu htb
  have hrpos : 0 < r := hr0.trans_le hr
  have hrR : (0 : Real) < r := by exact_mod_cast hrpos
  have hNpos : 0 < N := (Nat.zero_lt_succ n0).trans_le hN
  have hNR : (0 : Real) < N := by exact_mod_cast hNpos
  have hN1 : 1 <= N := hNpos
  let t := (r : Real) / u
  have ht : 0 <= t := (div_pos hrR hu).le
  have htbound : t <= b := htb
  let cN : Nat -> Real := fun j => (taylorCoefficient (law.complexPrefix N) 0 j).re
  let A := Nat.normalizedDescFactorialPolynomial law.realCoefficient r t
  let AN := Nat.normalizedDescFactorialPolynomial cN r t
  let V := deriv (Nat.normalizedDescFactorialPolynomial law.realCoefficient r) t
  let VN := deriv (Nat.normalizedDescFactorialPolynomial cN r) t
  have herror' := herror N hN1 r hrpos t ht htbound
  change abs (AN - A) <= C / (N : Real) /\
    abs (VN - V) <= D / (N : Real) at herror'
  have hV : abs V <= M := (hderiv r hrpos t ht htbound).1
  have hA : m / 2 <= A := hlower r hr t ht htbound
  have hnN : (n0 : Real) < N := by
    exact_mod_cast (Nat.lt_succ_self n0).trans_le hN
  have hsmall : C / (N : Real) <= d := by
    have hc := mul_lt_mul_of_pos_right (hn0.trans hnN) hd
    have hcancel : C / d * d = C := by field_simp
    rw [hcancel] at hc
    apply le_of_mul_le_mul_right ?_ hNR
    have hcancelN : C / (N : Real) * N = C := by field_simp
    rw [hcancelN]
    nlinarith
  have hdA : d <= A := by dsimp [d]; linarith
  have hdAN : d <= AN := by
    have herr := (abs_le.mp herror'.1).1
    change m / 4 <= AN
    change C / (N : Real) <= m / 4 at hsmall
    linarith
  have hApos : 0 < A := hd.trans_le hdA
  have hANpos : 0 < AN := hd.trans_le hdAN
  have hquot : abs (VN / AN - V / A) <= Q / (N : Real) := by
    have hid : VN / AN - V / A =
        (VN - V) / AN + V * (A - AN) / (AN * A) := by
      field_simp [hANpos.ne', hApos.ne']
      ring
    have hprod : d * d <= AN * A := mul_le_mul hdAN hdA hd.le hANpos.le
    have hfirst : abs ((VN - V) / AN) <= (D / (N : Real)) / d := by
      rw [abs_div, abs_of_pos hANpos]
      exact (div_le_div_of_nonneg_right herror'.2 hANpos.le).trans
        (div_le_div_of_nonneg_left (div_nonneg hD hNR.le) hd hdAN)
    have hsecond : abs (V * (A - AN) / (AN * A)) <=
        (M * (C / (N : Real))) / (d * d) := by
      rw [abs_div, abs_mul, abs_sub_comm A AN, abs_of_pos (mul_pos hANpos hApos)]
      have hnum : abs V * abs (AN - A) <= M * (C / (N : Real)) :=
        mul_le_mul hV herror'.1 (abs_nonneg _) hM
      exact (div_le_div_of_nonneg_right hnum (mul_nonneg hANpos.le hApos.le)).trans
        (div_le_div_of_nonneg_left (by positivity) (mul_pos hd hd) hprod)
    calc
      abs (VN / AN - V / A) <=
          abs ((VN - V) / AN) + abs (V * (A - AN) / (AN * A)) := by
        rw [hid]
        exact abs_add_le _ _
      _ <= (D / (N : Real)) / d + (M * (C / (N : Real))) / (d * d) :=
        add_le_add hfirst hsecond
      _ = Q / (N : Real) := by dsimp [Q]; ring
  have hfront : 0 < u ^ r / (r.factorial : Real) := by positivity
  have hfinitePos : 0 < Nat.factorialConvolution cN r u := by
    rw [Nat.factorialConvolution_eq_normalizedDescFactorialPolynomial cN r hrpos u hu.ne']
    exact mul_pos hfront hANpos
  have hinfinitePos : 0 < Nat.factorialConvolution law.realCoefficient r u := by
    rw [Nat.factorialConvolution_eq_normalizedDescFactorialPolynomial
      law.realCoefficient r hrpos u hu.ne']
    exact mul_pos hfront hApos
  refine And.intro hfinitePos (And.intro hinfinitePos ?_)
  rw [Nat.factorialConvolution_ratio_eq_normalized_logDeriv cN r hrpos u hu.ne' hANpos.ne',
    Nat.factorialConvolution_ratio_eq_normalized_logDeriv
      law.realCoefficient r hrpos u hu.ne' hApos.ne']
  change abs ((t - (t ^ 2 / r) * VN / AN) - (t - (t ^ 2 / r) * V / A)) <=
    b ^ 2 * Q / ((r : Real) * (N : Real))
  have hid : (t - (t ^ 2 / r) * VN / AN) - (t - (t ^ 2 / r) * V / A) =
      -(t ^ 2 / r) * (VN / AN - V / A) := by ring
  rw [hid, abs_mul, abs_neg, abs_of_nonneg (div_nonneg (sq_nonneg t) hrR.le)]
  calc
    t ^ 2 / (r : Real) * abs (VN / AN - V / A) <=
        b ^ 2 / (r : Real) * (Q / (N : Real)) := by
      apply mul_le_mul _ hquot (abs_nonneg _) (by positivity)
      apply div_le_div_of_nonneg_right _ hrR.le
      nlinarith
    _ = b ^ 2 * Q / ((r : Real) * (N : Real)) := by ring

end PrimeFactorOscillations.QuadraticPrimeLaw

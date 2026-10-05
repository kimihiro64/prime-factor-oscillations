/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Finite factorial convolutions and normalized polynomials

Exact scaling and differentiation identify adjacent-coefficient ratios with
the logarithmic derivative of one normalized polynomial. Every division
retains its nonzero hypotheses.
-/

set_option autoImplicit false
set_option Elab.async false

namespace Nat

noncomputable def factorialConvolution (c : Nat -> Real) (r : Nat) (u : Real) : Real :=
  (Finset.range (r + 1)).sum (fun j => c j * u ^ (r - j) / (r - j).factorial)

noncomputable def normalizedDescFactorialPolynomial
    (c : Nat -> Real) (r : Nat) (t : Real) : Real :=
  (Finset.range (r + 1)).sum (fun j =>
    c j * t ^ j * ((r.descFactorial j : Real) / (r : Real) ^ j))

theorem factorialConvolution_eq_normalizedDescFactorialPolynomial
    (c : Nat -> Real) (r : Nat) (hr : 0 < r) (u : Real) (hu : Not (u = 0)) :
    factorialConvolution c r u =
      u ^ r / r.factorial * normalizedDescFactorialPolynomial c r ((r : Real) / u) := by
  have hr0 : Not ((r : Real) = 0) := by exact_mod_cast Nat.ne_of_gt hr
  unfold factorialConvolution normalizedDescFactorialPolynomial
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hjr : j <= r := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  have hf : ((r - j).factorial : Real) * (r.descFactorial j : Real) = r.factorial := by
    exact_mod_cast factorial_mul_descFactorial hjr
  have hf0 : Not (((r - j).factorial : Real) = 0) := by positivity
  have hdesc : (r.descFactorial j : Real) =
      (r.factorial : Real) / (r - j).factorial := by
    apply (eq_div_iff hf0).mpr
    simpa only [mul_comm] using hf
  have hpow : u ^ (r - j) * u ^ j = u ^ r := by
    rw [<- pow_add, Nat.sub_add_cancel hjr]
  rw [hdesc, div_pow]
  field_simp
  rw [<- hpow]
  ring

private theorem hasDerivAt_factorialMonomial_succ (a u : Real) (n : Nat) :
    HasDerivAt (fun v : Real => a * v ^ (n + 1) / (n + 1).factorial)
      (a * u ^ n / n.factorial) u := by
  convert ((hasDerivAt_pow (n + 1) u).const_mul a).div_const
    ((n + 1).factorial : Real) using 1
  simp only [Nat.add_sub_cancel, factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  field_simp

theorem hasDerivAt_factorialConvolution_succ (c : Nat -> Real) (r : Nat) (u : Real) :
    HasDerivAt (factorialConvolution c (r + 1)) (factorialConvolution c r u) u := by
  have heq : factorialConvolution c (r + 1) =
      fun v : Real => (Finset.range (r + 1)).sum
        (fun j => c j * v ^ (r + 1 - j) / (r + 1 - j).factorial) + c (r + 1) := by
    funext v
    unfold factorialConvolution
    rw [Finset.sum_range_succ]
    simp
  rw [heq]
  unfold factorialConvolution
  apply HasDerivAt.add_const
  apply HasDerivAt.fun_sum
  intro j hj
  have hjr : j <= r := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  have hsub : r + 1 - j = (r - j) + 1 := by omega
  rw [hsub]
  exact hasDerivAt_factorialMonomial_succ (c j) u (r - j)

theorem deriv_factorialConvolution (c : Nat -> Real) (r : Nat) (hr : 0 < r) :
    deriv (factorialConvolution c r) = factorialConvolution c (r - 1) := by
  have hrEq : r = (r - 1) + 1 := by omega
  funext u
  conv_lhs => rw [hrEq]
  exact (hasDerivAt_factorialConvolution_succ c (r - 1) u).deriv

theorem hasDerivAt_normalizedDescFactorialPolynomial
    (c : Nat -> Real) (r : Nat) (t : Real) :
    HasDerivAt (normalizedDescFactorialPolynomial c r)
      ((Finset.range (r + 1)).sum (fun j =>
        (j : Real) * c j * t ^ (j - 1) *
          ((r.descFactorial j : Real) / (r : Real) ^ j))) t := by
  unfold normalizedDescFactorialPolynomial
  apply HasDerivAt.fun_sum
  intro j _
  convert ((hasDerivAt_pow j t).const_mul (c j)).mul_const
    ((r.descFactorial j : Real) / (r : Real) ^ j) using 1
  ring

theorem deriv_normalizedDescFactorialPolynomial (c : Nat -> Real) (r : Nat) (t : Real) :
    deriv (normalizedDescFactorialPolynomial c r) t =
      (Finset.range (r + 1)).sum (fun j =>
        (j : Real) * c j * t ^ (j - 1) *
          ((r.descFactorial j : Real) / (r : Real) ^ j)) :=
  (hasDerivAt_normalizedDescFactorialPolynomial c r t).deriv

theorem factorialConvolution_ne_zero_iff
    (c : Nat -> Real) (r : Nat) (hr : 0 < r) (u : Real) (hu : Not (u = 0)) :
    Not (factorialConvolution c r u = 0) <->
      Not (normalizedDescFactorialPolynomial c r ((r : Real) / u) = 0) := by
  have hf0 : Not ((r.factorial : Real) = 0) := by positivity
  have hpref : Not (u ^ r / (r.factorial : Real) = 0) :=
    div_ne_zero (pow_ne_zero r hu) hf0
  rw [factorialConvolution_eq_normalizedDescFactorialPolynomial c r hr u hu]
  simp only [_root_.mul_eq_zero, hpref, false_or]

theorem factorialConvolution_ratio_eq_normalized_logDeriv
    (c : Nat -> Real) (r : Nat) (hr : 0 < r) (u : Real) (hu : Not (u = 0))
    (hA : Not (normalizedDescFactorialPolynomial c r ((r : Real) / u) = 0)) :
    factorialConvolution c (r - 1) u / factorialConvolution c r u =
      (r : Real) / u - (((r : Real) / u) ^ 2 / r) *
        deriv (normalizedDescFactorialPolynomial c r) ((r : Real) / u) /
          normalizedDescFactorialPolynomial c r ((r : Real) / u) := by
  have hr0 : Not ((r : Real) = 0) := by exact_mod_cast Nat.ne_of_gt hr
  have hf0 : Not ((r.factorial : Real) = 0) := by positivity
  have hInv : HasDerivAt (fun v : Real => (r : Real) / v) (-(r : Real) / u ^ 2) u := by
    simpa using (hasDerivAt_const u (r : Real)).fun_div (hasDerivAt_id u) hu
  have hAderiv :=
    (hasDerivAt_normalizedDescFactorialPolynomial c r ((r : Real) / u)).differentiableAt.hasDerivAt
  have hProduct := ((hasDerivAt_pow r u).div_const (r.factorial : Real)).mul
    (hAderiv.comp u hInv)
  have heq : Filter.EventuallyEq (nhds u) (factorialConvolution c r)
      (fun v : Real => v ^ r / r.factorial *
        normalizedDescFactorialPolynomial c r ((r : Real) / v)) := by
    apply (eventually_ne_nhds hu).mono
    intro v hv
    exact factorialConvolution_eq_normalizedDescFactorialPolynomial c r hr v hv
  have hd := (hProduct.congr_of_eventuallyEq heq).deriv
  rw [deriv_factorialConvolution c r hr] at hd
  simp only [Function.comp_apply] at hd
  rw [hd, factorialConvolution_eq_normalizedDescFactorialPolynomial c r hr u hu]
  have hpow : u ^ r = u ^ (r - 1) * u := by
    rw [<- pow_succ]
    congr 1
    omega
  rw [hpow]
  field_simp
  ring

theorem hasDerivAt_deriv_normalizedDescFactorialPolynomial
    (c : Nat -> Real) (r : Nat) (t : Real) :
    HasDerivAt (deriv (normalizedDescFactorialPolynomial c r))
      ((Finset.range (r + 1)).sum (fun j =>
        (j : Real) * ((j - 1 : Nat) : Real) * c j * t ^ (j - 2) *
          ((r.descFactorial j : Real) / (r : Real) ^ j))) t := by
  have heq : deriv (normalizedDescFactorialPolynomial c r) =
      fun v : Real => (Finset.range (r + 1)).sum (fun j =>
        (j : Real) * c j * v ^ (j - 1) *
          ((r.descFactorial j : Real) / (r : Real) ^ j)) := by
    funext v
    exact deriv_normalizedDescFactorialPolynomial c r v
  rw [heq]
  apply HasDerivAt.fun_sum
  intro j _
  convert ((hasDerivAt_pow (j - 1) t).const_mul ((j : Real) * c j)).mul_const
    ((r.descFactorial j : Real) / (r : Real) ^ j) using 1
  simp only [Nat.sub_sub]
  ring

theorem deriv_deriv_normalizedDescFactorialPolynomial
    (c : Nat -> Real) (r : Nat) (t : Real) :
    deriv (deriv (normalizedDescFactorialPolynomial c r)) t =
      (Finset.range (r + 1)).sum (fun j =>
        (j : Real) * ((j - 1 : Nat) : Real) * c j * t ^ (j - 2) *
          ((r.descFactorial j : Real) / (r : Real) ^ j)) :=
  (hasDerivAt_deriv_normalizedDescFactorialPolynomial c r t).deriv

end Nat


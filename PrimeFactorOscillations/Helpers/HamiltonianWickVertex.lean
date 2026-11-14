/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Lean.Elab.Tactic.Omega
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! # The actual analytic Wick vertex and its coefficients

The complex vertex function is differentiated through a polynomial
differential operator. Its coefficient recurrence is derived from that
operator, retaining all signs. The coefficient bound is uniform in the
degree and is used by the full Wick diagram estimate.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

def wickVertexOperator (p : Polynomial Complex) : Polynomial Complex :=
  p.derivative + p * (Polynomial.X - 1)

def wickVertexPolynomial : Nat -> Polynomial Complex
  | 0 => 1 + Polynomial.X
  | n + 1 => wickVertexOperator (wickVertexPolynomial n)

def wickVertexFunction (z : Complex) : Complex :=
  (1 + z) * Complex.exp (-z + z ^ 2 / 2)

def wickVertexJet (n : Nat) (z : Complex) : Complex :=
  (wickVertexPolynomial n).eval z * Complex.exp (-z + z ^ 2 / 2)

def wickVertexCoefficient (n : Nat) : Complex :=
  (wickVertexPolynomial n).eval 0 / (n.factorial : Complex)

theorem wickVertexJet_hasDerivAt (n : Nat) (z : Complex) :
    HasDerivAt (wickVertexJet n) (wickVertexJet (n + 1) z) z := by
  have hPow : HasDerivAt (fun w : Complex => w ^ 2) (2 * z) z := by
    convert (hasDerivAt_id z).fun_pow' 2 using 1 <;>
      norm_num [Finset.sum_range_succ, id_eq] <;> ring
  have hExponent : HasDerivAt (fun w : Complex => -w + w ^ 2 / 2) (z - 1) z := by
    convert ((hasDerivAt_id z).neg).fun_add (hPow.div_const 2) using 1
    all_goals first
    | rfl
    | (funext w; dsimp <;> ring)
    | (dsimp <;> ring)
    | ring
  have hExp := (Complex.hasDerivAt_exp (-z + z ^ 2 / 2)).comp z hExponent
  have hProduct := ((wickVertexPolynomial n).hasDerivAt z).fun_mul hExp
  unfold wickVertexJet
  change HasDerivAt
    (fun w : Complex => (wickVertexPolynomial n).eval w * Complex.exp (-w + w ^ 2 / 2))
    ((wickVertexOperator (wickVertexPolynomial n)).eval z * Complex.exp (-z + z ^ 2 / 2)) z
  convert hProduct using 1
  all_goals first
  | rfl
  | (funext w; dsimp <;> ring)
  | (simp only [wickVertexOperator, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_one, Function.comp_apply] <;> ring)

theorem wickVertexFunction_iteratedDeriv (n : Nat) :
    iteratedDeriv n wickVertexFunction = wickVertexJet n := by
  induction n with
  | zero =>
    funext z
    simp [iteratedDeriv_zero, wickVertexJet, wickVertexPolynomial, wickVertexFunction]
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext z
    exact (wickVertexJet_hasDerivAt n z).deriv

theorem wickVertexCoefficient_actual (n : Nat) :
    wickVertexCoefficient n =
      iteratedDeriv n wickVertexFunction 0 / (n.factorial : Complex) := by
  rw [wickVertexFunction_iteratedDeriv]
  simp [wickVertexCoefficient, wickVertexJet]

theorem wickVertexOperator_add (p q : Polynomial Complex) :
    wickVertexOperator (p + q) = wickVertexOperator p + wickVertexOperator q := by
  simp only [wickVertexOperator, Polynomial.derivative_add]
  ring

theorem wickVertexOperator_mul (p q : Polynomial Complex) :
    wickVertexOperator (p * q) =
      p * wickVertexOperator q + p.derivative * q := by
  simp only [wickVertexOperator, Polynomial.derivative_mul]
  ring

theorem wickVertexOperator_polynomial (n : Nat) :
    wickVertexOperator (wickVertexPolynomial n) = wickVertexPolynomial (n + 1) := rfl

theorem wickVertexPolynomial_ode (n : Nat) :
    (1 + Polynomial.X) * wickVertexPolynomial (n + 3) +
        Polynomial.C ((n : Complex) + 2) * wickVertexPolynomial (n + 2) =
      Polynomial.X ^ 2 * wickVertexPolynomial (n + 2) +
        Polynomial.C (2 * ((n : Complex) + 2)) * Polynomial.X * wickVertexPolynomial (n + 1) +
        Polynomial.C (((n : Complex) + 2) * ((n : Complex) + 1)) * wickVertexPolynomial n := by
  induction n with
  | zero =>
    norm_num [wickVertexPolynomial, wickVertexOperator, Polynomial.derivative_add,
      Polynomial.derivative_mul, Polynomial.derivative_sub, Polynomial.C_1, Polynomial.C_ofNat]
    <;> ring
  | succ n ih =>
    have h := congrArg wickVertexOperator ih
    simp only [pow_two, wickVertexOperator_add, wickVertexOperator_mul,
      wickVertexOperator_polynomial, Polynomial.derivative_add, Polynomial.derivative_mul,
      Polynomial.derivative_C, Polynomial.derivative_X, Polynomial.derivative_one,
      add_zero, zero_add, mul_zero, zero_mul, mul_one, one_mul] at h
    convert h using 1 <;>
      simp only [Nat.cast_add, Nat.cast_one, map_add, map_mul, map_natCast,
        Polynomial.C_1, Polynomial.C_ofNat] <;> ring

theorem wickVertexCoefficient_initial :
    And (wickVertexCoefficient 0 = 1)
      (And (wickVertexCoefficient 1 = 0) (wickVertexCoefficient 2 = 0)) := by
  norm_num [wickVertexCoefficient, wickVertexPolynomial, wickVertexOperator,
    Polynomial.derivative_add, Polynomial.derivative_mul, Polynomial.derivative_sub]

theorem wickVertexCoefficient_low :
    And (wickVertexCoefficient 3 = 1 / 3)
      (And (wickVertexCoefficient 4 = -(1 / 4))
        (And (wickVertexCoefficient 5 = 1 / 5) (wickVertexCoefficient 6 = -(1 / 9)))) := by
  norm_num [wickVertexCoefficient, wickVertexPolynomial, wickVertexOperator,
    Polynomial.derivative_add, Polynomial.derivative_mul, Polynomial.derivative_sub]

theorem wickVertexCoefficient_recurrence (n : Nat) :
    ((n : Complex) + 3) * wickVertexCoefficient (n + 3) =
      wickVertexCoefficient n - ((n : Complex) + 2) * wickVertexCoefficient (n + 2) := by
  have h := congrArg (fun p : Polynomial Complex => p.eval 0) (wickVertexPolynomial_ode n)
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_C, pow_two,
    zero_add, add_zero, mul_zero, zero_mul, one_mul] at h
  have hFactor : ((n + 3).factorial : Complex) =
      ((n : Complex) + 3) * (((n : Complex) + 2) *
        (((n : Complex) + 1) * (n.factorial : Complex))) := by
    simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    ring
  have hFactor2 : ((n + 2).factorial : Complex) =
      ((n : Complex) + 2) * (((n : Complex) + 1) * (n.factorial : Complex)) := by
    simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    ring
  have hF0 : Not ((n.factorial : Complex) = 0) := by exact_mod_cast Nat.factorial_ne_zero n
  have hF2 : Not (((n + 2).factorial : Complex) = 0) := by
    exact_mod_cast Nat.factorial_ne_zero (n + 2)
  have hF3 : Not (((n + 3).factorial : Complex) = 0) := by
    exact_mod_cast Nat.factorial_ne_zero (n + 3)
  have hP3 : (wickVertexPolynomial (n + 3)).eval 0 =
      (((n : Complex) + 2) * ((n : Complex) + 1)) * (wickVertexPolynomial n).eval 0 -
        ((n : Complex) + 2) * (wickVertexPolynomial (n + 2)).eval 0 :=
    eq_sub_of_add_eq h
  have hN1 : Not ((n : Complex) + 1 = 0) := by
    exact_mod_cast (show Not (n + 1 = 0) by omega)
  have hN2 : Not ((n : Complex) + 2 = 0) := by
    exact_mod_cast (show Not (n + 2 = 0) by omega)
  have hN3 : Not ((n : Complex) + 3 = 0) := by
    exact_mod_cast (show Not (n + 3 = 0) by omega)
  unfold wickVertexCoefficient
  rw [hP3, hFactor, hFactor2]
  field_simp [hF0, hN1, hN2, hN3]
  <;> ring


theorem wickVertexCoefficient_norm_le_one (n : Nat) :
    norm (wickVertexCoefficient n) <= 1 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => rw [wickVertexCoefficient_initial.1]; norm_num
    | succ n =>
      cases n with
      | zero => rw [wickVertexCoefficient_initial.2.1]; norm_num
      | succ n =>
        cases n with
        | zero => rw [wickVertexCoefficient_initial.2.2]; norm_num
        | succ n =>
          change norm (wickVertexCoefficient (n + 3)) <= 1
          have h0 : norm (wickVertexCoefficient n) <= 1 := ih n (by omega)
          have h2 : norm (wickVertexCoefficient (n + 2)) <= 1 := ih (n + 2) (by omega)
          have hNorm3 : norm ((n : Complex) + 3) = (n : Real) + 3 := by
            have hCast : (n : Complex) + 3 = ((n + 3 : Nat) : Complex) := by norm_num
            rw [hCast, Complex.norm_natCast]
            norm_num
          have hNorm2 : norm ((n : Complex) + 2) = (n : Real) + 2 := by
            have hCast : (n : Complex) + 2 = ((n + 2 : Nat) : Complex) := by norm_num
            rw [hCast, Complex.norm_natCast]
            norm_num
          have hScaled : ((n : Real) + 3) * norm (wickVertexCoefficient (n + 3)) <=
              norm (wickVertexCoefficient n) +
                ((n : Real) + 2) * norm (wickVertexCoefficient (n + 2)) := by
            calc
              _ = norm (((n : Complex) + 3) * wickVertexCoefficient (n + 3)) := by
                rw [norm_mul, hNorm3]
              _ = norm (wickVertexCoefficient n -
                  ((n : Complex) + 2) * wickVertexCoefficient (n + 2)) :=
                congrArg norm (wickVertexCoefficient_recurrence n)
              _ <= norm (wickVertexCoefficient n) +
                  norm (((n : Complex) + 2) * wickVertexCoefficient (n + 2)) :=
                norm_sub_le _ _
              _ = _ := by rw [norm_mul, hNorm2]
          have hSecond := mul_le_mul_of_nonneg_left h2
            (show (0 : Real) <= (n : Real) + 2 by positivity)
          have hBound : ((n : Real) + 3) * norm (wickVertexCoefficient (n + 3)) <=
              (n : Real) + 3 := by linarith only [hScaled, h0, hSecond]
          by_contra hNot
          have hGreater : 1 < norm (wickVertexCoefficient (n + 3)) := lt_of_not_ge hNot
          have hPositive := mul_nonneg (Nat.cast_nonneg n : (0 : Real) <= (n : Real))
            (le_of_lt (sub_pos.mpr hGreater))
          nlinarith only [hBound, hGreater, hPositive]

end PrimeFactorOscillations

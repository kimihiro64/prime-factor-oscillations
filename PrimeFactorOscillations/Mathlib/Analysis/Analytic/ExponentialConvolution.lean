/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Normalized derivatives of an exponential product

The Leibniz formula gives the exact finite convolution for an entire function
multiplied by an exponential. The statement includes rank zero and zero shift.
-/

set_option autoImplicit false
set_option Elab.async false

namespace Complex

theorem normalized_iteratedDeriv_mul_exp_zero
    (f : Complex -> Complex) (hf : Differentiable Complex f) (B : Complex) (r : Nat) :
    iteratedDeriv r (fun z => f z * exp (B * z)) 0 / (r.factorial : Complex) =
      (Finset.range (r + 1)).sum (fun j =>
        (iteratedDeriv j f 0 / (j.factorial : Complex)) *
          B ^ (r - j) / ((r - j).factorial : Complex)) := by
  have hexp : Differentiable Complex (fun z : Complex => exp (B * z)) :=
    differentiable_exp.comp ((differentiable_const B).mul differentiable_id)
  rw [iteratedDeriv_fun_mul hf.contDiff.contDiffAt hexp.contDiff.contDiffAt]
  simp only [iteratedDeriv_cexp_const_mul, mul_zero, exp_zero, mul_one]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j hj
  have hjr : j <= r := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  have hfactorial : (r.choose j : Complex) * (j.factorial : Complex) *
      ((r - j).factorial : Complex) = (r.factorial : Complex) := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hjr
  have hrf : Not ((r.factorial : Complex) = 0) := by exact_mod_cast Nat.factorial_ne_zero r
  have hjf : Not ((j.factorial : Complex) = 0) := by exact_mod_cast Nat.factorial_ne_zero j
  have hdif : Not (((r - j).factorial : Complex) = 0) := by
    exact_mod_cast Nat.factorial_ne_zero (r - j)
  field_simp
  rw [<- hfactorial]
  ring

end Complex


/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.NumberTheory.ArithmeticFunction.Defs
import Mathlib.Tactic.Ring

/-!
# Multiplicative twists of integer arithmetic functions

Shared extraction of the existing signed twist and its convolution identity.
The public namespace, hypotheses and proof body are preserved.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
open scoped BigOperators Classical

namespace PrimeFactorOscillations.DepletedMobius

def twist {R : Type*} [Ring R] (eta : Nat -> R)
    (f : ArithmeticFunction Int) : ArithmeticFunction R where
  toFun n := (f n : R) * eta n
  map_zero' := by simp

theorem twist_mul {R : Type*} [CommRing R] (eta : Nat -> R)
    (heta : forall m n : Nat, eta (m * n) = eta m * eta n)
    (f g : ArithmeticFunction Int) :
    twist eta (f * g) = twist eta f * twist eta g := by
  ext n
  change (((f * g) n : Int) : R) * eta n =
    (twist eta f * twist eta g) n
  rw [ArithmeticFunction.mul_apply, ArithmeticFunction.mul_apply,
    Int.cast_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro x hx
  have hn : x.1 * x.2 = n := (Nat.mem_divisorsAntidiagonal.mp hx).1
  change ((f x.1 * g x.2 : Int) : R) * eta n =
    ((f x.1 : R) * eta x.1) * ((g x.2 : R) * eta x.2)
  rw [Int.cast_mul, <- hn, heta]
  ring

end PrimeFactorOscillations.DepletedMobius

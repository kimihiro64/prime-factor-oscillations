/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Analysis.Complex.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Tactic.Ring

/-!
# Bounded complex weights on the higher prime powers

The complete nonnegative psi-minus-theta mass controls arbitrary complex
weights of norm at most one, with the same explicit square-root bound.
-/

set_option autoImplicit false
set_option Elab.async false

namespace Chebyshev

theorem norm_weighted_primePower_difference_le (f : Nat -> Complex)
    (X : Nat) (hX : 1 <= X)
    (hf : forall n, Membership.mem (Finset.Icc 1 X) n -> norm (f n) <= 1) :
    norm (Finset.sum (Finset.Icc 1 X)
        (fun n => (ArithmeticFunction.vonMangoldt n : Complex) * f n) -
      Finset.sum (Finset.Icc 1 X)
        (fun n => ((if Nat.Prime n then Real.log (n : Real) else 0 : Real) : Complex) * f n)) <=
      2 * Real.sqrt (X : Real) * Real.log (X : Real) := by
  let d : Nat -> Real := fun n =>
    ArithmeticFunction.vonMangoldt n - (if Nat.Prime n then Real.log (n : Real) else 0)
  have hd : forall n, 0 <= d n := by
    intro n
    by_cases hp : Nat.Prime n
    next => simp [d, hp, ArithmeticFunction.vonMangoldt_apply_prime hp]
    next => simp [d, hp, ArithmeticFunction.vonMangoldt_nonneg]
  have hId : Finset.sum (Finset.Icc 1 X)
        (fun n => (ArithmeticFunction.vonMangoldt n : Complex) * f n) -
      Finset.sum (Finset.Icc 1 X)
        (fun n => ((if Nat.Prime n then Real.log (n : Real) else 0 : Real) : Complex) * f n) =
      Finset.sum (Finset.Icc 1 X) (fun n => (d n : Complex) * f n) := by
    simp only [d, Complex.ofReal_sub, sub_mul, Finset.sum_sub_distrib]
  have hMass : Finset.sum (Finset.Icc 1 X) d =
      psi (X : Real) - theta (X : Real) := by
    unfold psi theta
    simp only [Nat.floor_natCast, Finset.sum_filter]
    have hset : Finset.Icc 1 X = Finset.Ioc 0 X := by
      ext n
      simp only [Finset.mem_Icc, Finset.mem_Ioc]
      omega
    rw [hset]
    simp only [d, Finset.sum_sub_distrib]
  rw [hId]
  calc
    _ <= Finset.sum (Finset.Icc 1 X) (fun n => norm ((d n : Complex) * f n)) :=
      norm_sum_le _ _
    _ <= Finset.sum (Finset.Icc 1 X) d := by
      apply Finset.sum_le_sum
      intro n hn
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hd n)]
      calc
        d n * norm (f n) <= d n * 1 := mul_le_mul_of_nonneg_left (hf n hn) (hd n)
        _ = d n := mul_one _
    _ = psi (X : Real) - theta (X : Real) := hMass
    _ <= _ := psi_sub_theta_le (by exact_mod_cast hX)

theorem norm_weighted_primeLog_sum_le (f : Nat -> Complex)
    (X : Nat) (hX : 1 <= X)
    (hf : forall n, Membership.mem (Finset.Icc 1 X) n -> norm (f n) <= 1) :
    norm (Finset.sum (Finset.Icc 1 X)
      (fun n => ((if Nat.Prime n then Real.log (n : Real) else 0 : Real) : Complex) * f n)) <=
      norm (Finset.sum (Finset.Icc 1 X)
        (fun n => (ArithmeticFunction.vonMangoldt n : Complex) * f n)) +
      2 * Real.sqrt (X : Real) * Real.log (X : Real) := by
  let P := Finset.sum (Finset.Icc 1 X)
    (fun n => (ArithmeticFunction.vonMangoldt n : Complex) * f n)
  let T := Finset.sum (Finset.Icc 1 X)
    (fun n => ((if Nat.Prime n then Real.log (n : Real) else 0 : Real) : Complex) * f n)
  change norm T <= norm P + _
  have hDiff := norm_weighted_primePower_difference_le f X hX hf
  calc
    norm T = norm (P - (P - T)) := by congr 1; ring
    _ <= norm P + norm (P - T) := norm_sub_le _ _
    _ <= _ := add_le_add le_rfl hDiff

end Chebyshev

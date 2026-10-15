/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import PrimeFactorOscillations.Helpers.QRHPrimePrefix
import PrimeFactorOscillations.Mathlib.NumberTheory.SmoothNumbers.LargestPrimeFactorPowerBounds

/-!
# Uniform character bounds for every largest-factor prime row

The constant is chosen before the modulus, character and all row parameters.
The available audited exclusion and 7/8 input is consumed directly. The two
frontier rows can therefore be combined without an unproved prime estimate.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.QRH

theorem exists_uniform_prime_row_bounds :
    exists C : Real, And (0 < C)
      (forall {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N),
        Not (chi = 1) -> forall X y m : Nat,
          norm (Finset.sum (Nat.largestPrimeFactorRow X y m)
            (fun r => chi (r : ZMod N))) <=
            C * (X : Real) ^ (7 / 8 : Real) *
              (1 + Real.log N + Real.log ((X : Real) + 2)) ^ 2) := by
  let B : Real := Classical.choose exists_primeCharacterSum_le_seven_eighths
  have hB := Classical.choose_spec exists_primeCharacterSum_le_seven_eighths
  refine Exists.intro (2 * B) (And.intro (by have := hB.1; positivity) ?_)
  intro N inst chi hchi X y m
  let E : Real := B * (X : Real) ^ (7 / 8 : Real) *
    (1 + Real.log N + Real.log ((X : Real) + 2)) ^ 2
  have hN : (1 : Real) <= (N : Real) := by
    have hNat : 1 <= N := Nat.pos_of_ne_zero (NeZero.ne N)
    exact_mod_cast hNat
  have hLogN := Real.log_nonneg hN
  have hPrefix : forall t, t <= X ->
      norm (Finset.sum (Nat.primesBelow (t + 1)) (fun r => chi (r : ZMod N))) <= E := by
    intro t ht
    have htX : (t : Real) <= (X : Real) := Nat.cast_le.mpr ht
    have hLog := Real.log_le_log (by positivity : (0 : Real) < (t : Real) + 2)
      (show (t : Real) + 2 <= (X : Real) + 2 by linarith)
    have hLogt : 0 <= Real.log ((t : Real) + 2) := Real.log_nonneg (by
      have h : (0 : Real) <= (t : Real) := Nat.cast_nonneg t
      linarith)
    have hLogX : 0 <= Real.log ((X : Real) + 2) := Real.log_nonneg (by
      have h : (0 : Real) <= (X : Real) := Nat.cast_nonneg X
      linarith)
    have hSq : (1 + Real.log N + Real.log ((t : Real) + 2)) ^ 2 <=
        (1 + Real.log N + Real.log ((X : Real) + 2)) ^ 2 := by nlinarith
    have hPow : (t : Real) ^ (7 / 8 : Real) <= (X : Real) ^ (7 / 8 : Real) :=
      Real.rpow_le_rpow (Nat.cast_nonneg t) htX (by norm_num)
    calc
      _ <= B * (t : Real) ^ (7 / 8 : Real) *
          (1 + Real.log N + Real.log ((t : Real) + 2)) ^ 2 := hB.2 chi hchi t
      _ <= E := mul_le_mul (mul_le_mul_of_nonneg_left hPow hB.1.le) hSq
        (sq_nonneg _) (mul_nonneg hB.1.le (Real.rpow_nonneg (Nat.cast_nonneg X) _))
  have hRow := Nat.norm_sum_largestPrimeFactorRow_le (fun r => chi (r : ZMod N))
    (fun _ => E) X y m (fun _ _ _ => le_refl E) hPrefix
  calc
    _ <= 2 * E := hRow
    _ = _ := by dsimp [E]; ring

end PrimeFactorOscillations.QRH

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
import PrimeFactorOscillations.Mathlib.NumberTheory.DirichletCharacter.PartialSum
import PrimeFactorOscillations.Mathlib.NumberTheory.SmoothNumbers.LargestPrimeFactorPowerBounds

/-!
# Uniform smooth-number and largest-prime-factor character bounds

A single constant works for every nonprincipal character and every positive
integer cutoff pair. All prime-prefix, cofactor and ordinary-period terms
are discharged. Residue counts require the subsequent orthogonality step.
These are sums over ordinary integers, not over generated prime-pair states.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.LPF

noncomputable def characterError (C : Real) (N X y : Nat) : Real :=
  C * (X : Real) * (y : Real) ^ (-(1 / 8 : Real)) *
    (1 + Real.log N + Real.log ((X : Real) + 2)) ^ 2

theorem characterError_nonneg (C : Real) (hC : 0 <= C) (N X y : Nat) :
    0 <= characterError C N X y := by
  unfold characterError
  positivity

theorem exists_uniform_character_bounds :
    exists C : Real, And (0 < C)
      (forall {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N),
        Not (chi = 1) -> forall X y : Nat, 0 < X -> 0 < y ->
          And
            (norm (Finset.sum (Nat.smoothNumbersUpTo X (y + 1))
              (fun n => chi (n : ZMod N))) <= (N : Real) + characterError C N X y)
            (norm (Finset.sum ((Finset.Icc 1 X).filter
              (fun n => y < Nat.largestPrimeFactor n))
              (fun n => chi (Nat.largestPrimeFactor n : ZMod N))) <= characterError C N X y)) := by
  let B : Real := Classical.choose QRH.exists_primeCharacterSum_le_seven_eighths
  have hBAll := Classical.choose_spec QRH.exists_primeCharacterSum_le_seven_eighths
  have hB : 0 < B := hBAll.1
  refine Exists.intro (16 * B) (And.intro (by positivity) ?_)
  intro N inst chi hchi X y hX hy
  let L : Real := 1 + Real.log N + Real.log ((X : Real) + 2)
  have hN := BombieriVinogradov.DirichletCharacter.three_le_level_of_ne_one chi hchi
  have hNR : (1 : Real) <= (N : Real) := by exact_mod_cast (by omega : 1 <= N)
  have hLN := Real.log_nonneg hNR
  have hFrozen : 0 <= B * L ^ 2 := mul_nonneg hB.le (sq_nonneg L)
  have hPrefix : forall t, t <= X ->
      norm (Finset.sum (Nat.primesBelow (t + 1)) (fun p => chi (p : ZMod N))) <=
        (B * L ^ 2) * (t : Real) ^ (7 / 8 : Real) := by
    intro t ht
    have htR : (t : Real) <= (X : Real) := Nat.cast_le.mpr ht
    have hLog : Real.log ((t : Real) + 2) <= Real.log ((X : Real) + 2) :=
      Real.log_le_log (by positivity) (by linarith)
    have hLt : 0 <= Real.log ((t : Real) + 2) :=
      Real.log_nonneg (by have h : (0 : Real) <= (t : Real) := Nat.cast_nonneg t; linarith)
    have hLX : 0 <= Real.log ((X : Real) + 2) :=
      Real.log_nonneg (by have h : (0 : Real) <= (X : Real) := Nat.cast_nonneg X; linarith)
    have hSq : (1 + Real.log N + Real.log ((t : Real) + 2)) ^ 2 <= L ^ 2 := by
      dsimp [L]
      nlinarith
    calc
      _ <= B * (t : Real) ^ (7 / 8 : Real) *
          (1 + Real.log N + Real.log ((t : Real) + 2)) ^ 2 := hBAll.2 chi hchi t
      _ <= B * (t : Real) ^ (7 / 8 : Real) * L ^ 2 :=
        mul_le_mul_of_nonneg_left hSq (mul_nonneg hB.le (Real.rpow_nonneg (Nat.cast_nonneg t) _))
      _ = (B * L ^ 2) * (t : Real) ^ (7 / 8 : Real) := by ring
  have hMul : forall m p : Nat, chi ((m * p : Nat) : ZMod N) =
      chi (m : ZMod N) * chi (p : ZMod N) := by
    intro m p
    simp only [Nat.cast_mul, map_mul]
  have hSmooth := Nat.norm_sum_smoothNumbersUpTo_le_rpow
    (fun n => chi (n : ZMod N)) hMul X y hX hy
    (7 / 8) (B * L ^ 2) (by norm_num) (by norm_num) hFrozen
    (fun m hm => chi.norm_le_one _) hPrefix
  have hLargest := Nat.norm_sum_largePrimeFactor_twist_le_rpow
    (fun n => chi (n : ZMod N)) X y hX hy
    (7 / 8) (B * L ^ 2) (by norm_num) (by norm_num) hFrozen hPrefix
  have hOrdinary := chi.norm_sum_Icc_le_modulus hchi X
  have hCoeff : (2 * (B * L ^ 2) / (1 - (7 / 8 : Real))) *
      (X : Real) * (y : Real) ^ ((7 / 8 : Real) - 1) =
      characterError (16 * B) N X y := by
    unfold characterError
    rw [show (7 / 8 : Real) - 1 = -(1 / 8 : Real) by norm_num]
    dsimp [L]
    ring
  rw [hCoeff] at hSmooth hLargest
  exact And.intro (hSmooth.trans (_root_.add_le_add hOrdinary le_rfl)) hLargest

end PrimeFactorOscillations.LPF

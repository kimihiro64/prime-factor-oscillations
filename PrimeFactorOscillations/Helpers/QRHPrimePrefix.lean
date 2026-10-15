/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.NumberTheory.DirichletCharacter.Bounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import PrimeFactorOscillations.Helpers.QRHCharacterChebyshev
import PrimeFactorOscillations.Mathlib.NumberTheory.Chebyshev.WeightedPrimePower
import PrimeFactorOscillations.Mathlib.NumberTheory.PrimeCounting.WeightedPrefix

/-!
# Uniform seven-eighths bounds for prime-character prefixes

The higher prime powers are removed with their full square-root mass.
Finite partial summation then removes the logarithm without losing a power.
The final bound includes every natural endpoint, including zero and one.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.QRH

open BombieriVinogradov.SiegelWalfisz

noncomputable def characterPrimeLogSum {N : Nat} (x : Nat)
    (chi : DirichletCharacter Complex N) : Complex :=
  Finset.sum (Finset.Icc 1 x)
    (fun n => if Nat.Prime n then HSMul.hSMul (Real.log (n : Real)) (chi (n : ZMod N)) else 0)

theorem norm_characterPrimeLogSum_le_psi {N : Nat}
    (chi : DirichletCharacter Complex N) {x : Nat} (hx : 1 <= x) :
    norm (characterPrimeLogSum x chi) <= norm (characterChebyshevSum x chi) +
      2 * Real.sqrt (x : Real) * Real.log (x : Real) := by
  have h := Chebyshev.norm_weighted_primeLog_sum_le
    (fun n => chi (n : ZMod N)) x hx (fun n hn => chi.norm_le_one (n : ZMod N))
  have hId : Finset.sum (Finset.Icc 1 x)
      (fun n => ((if Nat.Prime n then Real.log (n : Real) else 0 : Real) : Complex) *
        chi (n : ZMod N)) = characterPrimeLogSum x chi := by
    unfold characterPrimeLogSum
    apply Finset.sum_congr rfl
    intro n hn
    by_cases hp : Nat.Prime n
    next =>
      simp only [hp, if_pos]
      exact (Algebra.smul_def (Real.log (n : Real)) (chi (n : ZMod N))).symm
    next => simp [hp]
  rw [hId] at h
  exact h

theorem exists_characterPrimeLogSum_le_seven_eighths :
    exists A : Real, And (0 < A)
      (forall {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N),
        Not (chi = 1) -> forall {x : Nat}, 2 <= x ->
          norm (characterPrimeLogSum x chi) <=
            A * (x : Real) ^ (7 / 8 : Real) *
              (1 + Real.log N + Real.log ((x : Real) + 2)) ^ 2) := by
  let A : Real := Classical.choose exists_characterChebyshevSum_le_seven_eighths
  have hAAll := Classical.choose_spec exists_characterChebyshevSum_le_seven_eighths
  have hA : 0 < A := hAAll.1
  refine Exists.intro (A + 2) (And.intro (by positivity) ?_)
  intro N inst chi hchi x hx
  have hx1 : 1 <= x := by omega
  have hxR : (1 : Real) <= (x : Real) := by exact_mod_cast hx1
  have hN := BombieriVinogradov.DirichletCharacter.three_le_level_of_ne_one chi hchi
  have hNR : (1 : Real) <= (N : Real) := by exact_mod_cast (by omega : 1 <= N)
  have hLN := Real.log_nonneg hNR
  have hLx := Real.log_nonneg hxR
  have hLx2 : 0 <= Real.log ((x : Real) + 2) := Real.log_nonneg (by linarith)
  have hLogs : Real.log x <= Real.log ((x : Real) + 2) :=
    Real.log_le_log (zero_lt_one.trans_le hxR) (by linarith)
  let L : Real := 1 + Real.log N + Real.log ((x : Real) + 2)
  have hL : 1 <= L := by dsimp [L]; linarith
  have hLog : Real.log x <= L ^ 2 := by
    have h : Real.log x <= L := by dsimp [L]; linarith
    nlinarith
  have hSqrt : Real.sqrt (x : Real) <= (x : Real) ^ (7 / 8 : Real) := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hxR (by norm_num)
  have hError : 2 * Real.sqrt (x : Real) * Real.log x <=
      2 * (x : Real) ^ (7 / 8 : Real) * L ^ 2 := by
    exact mul_le_mul (mul_le_mul_of_nonneg_left hSqrt (by norm_num))
      hLog hLx (mul_nonneg (by norm_num) (Real.rpow_nonneg (Nat.cast_nonneg x) _))
  have hPsi := hAAll.2 chi hchi hx
  have hTheta := norm_characterPrimeLogSum_le_psi chi hx1
  change norm (characterPrimeLogSum x chi) <= (A + 2) * (x : Real) ^ (7 / 8 : Real) * L ^ 2
  change norm (characterChebyshevSum x chi) <= A * (x : Real) ^ (7 / 8 : Real) * L ^ 2 at hPsi
  nlinarith

theorem exists_primeCharacterSum_le_seven_eighths :
    exists B : Real, And (0 < B)
      (forall {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N),
        Not (chi = 1) -> forall x : Nat,
          norm (Finset.sum (Nat.primesBelow (x + 1)) (fun p => chi (p : ZMod N))) <=
            B * (x : Real) ^ (7 / 8 : Real) *
              (1 + Real.log N + Real.log ((x : Real) + 2)) ^ 2) := by
  let A : Real := Classical.choose exists_characterPrimeLogSum_le_seven_eighths
  have hAAll := Classical.choose_spec exists_characterPrimeLogSum_le_seven_eighths
  have hA : 0 < A := hAAll.1
  have hLogTwo : 0 < Real.log (2 : Real) := Real.log_pos (by norm_num)
  refine Exists.intro (A / Real.log (2 : Real)) (And.intro (div_pos hA hLogTwo) ?_)
  intro N inst chi hchi x
  have hN := BombieriVinogradov.DirichletCharacter.three_le_level_of_ne_one chi hchi
  have hNR : (1 : Real) <= (N : Real) := by exact_mod_cast (by omega : 1 <= N)
  have hLN := Real.log_nonneg hNR
  let L : Real := 1 + Real.log N + Real.log ((x : Real) + 2)
  have hLx2 : 0 <= Real.log ((x : Real) + 2) :=
    Real.log_nonneg (by have h : (0 : Real) <= (x : Real) := Nat.cast_nonneg x; linarith)
  have hL : 1 <= L := by dsimp [L]; linarith
  let M : Real := A * (x : Real) ^ (7 / 8 : Real) * L ^ 2
  have hM : 0 <= M := by dsimp [M]; positivity
  have hPrefixes : forall t, t <= x -> norm (characterPrimeLogSum t chi) <= M := by
    intro t htx
    by_cases ht : 2 <= t
    next =>
      have htR : (t : Real) <= (x : Real) := Nat.cast_le.mpr htx
      have hPow : (t : Real) ^ (7 / 8 : Real) <= (x : Real) ^ (7 / 8 : Real) :=
        Real.rpow_le_rpow (Nat.cast_nonneg t) htR (by norm_num)
      have hLog : Real.log ((t : Real) + 2) <= Real.log ((x : Real) + 2) :=
        Real.log_le_log (by positivity) (by linarith)
      have hLt0 : 0 <= Real.log ((t : Real) + 2) :=
        Real.log_nonneg (by have h : (0 : Real) <= (t : Real) := Nat.cast_nonneg t; linarith)
      have hSq : (1 + Real.log N + Real.log ((t : Real) + 2)) ^ 2 <= L ^ 2 := by
        dsimp [L]
        nlinarith
      calc
        _ <= A * (t : Real) ^ (7 / 8 : Real) *
            (1 + Real.log N + Real.log ((t : Real) + 2)) ^ 2 := hAAll.2 chi hchi ht
        _ <= M := mul_le_mul (mul_le_mul_of_nonneg_left hPow hA.le) hSq (sq_nonneg _)
          (mul_nonneg hA.le (Real.rpow_nonneg (Nat.cast_nonneg x) _))
    next =>
      have hsmall : Or (t = 0) (t = 1) := by omega
      rcases hsmall with h0 | h1
      next => simpa [characterPrimeLogSum, h0] using hM
      next => simpa [characterPrimeLogSum, h1] using hM
  have h := Nat.norm_sum_primesBelow_le_of_weighted_prefix
    (fun p => chi (p : ZMod N)) x M hPrefixes
  calc
    _ <= M / Real.log (2 : Real) := h
    _ = (A / Real.log (2 : Real)) * (x : Real) ^ (7 / 8 : Real) *
        (1 + Real.log N + Real.log ((x : Real) + 2)) ^ 2 := by dsimp [M, L]; ring

end PrimeFactorOscillations.QRH

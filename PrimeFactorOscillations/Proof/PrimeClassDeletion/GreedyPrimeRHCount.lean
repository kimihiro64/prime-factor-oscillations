/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Proof.PrimeClassDeletion.GreedyPrimeRHUpper
import PrimeFactorOscillations.Proof.PrimeClassDeletion.PrimeClassCountSplit

/-!
# The full square-root logarithmic RH deletion-count bound

Splitting at the square root saves the logarithm lost by charging every
deleted prime only its minimal weight. The finite initial mass, the native
greedy overshoot, and the entire low-prime count remain in the inequality.
-/

set_option autoImplicit false
set_option Elab.async false

open PrimeFactorOscillations.PrimeClassSampling

namespace PrimeFactorOscillations.PrimeClassDeletion

theorem primeClassPrefix_count_le_sqrt_log_of_theta_bound
    (P : Set Nat) (X : Nat) (hX : 4 <= X) (hLog : 1 <= Real.log (X : Real))
    (A C : Real) (hA : 0 <= A)
    (hTheta : primeClassTheta P X <=
      A + C * Real.sqrt (X : Real) * (Real.log (X : Real)) ^ 2 +
        Real.log (X : Real)) :
    ((primeClassPrefix P X).card : Real) <=
      (2 * A + 2 * C + 4) * Real.sqrt (X : Real) * Real.log (X : Real) := by
  let q := Real.sqrt (X : Real)
  let l := Real.log (X : Real)
  have hq : 1 <= q := by
    have h := Real.sqrt_le_sqrt (show (1 : Real) <= (X : Real) by exact_mod_cast (by omega : 1 <= X))
    simpa only [Real.sqrt_one] using h
  have hl : 1 <= l := hLog
  have hq0 : 0 <= q := Real.sqrt_nonneg _
  have hl0 : 0 <= l := by linarith only [hl]
  have hlPos : 0 < l := by linarith only [hl]
  have hLogSqrt : Real.log q = l / 2 := Real.log_sqrt (Nat.cast_nonneg X)
  have hCeil : (Nat.ceil q : Real) <= q + 1 := (Nat.ceil_lt_add_one hq0).le
  have hCeilScaled := mul_le_mul_of_nonneg_right hCeil (Real.log_nonneg hq)
  have hSplit := primeClassPrefix_count_mul_log_le_theta_add_initial P X q hq
  rw [hLogSqrt] at hSplit hCeilScaled
  have hRaw : ((primeClassPrefix P X).card : Real) * l <=
      2 * A + 2 * C * q * l ^ 2 + 2 * l + (q + 1) * l := by
    change primeClassTheta P X <= A + C * q * l ^ 2 + l at hTheta
    nlinarith only [hSplit, hCeilScaled, hTheta]
  have hQL : 1 <= q * l := by
    have h := mul_le_mul hq hl (by norm_num : (0 : Real) <= 1) hq0
    simpa only [one_mul] using h
  have hSq : 1 <= l ^ 2 := by nlinarith only [hl]
  have hQLSq : 1 <= q * l ^ 2 := by
    have h := mul_le_mul hq hSq (by norm_num : (0 : Real) <= 1) hq0
    simpa only [one_mul] using h
  have hInitialMass := mul_le_mul_of_nonneg_left hQLSq (show 0 <= 2 * A by positivity)
  have hOvershoot := mul_le_mul_of_nonneg_left hQL (show 0 <= 2 * l by positivity)
  have hLow := mul_le_mul (show q + 1 <= 2 * q by linarith only [hq])
    (show l <= l ^ 2 by nlinarith only [hl]) hl0 (show 0 <= 2 * q by positivity)
  have hCombined : ((primeClassPrefix P X).card : Real) * l <=
      (2 * A + 2 * C + 4) * q * l ^ 2 := by
    nlinarith only [hRaw, hInitialMass, hOvershoot, hLow]
  by_contra hFail
  have hBad := mul_lt_mul_of_pos_right (lt_of_not_ge hFail) hlPos
  change (2 * A + 2 * C + 4) * q * l * l <
    ((primeClassPrefix P X).card : Real) * l at hBad
  nlinarith only [hBad, hCombined]

theorem greedyDeletedPrimeClass_RH_count_sqrt_log_bound (hRH : RiemannHypothesis) :
    Exists fun C : Real => And (0 < C) (forall X : Nat,
      4 <= X -> 1 <= Real.log (X : Real) ->
        ((primeClassPrefix greedyDeletedPrimeClass X).card : Real) <=
          C * Real.sqrt (X : Real) * Real.log (X : Real)) := by
  choose A hA C hC hTheta using greedyDeletedPrimeClass_RH_theta_mass_bound hRH
  refine Exists.intro (2 * A + 2 * C + 4) (And.intro (by positivity) ?_)
  intro X hX hLog
  exact primeClassPrefix_count_le_sqrt_log_of_theta_bound greedyDeletedPrimeClass X hX hLog
    A C hA (hTheta X (by omega))

theorem greedyDeletedPrimeClass_RH_eventually_count_sqrt_log (hRH : RiemannHypothesis) :
    Exists fun C : Real => And (0 < C) (Exists fun N : Nat => forall X : Nat,
      N <= X ->
        ((primeClassPrefix greedyDeletedPrimeClass X).card : Real) <=
          C * Real.sqrt (X : Real) * Real.log (X : Real)) := by
  choose C hC hCount using greedyDeletedPrimeClass_RH_count_sqrt_log_bound hRH
  refine Exists.intro C (And.intro hC (Exists.intro (Nat.ceil (Real.exp 1) + 4) ?_))
  intro X hX
  have hFour : 4 <= X := by omega
  have hExp : Real.exp 1 <= (X : Real) :=
    (Nat.le_ceil (Real.exp 1)).trans (Nat.cast_le.mpr (by omega))
  have hLog : 1 <= Real.log (X : Real) := by
    have h := Real.log_le_log (Real.exp_pos 1) hExp
    simpa only [Real.log_exp] using h
  exact hCount X hFour hLog

end PrimeFactorOscillations.PrimeClassDeletion

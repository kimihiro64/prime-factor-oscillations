/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Proof.PrimeClassDeletion.GreedyPrimeClass

/-!
# Convert prime-class logarithmic mass into a count

Primes below the arbitrary real splitting point are charged to its ceiling.
Every remaining prime contributes at least the logarithm of that point.
-/

set_option autoImplicit false
set_option Elab.async false

open PrimeFactorOscillations.PrimeClassSampling

namespace PrimeFactorOscillations.PrimeClassDeletion

theorem primeClassPrefix_count_mul_log_le_theta_add_initial
    (P : Set Nat) (X : Nat) (q : Real) (hq : 1 <= q) :
    ((primeClassPrefix P X).card : Real) * Real.log q <=
      primeClassTheta P X + (Nat.ceil q : Real) * Real.log q := by
  classical
  let S := primeClassPrefix P X
  let K := Nat.ceil q
  have hLog : 0 <= Real.log q := Real.log_nonneg hq
  have hLow : (S.filter (fun p => p < K)).card <= K := by
    calc
      _ <= (Finset.range K).card := by
        apply Finset.card_le_card
        intro p hp
        exact Finset.mem_range.mpr (Finset.mem_filter.mp hp).2
      _ = K := Finset.card_range K
  have hTerm (p : Nat) (hp : Membership.mem S p) :
      Real.log q <= Real.log (p : Real) + if p < K then Real.log q else 0 := by
    have hPrime := primeClassPrefix_prime P X p hp
    have hpLog : 0 <= Real.log (p : Real) :=
      Real.log_nonneg (by exact_mod_cast hPrime.one_le)
    by_cases hSmall : p < K
    case pos =>
      simp only [ite_eq_left hSmall]
      linarith only [hpLog]
    case neg =>
      simp only [ite_eq_right hSmall, add_zero]
      have hKp : K <= p := le_of_not_gt hSmall
      have hqp : q <= (p : Real) := (Nat.le_ceil q).trans (Nat.cast_le.mpr hKp)
      exact Real.log_le_log (by linarith only [hq]) hqp
  calc
    _ = S.sum (fun _ => Real.log q) := by simp only [Finset.sum_const, nsmul_eq_mul, S]
    _ <= S.sum (fun p => Real.log (p : Real) + if p < K then Real.log q else 0) :=
      Finset.sum_le_sum hTerm
    _ = primeClassTheta P X + ((S.filter (fun p => p < K)).card : Real) * Real.log q := by
      rw [Finset.sum_add_distrib, <- Finset.sum_filter]
      simp only [Finset.sum_const, nsmul_eq_mul, primeClassTheta, S]
    _ <= _ := by
      have hScaled := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hLow) hLog
      dsimp only [K] at hScaled
      linarith only [hScaled]

end PrimeFactorOscillations.PrimeClassDeletion

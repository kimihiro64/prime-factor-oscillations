/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The logarithmic field of proper prime returns

The original single p-returns carry log(p). Higher prime-power divisors
provide an explicit additional compensation. Their complete sum cancels
the logarithmic source at every composite site, leaving the prime birth
weight. Binary least-owner reassignment must not discard these weights.
This is an exact model identity, not a new zero-free estimate.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.PrimeClassDeletion

noncomputable def primeWaveBirth (n : Nat) : Real :=
  if Nat.Prime n then Real.log (n : Real) else 0

noncomputable def primeSingleReturnWeight (n : Nat) : Real :=
  Finset.sum (n.divisors.erase n)
    (fun p => if Nat.Prime p then Real.log (p : Real) else 0)

noncomputable def primePowerReturnCompensation (n : Nat) : Real :=
  Finset.sum n.divisors
    (fun d => if Nat.Prime d then 0 else ArithmeticFunction.vonMangoldt d)

noncomputable def primeReturnLogWeight (n : Nat) : Real :=
  primeSingleReturnWeight n + primePowerReturnCompensation n

noncomputable def primeWaveHeadroom (x : Real) : Real :=
  x - Chebyshev.theta x

theorem primePowerReturnCompensation_nonneg (n : Nat) :
    0 <= primePowerReturnCompensation n := by
  apply Finset.sum_nonneg
  intro d hd
  by_cases hp : Nat.Prime d
  . simp [hp]
  . simpa only [hp, ite_false] using
      (ArithmeticFunction.vonMangoldt_nonneg : 0 <= ArithmeticFunction.vonMangoldt d)

theorem primeWaveBirth_add_returns (n : Nat) (hn : 0 < n) :
    primeWaveBirth n + primeReturnLogWeight n = Real.log (n : Real) := by
  have hself : Membership.mem n.divisors n :=
    Nat.mem_divisors_self n (Nat.ne_of_gt hn)
  have herase := Finset.sum_erase_add n.divisors
    (fun d => if Nat.Prime d then Real.log (d : Real) else 0) hself
  have hsplit : forall d : Nat,
      (if Nat.Prime d then Real.log (d : Real) else 0) +
        (if Nat.Prime d then 0 else ArithmeticFunction.vonMangoldt d) =
          ArithmeticFunction.vonMangoldt d := by
    intro d
    by_cases hp : Nat.Prime d
    . simp [hp, ArithmeticFunction.vonMangoldt_apply_prime hp]
    . simp [hp]
  calc
    primeWaveBirth n + primeReturnLogWeight n =
        (Finset.sum (n.divisors.erase n)
            (fun d => if Nat.Prime d then Real.log (d : Real) else 0) +
          (if Nat.Prime n then Real.log (n : Real) else 0)) +
        Finset.sum n.divisors
          (fun d => if Nat.Prime d then 0 else ArithmeticFunction.vonMangoldt d) := by
      unfold primeWaveBirth primeReturnLogWeight primeSingleReturnWeight
        primePowerReturnCompensation
      ring
    _ = Finset.sum n.divisors
          (fun d => if Nat.Prime d then Real.log (d : Real) else 0) +
        Finset.sum n.divisors
          (fun d => if Nat.Prime d then 0 else ArithmeticFunction.vonMangoldt d) := by
      rw [herase]
    _ = Finset.sum n.divisors ArithmeticFunction.vonMangoldt := by
      rw [<- Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro d hd
      exact hsplit d
    _ = Real.log (n : Real) := ArithmeticFunction.vonMangoldt_sum

theorem primeReturnLogWeight_eq_zero_of_prime (n : Nat) (hn : Nat.Prime n) :
    primeReturnLogWeight n = 0 := by
  have h := primeWaveBirth_add_returns n hn.pos
  simp only [primeWaveBirth, hn, ite_true] at h
  linarith only [h]

theorem primeReturnLogWeight_eq_log_of_not_prime (n : Nat)
    (hn : 0 < n) (hprime : Not (Nat.Prime n)) :
    primeReturnLogWeight n = Real.log (n : Real) := by
  have h := primeWaveBirth_add_returns n hn
  simpa only [primeWaveBirth, hprime, ite_false, zero_add] using h

theorem primeWaveTheta_nat_succ (n : Nat) :
    Chebyshev.theta ((n + 1 : Nat) : Real) =
      Chebyshev.theta (n : Real) + primeWaveBirth (n + 1) := by
  unfold Chebyshev.theta primeWaveBirth
  simp only [Nat.floor_natCast, Finset.sum_filter]
  exact Finset.sum_Ioc_succ_top (Nat.zero_le n)
    (fun p => if Nat.Prime p then Real.log (p : Real) else 0)

theorem primeWaveHeadroom_nat_succ (n : Nat) :
    primeWaveHeadroom ((n + 1 : Nat) : Real) - primeWaveHeadroom (n : Real) =
      1 - Real.log ((n + 1 : Nat) : Real) + primeReturnLogWeight (n + 1) := by
  have hbirth := primeWaveBirth_add_returns (n + 1) (Nat.zero_lt_succ n)
  unfold primeWaveHeadroom
  rw [primeWaveTheta_nat_succ]
  simp only [Nat.cast_add, Nat.cast_one] at hbirth
  simp only [Nat.cast_add, Nat.cast_one]
  linarith only [hbirth]

theorem primeWaveHeadroom_eq_compensated_returns (N : Nat) :
    primeWaveHeadroom (N : Real) =
      (N : Real) - Real.log (N.factorial : Real) +
        Finset.sum (Finset.range N) (fun j => primeReturnLogWeight (j + 1)) := by
  induction N with
  | zero =>
      simp [primeWaveHeadroom, Chebyshev.theta]
  | succ N ih =>
      have hstep := primeWaveHeadroom_nat_succ N
      have hfac : Real.log ((N + 1).factorial : Real) =
          Real.log ((N + 1 : Nat) : Real) + Real.log (N.factorial : Real) := by
        rw [Nat.factorial_succ, Nat.cast_mul]
        apply Real.log_mul
        . exact_mod_cast Nat.ne_of_gt (Nat.zero_lt_succ N)
        . exact_mod_cast Nat.ne_of_gt (Nat.factorial_pos N)
      rw [Finset.sum_range_succ, hfac]
      simp only [Nat.cast_add, Nat.cast_one] at hstep ih
      simp only [Nat.cast_add, Nat.cast_one]
      linarith only [hstep, ih]

theorem primeWave_compensated_square_step (n : Nat) (hn : 0 < n) :
    (1 - Real.log (n : Real) + primeReturnLogWeight n) ^ 2 -
        (primeWaveBirth n) ^ 2 + 1 = 2 * (1 - primeWaveBirth n) := by
  have hbirth := primeWaveBirth_add_returns n hn
  have hstep : 1 - Real.log (n : Real) + primeReturnLogWeight n =
      1 - primeWaveBirth n := by
    linarith only [hbirth]
  rw [hstep]
  ring

theorem primeWave_compensated_square_readout (N : Nat) :
    Finset.sum (Finset.range N)
      (fun j => (1 - Real.log ((j + 1 : Nat) : Real) +
          primeReturnLogWeight (j + 1)) ^ 2 -
        (primeWaveBirth (j + 1)) ^ 2 + 1) =
      2 * primeWaveHeadroom (N : Real) := by
  induction N with
  | zero =>
      simp [primeWaveHeadroom, Chebyshev.theta]
  | succ N ih =>
      have hstep := primeWaveHeadroom_nat_succ N
      have hbirth := primeWaveBirth_add_returns (N + 1) (Nat.zero_lt_succ N)
      have hunit : primeWaveHeadroom ((N + 1 : Nat) : Real) -
          primeWaveHeadroom (N : Real) = 1 - primeWaveBirth (N + 1) := by
        linarith only [hstep, hbirth]
      rw [Finset.sum_range_succ, ih,
        primeWave_compensated_square_step (N + 1) (Nat.zero_lt_succ N)]
      linarith only [hunit]

end PrimeFactorOscillations.PrimeClassDeletion

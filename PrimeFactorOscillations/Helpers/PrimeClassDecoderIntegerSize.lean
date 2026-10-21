/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Tactic.GCongr
import PrimeFactorOscillations.Helpers.PrimeClassDecoderIntegerProbes
import PrimeFactorOscillations.Helpers.PrimeClassSamplingProbability

/-!
# Size of the actual finite decoder integers

The coefficient budget is derived from the actual sample partition for
every truncation rank. No asymptotic or class summability is assumed.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.PrimeClassDecoder

theorem sampleCount_partial_sum_le (P : Set Nat) (N M : Nat) :
    (Finset.range (M + 1)).sum (sampleCount P N) <= N := by
  classical
  by_cases hMN : M <= N
  case pos =>
    calc
      (Finset.range (M + 1)).sum (sampleCount P N) <=
          (Finset.range (N + 1)).sum (sampleCount P N) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.range_mono (Nat.succ_le_succ hMN))
        intro i hi hnot
        exact Nat.zero_le _
      _ = N := PrimeClassSampling.sampleCount_sum P N
  case neg =>
    have hNM : N <= M := by omega
    have heq : (Finset.range (N + 1)).sum (sampleCount P N) =
        (Finset.range (M + 1)).sum (sampleCount P N) := by
      apply Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ hNM))
      intro k hk hnot
      have hNk : N < k := by
        have hnot' : Not (k < N + 1) := fun h => hnot (Finset.mem_range.mpr h)
        omega
      exact PrimeClassSampling.sampleCount_eq_zero_of_lt P N k hNk
    rw [<- heq, PrimeClassSampling.sampleCount_sum]

theorem integerProbe_abs_le_coefficient_mass
    (M R n : Nat) (C : Nat -> Nat) (hn : n <= R) :
    abs (integerProbe M C n : Real) <=
      ((Finset.range (M + 1)).sum (fun k => (C k : Real))) *
        (2 * (R : Real) + 1) ^ M * (2 : Real) ^ M := by
  have hbase : (1 : Real) <= 2 * (R : Real) + 1 := by
    have hR : (0 : Real) <= (R : Real) := Nat.cast_nonneg R
    linarith
  have hx : 0 <= 2 * (n : Real) + 1 := by positivity
  simp only [integerProbe, Int.cast_sum, Int.cast_mul, Int.cast_pow,
    Int.cast_neg, Int.cast_one, Int.cast_natCast, Nat.cast_add,
    Nat.cast_mul, Nat.cast_ofNat]
  push_cast
  calc
    abs ((Finset.range (M + 1)).sum (fun k =>
        (-1 : Real) ^ k * (C k : Real) * (2 * (n : Real) + 1) ^ k *
          (2 : Real) ^ (M - k))) <=
        (Finset.range (M + 1)).sum (fun k =>
          abs ((-1 : Real) ^ k * (C k : Real) *
            (2 * (n : Real) + 1) ^ k * (2 : Real) ^ (M - k))) :=
      Finset.abs_sum_le_sum_abs _ _
    _ <= (Finset.range (M + 1)).sum (fun k =>
        (C k : Real) * (2 * (R : Real) + 1) ^ M * (2 : Real) ^ M) := by
      apply Finset.sum_le_sum
      intro k hk
      have hkM : k <= M := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
      have hpow : (2 * (n : Real) + 1) ^ k <= (2 * (R : Real) + 1) ^ M := by
        calc
          (2 * (n : Real) + 1) ^ k <= (2 * (R : Real) + 1) ^ k := by
            gcongr
          _ <= (2 * (R : Real) + 1) ^ M := by
            gcongr
      have htwo : (2 : Real) ^ (M - k) <= (2 : Real) ^ M := by
        gcongr <;> norm_num
      have hC : (0 : Real) <= (C k : Real) := Nat.cast_nonneg (C k)
      simp only [abs_mul, abs_pow, abs_neg, abs_one, one_pow,
        abs_of_nonneg hC, abs_of_nonneg hx, one_mul,
        abs_of_pos (show (0 : Real) < 2 by norm_num)]
      gcongr
    _ = ((Finset.range (M + 1)).sum (fun k => (C k : Real))) *
        (2 * (R : Real) + 1) ^ M * (2 : Real) ^ M := by
      rw [<- Finset.sum_mul, <- Finset.sum_mul]

theorem integerSampleProbe_abs_le (P : Set Nat) (N M R n : Nat) (hn : n <= R) :
    abs (integerProbe M (sampleCount P N) n : Real) <=
      (N : Real) * (2 * (R : Real) + 1) ^ M * (2 : Real) ^ M := by
  have hmass : (Finset.range (M + 1)).sum
      (fun k => (sampleCount P N k : Real)) <= (N : Real) := by
    exact_mod_cast sampleCount_partial_sum_le P N M
  exact (integerProbe_abs_le_coefficient_mass M R n (sampleCount P N) hn).trans
    (by gcongr)

end PrimeFactorOscillations.PrimeClassDecoder

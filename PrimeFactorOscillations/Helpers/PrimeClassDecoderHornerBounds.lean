/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.PrimeClassDecoderHorner

/-!
# Uniform bounds for all retained Horner values

This controls every partial accumulator and its next multiplication,
not just the final integer probe. The sample coefficient bounds are
proved from the actual partition of one through N.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.PrimeClassDecoder

theorem sampleCount_le_sampleSize (P : Set Nat) (N k : Nat) :
    sampleCount P N k <= N := by
  exact (Finset.single_le_sum (fun i hi => Nat.zero_le (sampleCount P N i))
    (Finset.mem_range.mpr (Nat.lt_succ_self k))).trans
      (sampleCount_partial_sum_le P N k)

theorem nat_succ_le_two_pow (M : Nat) : M + 1 <= 2 ^ M := by
  induction M with
  | zero => norm_num
  | succ M ih =>
    rw [pow_succ]
    omega

theorem integerHornerState_shifted_abs_le
    (C : Nat -> Nat) (x : Int) (M N j ell : Nat) (A : Real)
    (hA : 1 <= A) (hx : abs (x : Real) <= A)
    (hj : j + ell <= M + 1) (hC : forall k, k <= M -> C k <= N) :
    abs ((x ^ ell * (integerHornerState C x M j).accumulator : Int) : Real) <=
      (j : Real) * (N : Real) * A ^ M * (2 : Real) ^ M := by
  rw [integerHornerState_sum]
  simp only [Int.cast_mul, Int.cast_pow, Int.cast_sum, Int.cast_natCast, Int.cast_ofNat]
  rw [Finset.mul_sum]
  calc
    abs ((Finset.range j).sum (fun i =>
        (x : Real) ^ ell * ((C (M - i) : Real) *
          (x : Real) ^ (j - 1 - i) * (2 : Real) ^ i))) <=
        (Finset.range j).sum (fun i =>
          abs ((x : Real) ^ ell * ((C (M - i) : Real) *
            (x : Real) ^ (j - 1 - i) * (2 : Real) ^ i))) :=
      Finset.abs_sum_le_sum_abs _ _
    _ <= (Finset.range j).sum (fun i => (N : Real) * A ^ M * (2 : Real) ^ M) := by
      apply Finset.sum_le_sum
      intro i hi
      have hij : i < j := Finset.mem_range.mp hi
      have hiM : i <= M := by omega
      have heM : j - 1 - i + ell <= M := by omega
      have hcoeff : (C (M - i) : Real) <= (N : Real) := by
        exact_mod_cast hC (M - i) (Nat.sub_le M i)
      have hcoeff0 : (0 : Real) <= (C (M - i) : Real) := Nat.cast_nonneg _
      have hpow : abs (x : Real) ^ (j - 1 - i + ell) <= A ^ M := by
        calc
          abs (x : Real) ^ (j - 1 - i + ell) <= A ^ (j - 1 - i + ell) := by
            gcongr
          _ <= A ^ M := by gcongr
      have htwo : (2 : Real) ^ i <= (2 : Real) ^ M := by
        gcongr
        norm_num
      simp only [abs_mul, abs_pow, abs_of_nonneg hcoeff0,
        abs_of_pos (show (0 : Real) < 2 by norm_num)]
      have halgebra :
          abs (x : Real) ^ ell * ((C (M - i) : Real) *
            abs (x : Real) ^ (j - 1 - i) * (2 : Real) ^ i) =
          (C (M - i) : Real) *
            abs (x : Real) ^ (j - 1 - i + ell) * (2 : Real) ^ i := by
        rw [pow_add]
        ring
      rw [halgebra]
      gcongr
    _ = (j : Real) * (N : Real) * A ^ M * (2 : Real) ^ M := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      ring

theorem integerHornerState_uniform_abs_le
    (C : Nat -> Nat) (x : Int) (M N j ell : Nat) (A : Real)
    (hA : 1 <= A) (hx : abs (x : Real) <= A)
    (hj : j + ell <= M + 1) (hC : forall k, k <= M -> C k <= N) :
    abs ((x ^ ell * (integerHornerState C x M j).accumulator : Int) : Real) <=
      (N : Real) * A ^ M * (4 : Real) ^ M := by
  have hjpow : j <= 2 ^ M := (by omega : j <= M + 1).trans (nat_succ_le_two_pow M)
  have hjreal : (j : Real) <= (2 : Real) ^ M := by exact_mod_cast hjpow
  calc
    abs ((x ^ ell * (integerHornerState C x M j).accumulator : Int) : Real) <=
        (j : Real) * (N : Real) * A ^ M * (2 : Real) ^ M :=
      integerHornerState_shifted_abs_le C x M N j ell A hA hx hj hC
    _ <= (2 : Real) ^ M * (N : Real) * A ^ M * (2 : Real) ^ M := by
      gcongr
    _ = (N : Real) * A ^ M * (4 : Real) ^ M := by
      rw [show (4 : Real) ^ M = (2 : Real) ^ M * (2 : Real) ^ M by
        rw [<- mul_pow]; norm_num]
      ring

theorem integerHornerSample_shifted_abs_le
    (P : Set Nat) (N M R n j ell : Nat) (hn : n <= R) (hj : j + ell <= M + 1) :
    abs (((-((2 * n + 1 : Nat) : Int)) ^ ell *
      (integerHornerState (sampleCount P N)
        (-((2 * n + 1 : Nat) : Int)) M j).accumulator : Int) : Real) <=
      (N : Real) * (2 * (R : Real) + 1) ^ M * (4 : Real) ^ M := by
  have hA : (1 : Real) <= 2 * (R : Real) + 1 := by
    have hR : (0 : Real) <= (R : Real) := Nat.cast_nonneg R
    linarith
  have hx : abs (((-((2 * n + 1 : Nat) : Int)) : Int) : Real) <=
      2 * (R : Real) + 1 := by
    simp only [Int.cast_neg, Int.cast_natCast, abs_neg,
      abs_of_nonneg (show (0 : Real) <= ((2 * n + 1 : Nat) : Real) by positivity)]
    push_cast
    gcongr
  exact integerHornerState_uniform_abs_le (sampleCount P N)
    (-((2 * n + 1 : Nat) : Int)) M N j ell (2 * (R : Real) + 1) hA hx hj
    (fun k hk => sampleCount_le_sampleSize P N k)

theorem integerHornerSample_step_values_le
    (P : Set Nat) (N M R n j : Nat) (hn : n <= R) (hj : j <= M) :
    And
      (abs (((integerHornerState (sampleCount P N)
        (-((2 * n + 1 : Nat) : Int)) M (j + 1)).accumulator : Int) : Real) <=
          (N : Real) * (2 * (R : Real) + 1) ^ M * (4 : Real) ^ M)
      (abs (((-((2 * n + 1 : Nat) : Int)) *
        (integerHornerState (sampleCount P N)
          (-((2 * n + 1 : Nat) : Int)) M j).accumulator : Int) : Real) <=
          (N : Real) * (2 * (R : Real) + 1) ^ M * (4 : Real) ^ M) := by
  apply And.intro
  case left =>
    simpa only [pow_zero, one_mul] using
      integerHornerSample_shifted_abs_le P N M R n (j + 1) 0 hn (by omega)
  case right =>
    simpa only [pow_one] using
      integerHornerSample_shifted_abs_le P N M R n j 1 hn (by omega)

end PrimeFactorOscillations.PrimeClassDecoder

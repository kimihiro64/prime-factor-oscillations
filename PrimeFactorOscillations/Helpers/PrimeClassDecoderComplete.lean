/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.PrimeClassDecoderPreprocessingCost
import PrimeFactorOscillations.Helpers.PrimeClassDecoderPreprocessingValues

/-!
# Complete finite integer decoding, including preprocessing

The literal executable program may evaluate each adjacent endpoint again;
its cost is charged for both evaluations. The full preprocessing and
evaluation cost is at most 31*R_N*M_N eventually. The same threshold
certifies exact integer signs, every prefix count and logarithmic binary
widths for the preprocessing, Horner and comparison values.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.PrimeClassDecoder

theorem int_neg_one_pow_sign (k : Nat) :
    ((-1 : Int) ^ k).sign = (-1 : Int) ^ k := by
  induction k with
  | zero => norm_num
  | succ k ih =>
    rw [pow_succ, Int.sign_mul, ih, Int.sign_neg_one]

theorem int_sign_of_parity_aligned (z : Int) (k : Nat)
    (hpos : 0 < (-1 : Real) ^ k * (z : Real)) :
    z.sign = (-1 : Int) ^ k := by
  have hInt : 0 < (-1 : Int) ^ k * z := by exact_mod_cast hpos
  have hsign := Int.sign_eq_one_of_pos hInt
  rw [Int.sign_mul, int_neg_one_pow_sign] at hsign
  have hsquare : (-1 : Int) ^ k * (-1 : Int) ^ k = 1 := by
    rw [<- mul_pow]
    norm_num
  have hmul := congrArg (fun a : Int => (-1 : Int) ^ k * a) hsign
  rw [<- mul_assoc, hsquare, one_mul, mul_one] at hmul
  exact hmul

def integerHornerLiteralOperations (R M : Nat) : Nat :=
  2 * R * (5 * (M + 1) + 4) + 2 * R

theorem integerHorner_literal_operation_bound (R M : Nat) (hM : 1 <= M) :
    integerHornerLiteralOperations R M <= 30 * R * M := by
  unfold integerHornerLiteralOperations
  nlinarith

theorem integerHorner_literal_counter_eq (R M : Nat) (C : Nat -> Nat) :
    (Finset.Icc 1 R).sum (fun n =>
      (integerHornerState C (-((2 * (n - 1) + 1 : Nat) : Int)) M (M + 1)).arithmeticSteps +
        (integerHornerState C (-((2 * n + 1 : Nat) : Int)) M (M + 1)).arithmeticSteps + 10) =
      integerHornerLiteralOperations R M := by
  simp only [integerHornerState_arithmeticSteps, Finset.sum_const, Nat.card_Icc,
    Nat.add_sub_cancel, nsmul_eq_mul, Nat.cast_id, integerHornerLiteralOperations]
  ring

end PrimeFactorOscillations.PrimeClassDecoder

namespace PrimeFactorOscillations.PrimeClassSampling

open Filter
open PrimeFactorOscillations.PrimeClassDecoder

structure CompleteIntegerDecoderCertificate (P : Set Nat) (N : Nat) (h c : Rat) : Prop where
  evaluation : FiniteIntegerDecoderCertificate P N (h : Real) (c : Real)
  preprocessing : DecoderPreprocessingBitCertificate h c N
  executable_exact :
    executableIntegerPrimeDecoder h c N (sampleCount P N) =
      primeClassPrefix P (decoderRadius (h : Real) N + 1)
  literal_sign : forall n : Nat, n <= decoderRadius (h : Real) N ->
    (integerProbe (decoderRank (c : Real) N) (sampleCount P N) n).sign =
      (-1 : Int) ^ (primeClassPrefix P (n + 1)).card
  total_arithmetic_operations :
    decoderPreprocessingOperations h N +
      (Finset.Icc 1 (decoderRadius (h : Real) N)).sum (fun n =>
        (integerHornerState (sampleCount P N) (-((2 * (n - 1) + 1 : Nat) : Int))
          (decoderRank (c : Real) N) (decoderRank (c : Real) N + 1)).arithmeticSteps +
        (integerHornerState (sampleCount P N) (-((2 * n + 1 : Nat) : Int))
          (decoderRank (c : Real) N) (decoderRank (c : Real) N + 1)).arithmeticSteps + 10) <=
        31 * decoderRadius (h : Real) N * decoderRank (c : Real) N

theorem finite_integer_prime_decoding_complete
    (P : Set Nat) (sigma : Real) (h c : Rat) (hs : 0 < sigma) (hs1 : sigma < 1)
    (hsum : Summable (classPowerWeight P sigma))
    (hh : 0 < h) (hc : 0 < c) (hpower : (h : Real) * sigma < 1)
    (hcBound : (c : Real) < (1 - sigma) / (h : Real)) :
    Filter.Eventually (fun N : Nat => CompleteIntegerDecoderCertificate P N h c) atTop := by
  have hcR : (0 : Real) < (c : Real) := by exact_mod_cast hc
  filter_upwards [
    executable_integer_prime_decoding P sigma h c hs hs1 hsum hh hc hpower hcBound,
    decoder_preprocessing_bit_certificate h c hh hc,
    decoderPreprocessingOperations_eventual h c hh hc,
    (decoderRank_real_atTop (c : Real) hcR).eventually (eventually_ge_atTop 1)]
      with N hdecode hbits hprep hM
  have hMN : 1 <= decoderRank (c : Real) N := by exact_mod_cast hM
  have houtput := hdecode.2
  rw [rationalDecoderRadiusFromRat_eq h (le_of_lt hh)] at houtput
  refine {
    evaluation := hdecode.1
    preprocessing := hbits
    executable_exact := houtput
    literal_sign := ?literal_sign
    total_arithmetic_operations := ?total_arithmetic_operations }
  case literal_sign =>
    intro n hn
    exact int_sign_of_parity_aligned _ _ ((hdecode.1.signed_probes n hn).1)
  case total_arithmetic_operations =>
    rw [integerHorner_literal_counter_eq]
    calc
      decoderPreprocessingOperations h N +
          integerHornerLiteralOperations (decoderRadius (h : Real) N) (decoderRank (c : Real) N) <=
          decoderRadius (h : Real) N * decoderRank (c : Real) N +
            30 * decoderRadius (h : Real) N * decoderRank (c : Real) N :=
        Nat.add_le_add hprep (integerHorner_literal_operation_bound _ _ hMN)
      _ = 31 * decoderRadius (h : Real) N * decoderRank (c : Real) N := by ring

end PrimeFactorOscillations.PrimeClassSampling

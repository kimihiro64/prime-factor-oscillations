/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.PrimeClassDecoderAlgorithm
import PrimeFactorOscillations.Helpers.PrimeClassDecoderArithmeticValues

/-!
# The actual decoder with simultaneous arithmetic and bit guarantees

One eventual threshold controls every prefix, every retained Horner value,
the stored powers, scaled coefficients and the full sign-test products.
The arithmetic model charges the sum of the explicit Horner counters,
four setup operations per point and two operations per adjacent test.
Rational-parameter construction of the selector integers is separate.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.PrimeClassDecoder

theorem integerHorner_complete_counter_eq (R M : Nat) (C : Nat -> Nat) :
    (Finset.range (R + 1)).sum (fun n =>
      (integerHornerState C (-((2 * n + 1 : Nat) : Int)) M (M + 1)).arithmeticSteps) +
        4 * (R + 1) + 2 * R = integerHornerCompleteOperations R M := by
  simp only [integerHornerState_arithmeticSteps, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul, Nat.cast_id, integerHornerCompleteOperations]
  ring

end PrimeFactorOscillations.PrimeClassDecoder

namespace PrimeFactorOscillations.PrimeClassSampling

open Filter
open PrimeFactorOscillations.PrimeClassDecoder

structure FiniteIntegerDecoderCertificate
    (P : Set Nat) (N : Nat) (h c : Real) : Prop where
  signed_probes : forall n : Nat, n <= decoderRadius h N ->
    And (0 < (-1 : Real) ^ (primeClassPrefix P (n + 1)).card *
      (integerProbe (decoderRank c N) (sampleCount P N) n : Real))
      (Not (integerProbe (decoderRank c N) (sampleCount P N) n = 0))
  adjacent_labels : forall n : Nat, 1 <= n -> n <= decoderRadius h N ->
    (integerProbe (decoderRank c N) (sampleCount P N) (n - 1) *
      integerProbe (decoderRank c N) (sampleCount P N) n < 0 <->
        And (Nat.Prime (n + 1)) (Membership.mem P (n + 1)))
  all_prefixes : forall r : Nat, r <= decoderRadius h N ->
    And (integerPrimeDecoder r (decoderRank c N) (sampleCount P N) =
        primeClassPrefix P (r + 1))
      ((integerSignChangeIndices r (decoderRank c N) (sampleCount P N)).card =
        (primeClassPrefix P (r + 1)).card)
  finite_data : forall D : Nat -> Nat,
    (forall k : Nat, k <= decoderRank c N -> D k = sampleCount P N k) ->
    integerPrimeDecoder (decoderRadius h N) (decoderRank c N) D =
      primeClassPrefix P (decoderRadius h N + 1)
  horner_correct : forall n : Nat,
    (integerHornerState (sampleCount P N) (-((2 * n + 1 : Nat) : Int))
      (decoderRank c N) (decoderRank c N + 1)).accumulator =
        integerProbe (decoderRank c N) (sampleCount P N) n
  arithmetic_cost :
    (Finset.range (decoderRadius h N + 1)).sum (fun n =>
      (integerHornerState (sampleCount P N) (-((2 * n + 1 : Nat) : Int))
        (decoderRank c N) (decoderRank c N + 1)).arithmeticSteps) +
          4 * (decoderRadius h N + 1) + 2 * decoderRadius h N <=
            30 * decoderRadius h N * decoderRank c N
  probe_bits : forall n : Nat, n <= decoderRadius h N ->
    (integerBitWidth (integerProbe (decoderRank c N) (sampleCount P N) n) : Real) <=
      decoderBitConstant h c * Real.log (N : Real)
  horner_bits : forall n j ell : Nat, n <= decoderRadius h N ->
    j + ell <= decoderRank c N + 1 ->
    (integerBitWidth
      ((-((2 * n + 1 : Nat) : Int)) ^ ell *
        (integerHornerState (sampleCount P N) (-((2 * n + 1 : Nat) : Int))
          (decoderRank c N) j).accumulator) : Real) <=
            decoderBitConstant h c * Real.log (N : Real)
  coefficient_bits : forall k j : Nat, j <= decoderRank c N ->
    (integerBitWidth ((sampleCount P N k : Int) * (2 : Int) ^ j) : Real) <=
      decoderBitConstant h c * Real.log (N : Real)
  stored_power_bits : forall n j : Nat, j <= decoderRank c N + 1 ->
    (integerBitWidth
      ((integerHornerState (sampleCount P N) (-((2 * n + 1 : Nat) : Int))
        (decoderRank c N) j).twoPower : Int) : Real) <=
          decoderBitConstant h c * Real.log (N : Real)
  comparison_bits : forall a b : Nat, a <= decoderRadius h N -> b <= decoderRadius h N ->
    (integerBitWidth (integerProbe (decoderRank c N) (sampleCount P N) a *
      integerProbe (decoderRank c N) (sampleCount P N) b) : Real) <=
        2 * decoderBitConstant h c * Real.log (N : Real)
  bit_constant_pos : 0 < decoderBitConstant h c

theorem finite_integer_prime_decoding_certificate
    (P : Set Nat) (sigma h c : Real) (hs : 0 < sigma) (hs1 : sigma < 1)
    (hsum : Summable (classPowerWeight P sigma))
    (hh : 0 < h) (hc : 0 < c) (hpower : h * sigma < 1)
    (hcBound : c < (1 - sigma) / h) :
    Filter.Eventually (fun N : Nat => FiniteIntegerDecoderCertificate P N h c) atTop := by
  filter_upwards [
    finite_integer_prime_decoding P sigma h c hs hs1 hsum hh hc hpower hcBound,
    finite_integer_prime_decoding_all_prefixes P sigma h c hs hs1 hsum hh hc hpower hcBound,
    integerSampleProbe_bits_eventual P h c hh hc,
    integerHornerSample_bits_eventual P h c hh hc,
    integerHornerSample_stored_bits_eventual P h c hh hc,
    integerSampleProbe_product_bits_eventual P h c hh hc,
    (decoderRadius_real_atTop h hh).eventually (eventually_ge_atTop 1),
    (decoderRank_real_atTop c hc).eventually (eventually_ge_atTop 1)]
      with N hmath hprefix hprobe hhorner hstored hproduct hR hM
  have hRN : 1 <= decoderRadius h N := by exact_mod_cast hR
  have hMN : 1 <= decoderRank c N := by exact_mod_cast hM
  refine {
    signed_probes := hmath.1
    adjacent_labels := hmath.2.1
    all_prefixes := hprefix
    finite_data := ?finite_data
    horner_correct := fun n => integerHornerState_eq_integerProbe _ n _
    arithmetic_cost := ?arithmetic_cost
    probe_bits := hprobe
    horner_bits := hhorner
    coefficient_bits := hstored.1
    stored_power_bits := hstored.2
    comparison_bits := hproduct
    bit_constant_pos := ?bit_constant_pos }
  case finite_data =>
    intro D hD
    rw [integerPrimeDecoder_eq_of_counts_agree (decoderRadius h N) (decoderRank c N)
      D (sampleCount P N) hD]
    exact (hprefix (decoderRadius h N) (Nat.le_refl _)).1
  case arithmetic_cost =>
    rw [integerHorner_complete_counter_eq]
    exact integerHorner_complete_operation_bound _ _ hRN hMN
  case bit_constant_pos =>
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hch : 0 < c * h := mul_pos hc hh
    unfold decoderBitConstant
    positivity

end PrimeFactorOscillations.PrimeClassSampling

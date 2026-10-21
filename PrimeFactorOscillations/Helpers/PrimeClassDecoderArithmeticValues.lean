/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.PrimeClassDecoderBits

/-!
# Stored powers, coefficient products and sign-test products

All remaining arithmetic values in the Horner evaluation have the same
logarithmic bit bound. Multiplying two probes for a sign test is charged
its full squared magnitude budget.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.PrimeClassDecoder

open Filter

theorem decoder_pow_two_le_budget
    (N R M j : Nat) (hN : 1 <= N) (hj : j <= 2 * M) :
    (2 : Real) ^ j <= decoderIntegerMagnitudeBudget N R M := by
  have hNr : (1 : Real) <= (N : Real) := by exact_mod_cast hN
  have hA : (1 : Real) <= 2 * (R : Real) + 1 := by
    have hR : (0 : Real) <= (R : Real) := Nat.cast_nonneg R
    linarith
  have hApow : (1 : Real) <= (2 * (R : Real) + 1) ^ M := by
    calc
      (1 : Real) = (1 : Real) ^ M := by simp
      _ <= (2 * (R : Real) + 1) ^ M := by gcongr
  have htwo : (2 : Real) ^ j <= (4 : Real) ^ M := by
    calc
      (2 : Real) ^ j <= (2 : Real) ^ (2 * M) := by gcongr; norm_num
      _ = (4 : Real) ^ M := by rw [pow_mul]; norm_num
  unfold decoderIntegerMagnitudeBudget
  calc
    (2 : Real) ^ j <= (4 : Real) ^ M := htwo
    _ = 1 * 1 * (4 : Real) ^ M := by ring
    _ <= (N : Real) * (2 * (R : Real) + 1) ^ M * (4 : Real) ^ M := by gcongr

theorem integerHornerSample_coefficient_product_abs_le
    (P : Set Nat) (N R M k j : Nat) (hj : j <= M) :
    abs (((sampleCount P N k : Int) * (2 : Int) ^ j : Int) : Real) <=
      decoderIntegerMagnitudeBudget N R M := by
  have hC : (sampleCount P N k : Real) <= (N : Real) := by
    exact_mod_cast sampleCount_le_sampleSize P N k
  have hC0 : (0 : Real) <= (sampleCount P N k : Real) := Nat.cast_nonneg _
  have hA : (1 : Real) <= 2 * (R : Real) + 1 := by
    have hR : (0 : Real) <= (R : Real) := Nat.cast_nonneg R
    linarith
  have hApow : (1 : Real) <= (2 * (R : Real) + 1) ^ M := by
    calc
      (1 : Real) = (1 : Real) ^ M := by simp
      _ <= (2 * (R : Real) + 1) ^ M := by gcongr
  have htwo : (2 : Real) ^ j <= (4 : Real) ^ M := by
    calc
      (2 : Real) ^ j <= (4 : Real) ^ j := by gcongr; norm_num
      _ <= (4 : Real) ^ M := by gcongr; norm_num
  simp only [Int.cast_mul, Int.cast_pow, Int.cast_natCast, Int.cast_ofNat,
    abs_mul, abs_pow, abs_of_nonneg hC0, abs_of_pos (show (0 : Real) < 2 by norm_num)]
  unfold decoderIntegerMagnitudeBudget
  calc
    (sampleCount P N k : Real) * (2 : Real) ^ j <= (N : Real) * (4 : Real) ^ M := by
      gcongr
    _ = (N : Real) * 1 * (4 : Real) ^ M := by ring
    _ <= (N : Real) * (2 * (R : Real) + 1) ^ M * (4 : Real) ^ M := by gcongr

theorem integerHornerSample_stored_bits_eventual
    (P : Set Nat) (h c : Real) (hh : 0 < h) (hc : 0 < c) :
    Filter.Eventually (fun N : Nat =>
      And (forall k j : Nat, j <= decoderRank c N ->
        (integerBitWidth ((sampleCount P N k : Int) * (2 : Int) ^ j) : Real) <=
          decoderBitConstant h c * Real.log (N : Real))
        (forall n j : Nat, j <= decoderRank c N + 1 ->
          (integerBitWidth
            ((integerHornerState (sampleCount P N) (-((2 * n + 1 : Nat) : Int))
              (decoderRank c N) j).twoPower : Int) : Real) <=
            decoderBitConstant h c * Real.log (N : Real))) atTop := by
  filter_upwards [decoder_budget_bits_eventual_bound h c hh hc, eventually_ge_atTop 1,
    (decoderRank_real_atTop c hc).eventually (eventually_ge_atTop 1)] with N hb hN hM
  have hMN : 1 <= decoderRank c N := by exact_mod_cast hM
  apply And.intro
  case left =>
    intro k j hj
    apply hb
    exact integerHornerSample_coefficient_product_abs_le P N (decoderRadius h N)
      (decoderRank c N) k j hj
  case right =>
    intro n j hj
    apply hb
    rw [integerHornerState_twoPower]
    push_cast
    rw [abs_pow, abs_of_pos (show (0 : Real) < 2 by norm_num)]
    exact decoder_pow_two_le_budget N (decoderRadius h N) (decoderRank c N) j hN (by omega)

theorem decoder_squared_budget_bits_eventual
    (h c : Real) (hh : 0 < h) (hc : 0 < c) :
    Filter.Eventually (fun N : Nat => forall z : Int,
      abs (z : Real) <= (decoderIntegerMagnitudeBudget N
        (decoderRadius h N) (decoderRank c N)) ^ 2 ->
      (integerBitWidth z : Real) <= 2 * decoderBitConstant h c * Real.log (N : Real)) atTop := by
  have hlogN : Tendsto (fun N : Nat => Real.log (N : Real)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [decoder_budget_log_eventual_bound h c hh hc,
    hlogN.eventually (eventually_ge_atTop 1)] with N hb hN
  intro z hz
  have hsq : 1 <= (decoderIntegerMagnitudeBudget N
      (decoderRadius h N) (decoderRank c N)) ^ 2 := by nlinarith [hb.1]
  have hbits := integerBitWidth_le_log z _ hsq hz
  rw [Real.log_pow] at hbits
  simp only [Nat.cast_ofNat, mul_div_assoc] at hbits
  have htwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hdiv1 :
      (Real.log (decoderIntegerMagnitudeBudget N (decoderRadius h N) (decoderRank c N)) /
        Real.log 2) * Real.log 2 =
      Real.log (decoderIntegerMagnitudeBudget N (decoderRadius h N) (decoderRank c N)) := by
    field_simp [ne_of_gt htwo]
  have hdiv2 : (((2 + c * h) / Real.log 2) * Real.log (N : Real)) * Real.log 2 =
      (2 + c * h) * Real.log (N : Real) := by field_simp [ne_of_gt htwo]
  have hquot :
      Real.log (decoderIntegerMagnitudeBudget N (decoderRadius h N) (decoderRank c N)) /
        Real.log 2 <= ((2 + c * h) / Real.log 2) * Real.log (N : Real) := by
    nlinarith [hb.2]
  unfold decoderBitConstant
  nlinarith

theorem integerSampleProbe_product_bits_eventual
    (P : Set Nat) (h c : Real) (hh : 0 < h) (hc : 0 < c) :
    Filter.Eventually (fun N : Nat => forall a b : Nat,
      a <= decoderRadius h N -> b <= decoderRadius h N ->
      (integerBitWidth (integerProbe (decoderRank c N) (sampleCount P N) a *
        integerProbe (decoderRank c N) (sampleCount P N) b) : Real) <=
        2 * decoderBitConstant h c * Real.log (N : Real)) atTop := by
  filter_upwards [decoder_squared_budget_bits_eventual h c hh hc,
    decoder_budget_log_eventual_bound h c hh hc] with N hb hbudget
  intro a b ha hble
  apply hb
  rw [Int.cast_mul, abs_mul]
  have hleft := integerSampleProbe_abs_le P N (decoderRank c N) (decoderRadius h N) a ha
  have hright := integerSampleProbe_abs_le P N (decoderRank c N) (decoderRadius h N) b hble
  have htwo : (2 : Real) ^ decoderRank c N <= (4 : Real) ^ decoderRank c N := by
    gcongr
    norm_num
  have hla : abs (integerProbe (decoderRank c N) (sampleCount P N) a : Real) <=
      decoderIntegerMagnitudeBudget N (decoderRadius h N) (decoderRank c N) := by
    exact hleft.trans (by unfold decoderIntegerMagnitudeBudget; gcongr)
  have hlb : abs (integerProbe (decoderRank c N) (sampleCount P N) b : Real) <=
      decoderIntegerMagnitudeBudget N (decoderRadius h N) (decoderRank c N) := by
    exact hright.trans (by unfold decoderIntegerMagnitudeBudget; gcongr)
  simpa only [pow_two] using mul_le_mul hla hlb (abs_nonneg _)
    (by linarith [hbudget.1] : 0 <= decoderIntegerMagnitudeBudget N
      (decoderRadius h N) (decoderRank c N))

end PrimeFactorOscillations.PrimeClassDecoder

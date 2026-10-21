/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.PrimeClassDecoderBitBudget

/-!
# Actual binary bit lengths for the finite prime decoder

The computable width is one plus the base-two logarithm of one plus
the absolute integer value. The same eventual threshold controls every
integer in the magnitude budget, hence all retained Horner values.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.PrimeClassDecoder

open Filter

def integerBitWidth (z : Int) : Nat := Nat.log 2 (z.natAbs + 1) + 1

noncomputable def decoderBitConstant (h c : Real) : Real :=
  (2 + c * h) / Real.log 2 + 2

theorem integerBitWidth_le_log (z : Int) (B : Real) (hB : 1 <= B)
    (hz : abs (z : Real) <= B) :
    (integerBitWidth z : Real) <= Real.log B / Real.log 2 + 2 := by
  let m : Nat := z.natAbs + 1
  let L : Nat := Nat.log 2 m
  have hm : Not (m = 0) := by dsimp [m]; omega
  have hpow : (2 : Real) ^ L <= (m : Real) := by
    exact_mod_cast Nat.pow_log_le_self 2 hm
  have hcast : (z.natAbs : Real) = abs (z : Real) := by
    rw [<- Int.cast_abs, <- Int.natCast_natAbs, Int.cast_natCast]
  have hmpos : (0 : Real) < (m : Real) := by
    exact_mod_cast (show 0 < m by omega)
  have hmle : (m : Real) <= 2 * B := by
    dsimp [m]
    push_cast
    rw [hcast]
    linarith
  have hlogL : (L : Real) * Real.log 2 <= Real.log (m : Real) := by
    have hlog := Real.log_le_log (pow_pos (by norm_num : (0 : Real) < 2) L) hpow
    simpa only [Real.log_pow] using hlog
  have hBpos : 0 < B := by linarith
  have hlogm : Real.log (m : Real) <= Real.log 2 + Real.log B := by
    have h := Real.log_le_log hmpos hmle
    rw [Real.log_mul (by norm_num : Not ((2 : Real) = 0)) (ne_of_gt hBpos)] at h
    exact h
  have htwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hdiv : (Real.log B / Real.log 2) * Real.log 2 = Real.log B := by
    field_simp [ne_of_gt htwo]
  change ((L + 1 : Nat) : Real) <= _
  push_cast
  nlinarith

theorem decoder_budget_bits_eventual_bound
    (h c : Real) (hh : 0 < h) (hc : 0 < c) :
    Filter.Eventually (fun N : Nat => forall z : Int,
      abs (z : Real) <= decoderIntegerMagnitudeBudget N (decoderRadius h N) (decoderRank c N) ->
      (integerBitWidth z : Real) <= decoderBitConstant h c * Real.log (N : Real)) atTop := by
  have hlogN : Tendsto (fun N : Nat => Real.log (N : Real)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [decoder_budget_log_eventual_bound h c hh hc,
    hlogN.eventually (eventually_ge_atTop 1)] with N hb hN
  intro z hz
  have hbits := integerBitWidth_le_log z _ hb.1 hz
  have htwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hdiv1 :
      (Real.log (decoderIntegerMagnitudeBudget N (decoderRadius h N) (decoderRank c N)) /
        Real.log 2) * Real.log 2 =
      Real.log (decoderIntegerMagnitudeBudget N (decoderRadius h N) (decoderRank c N)) := by
    field_simp [ne_of_gt htwo]
  have hdiv2 : (((2 + c * h) / Real.log 2) * Real.log (N : Real)) * Real.log 2 =
      (2 + c * h) * Real.log (N : Real) := by
    field_simp [ne_of_gt htwo]
  have hquot :
      Real.log (decoderIntegerMagnitudeBudget N (decoderRadius h N) (decoderRank c N)) /
        Real.log 2 <= ((2 + c * h) / Real.log 2) * Real.log (N : Real) := by
    nlinarith [hb.2]
  unfold decoderBitConstant
  nlinarith

theorem integerSampleProbe_bits_eventual
    (P : Set Nat) (h c : Real) (hh : 0 < h) (hc : 0 < c) :
    Filter.Eventually (fun N : Nat => forall n : Nat, n <= decoderRadius h N ->
      (integerBitWidth (integerProbe (decoderRank c N) (sampleCount P N) n) : Real) <=
        decoderBitConstant h c * Real.log (N : Real)) atTop := by
  filter_upwards [decoder_budget_bits_eventual_bound h c hh hc] with N hN
  intro n hn
  apply hN
  exact (integerSampleProbe_abs_le P N (decoderRank c N) (decoderRadius h N) n hn).trans
    (by unfold decoderIntegerMagnitudeBudget; gcongr; norm_num)

theorem integerHornerSample_bits_eventual
    (P : Set Nat) (h c : Real) (hh : 0 < h) (hc : 0 < c) :
    Filter.Eventually (fun N : Nat => forall n j ell : Nat,
      n <= decoderRadius h N -> j + ell <= decoderRank c N + 1 ->
      (integerBitWidth
        ((-((2 * n + 1 : Nat) : Int)) ^ ell *
          (integerHornerState (sampleCount P N)
            (-((2 * n + 1 : Nat) : Int)) (decoderRank c N) j).accumulator) : Real) <=
        decoderBitConstant h c * Real.log (N : Real)) atTop := by
  filter_upwards [decoder_budget_bits_eventual_bound h c hh hc] with N hN
  intro n j ell hn hj
  apply hN
  exact integerHornerSample_shifted_abs_le P N (decoderRank c N)
    (decoderRadius h N) n j ell hn hj

end PrimeFactorOscillations.PrimeClassDecoder

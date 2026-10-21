/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.PrimeClassDecoderExecutable
import PrimeFactorOscillations.Helpers.PrimeClassDecoderPreprocessingScale

/-!
# The complete arithmetic budget including selector preprocessing

The unit arithmetic model charges five operations per binary-log test,
a multiplications for the initial U^a, b+6 operations per forward-root
test, and twelve fixed setup/rank operations. Input count acquisition
is excluded. Preprocessing plus all Horner and adjacent tests is
eventually at most 31*R_N*M_N.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.PrimeClassDecoder

open Filter

def decoderPreprocessingOperations (h : Rat) (N : Nat) : Nat :=
  5 * (decoderBinaryLogState N (N + 1)).tests +
    5 * (decoderBinaryLogState (binaryCutoff N) (binaryCutoff N + 1)).tests +
      h.num.toNat +
        (h.den + 6) *
          (integerRootForward (binaryCutoff N ^ h.num.toNat) h.den 0
            (binaryCutoff N ^ h.num.toNat + 1)).tests + 12

theorem decoderPreprocessingOperations_le
    (h : Rat) (hh : 0 <= h) (N : Nat) :
    decoderPreprocessingOperations h N <=
      (h.num.toNat + h.den + 28) * (binaryCutoff N + decoderRadius (h : Real) N + 1) := by
  have hU : iteratedBinaryCutoff N <= binaryCutoff N := Nat.log_le_self 2 (binaryCutoff N)
  have hroot := fastIntegerRootCutoff_tests_le (binaryCutoff N ^ h.num.toNat)
    h.den (Nat.succ_le_of_lt (Rat.den_pos h))
  change (integerRootForward (binaryCutoff N ^ h.num.toNat) h.den 0
    (binaryCutoff N ^ h.num.toNat + 1)).tests <= rationalDecoderRadiusFromRat h N + 1 at hroot
  rw [rationalDecoderRadiusFromRat_eq h hh] at hroot
  have hscaled := Nat.mul_le_mul_left (h.den + 6) hroot
  unfold decoderPreprocessingOperations
  rw [decoderBinaryCutoff_tests, decoderBinaryCutoff_tests]
  change 5 * (binaryCutoff N + 1) + 5 * (iteratedBinaryCutoff N + 1) + h.num.toNat +
    (h.den + 6) *
      (integerRootForward (binaryCutoff N ^ h.num.toNat) h.den 0
        (binaryCutoff N ^ h.num.toNat + 1)).tests + 12 <= _
  nlinarith

theorem decoderPreprocessingOperations_eventual
    (h c : Rat) (hh : 0 < h) (hc : 0 < c) :
    Filter.Eventually (fun N : Nat => decoderPreprocessingOperations h N <=
      decoderRadius (h : Real) N * decoderRank (c : Real) N) atTop := by
  have hhR : (0 : Real) < (h : Real) := by exact_mod_cast hh
  have hcR : (0 : Real) < (c : Real) := by exact_mod_cast hc
  filter_upwards [preprocessing_eventually_le_evaluation_budget (h : Real) (c : Real)
    ((h.num.toNat + h.den + 28 : Nat) : Real) hhR hcR] with N hN
  have hbound : (decoderPreprocessingOperations h N : Real) <=
      ((h.num.toNat + h.den + 28 : Nat) : Real) *
        ((binaryCutoff N : Real) + (decoderRadius (h : Real) N : Real) + 1) := by
    exact_mod_cast decoderPreprocessingOperations_le h (le_of_lt hh) N
  have hresult := hbound.trans hN
  exact_mod_cast hresult

theorem decoder_complete_arithmetic_operations_eventual
    (h c : Rat) (hh : 0 < h) (hc : 0 < c) :
    Filter.Eventually (fun N : Nat =>
      decoderPreprocessingOperations h N +
        integerHornerCompleteOperations (decoderRadius (h : Real) N) (decoderRank (c : Real) N) <=
          31 * decoderRadius (h : Real) N * decoderRank (c : Real) N) atTop := by
  have hhR : (0 : Real) < (h : Real) := by exact_mod_cast hh
  have hcR : (0 : Real) < (c : Real) := by exact_mod_cast hc
  filter_upwards [decoderPreprocessingOperations_eventual h c hh hc,
    (decoderRadius_real_atTop (h : Real) hhR).eventually (eventually_ge_atTop 1),
    (decoderRank_real_atTop (c : Real) hcR).eventually (eventually_ge_atTop 1)] with N hp hR hM
  have hRN : 1 <= decoderRadius (h : Real) N := by exact_mod_cast hR
  have hMN : 1 <= decoderRank (c : Real) N := by exact_mod_cast hM
  have heval := integerHorner_complete_operation_bound _ _ hRN hMN
  nlinarith

end PrimeFactorOscillations.PrimeClassDecoder

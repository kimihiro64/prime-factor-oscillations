/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.PrimeClassDecoderExecutable
import PrimeFactorOscillations.Helpers.PrimeClassDecoderPreprocessingBits

/-!
# Actual preprocessing values retain logarithmic binary width

The certificate covers binary-log states, fixed parameter integers,
all root-search powers through the final failed test, both rank
multiplications and their integer quotient.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.PrimeClassDecoder

open Filter

theorem preprocessing_root_power_le
    (U a b t k : Nat) (hU : 1 <= U) (ht : t <= U ^ a + 1) (hk : k <= b + 1) :
    t ^ k <= (U + 1) ^ ((a + 1) * (b + 1)) := by
  have hC : 1 <= U + 1 := by omega
  have hpow : U ^ a <= (U + 1) ^ a := by gcongr; omega
  have hone : 1 <= (U + 1) ^ a := by
    calc
      1 = (1 : Nat) ^ a := by simp
      _ <= (U + 1) ^ a := by gcongr
  have hbase : t <= (U + 1) ^ (a + 1) := by
    rw [pow_succ]
    nlinarith
  have hbase1 : 1 <= (U + 1) ^ (a + 1) := by
    calc
      1 = (1 : Nat) ^ (a + 1) := by simp
      _ <= (U + 1) ^ (a + 1) := by gcongr
  calc
    t ^ k <= ((U + 1) ^ (a + 1)) ^ k := by gcongr
    _ <= ((U + 1) ^ (a + 1)) ^ (b + 1) := by gcongr
    _ = (U + 1) ^ ((a + 1) * (b + 1)) := by rw [pow_mul]

theorem preprocessing_linear_value_le
    (U f K E : Nat) (hf : f <= K) (hE : 1 <= E) :
    f * U <= K * (U + 1) ^ E := by
  have hbase : 1 <= U + 1 := by omega
  have hpow : U <= (U + 1) ^ E := by
    calc
      U <= U + 1 := by omega
      _ = (U + 1) ^ 1 := by simp
      _ <= (U + 1) ^ E := by gcongr
  exact Nat.mul_le_mul hf hpow

def decoderPreprocessingScalar (h c : Rat) : Nat :=
  h.num.toNat + h.den + c.num.toNat + c.den + 1

def decoderPreprocessingExponent (h : Rat) : Nat :=
  (h.num.toNat + 1) * (h.den + 1)

structure DecoderPreprocessingBitCertificate (h c : Rat) (N : Nat) : Prop where
  binary_values : forall t : Nat, t <= N + 1 ->
    (integerBitWidth (t : Int) : Real) <=
      decoderBitConstant (h : Real) (c : Real) * Real.log (N : Real)
  fixed_values : forall t : Nat, t <= decoderPreprocessingScalar h c ->
    (integerBitWidth (t : Int) : Real) <=
      decoderBitConstant (h : Real) (c : Real) * Real.log (N : Real)
  root_values : forall t k : Nat,
    t <= binaryCutoff N ^ h.num.toNat + 1 -> k <= h.den + 1 ->
    (integerBitWidth (t ^ k : Int) : Real) <=
      decoderBitConstant (h : Real) (c : Real) * Real.log (N : Real)
  rank_numerator :
    (integerBitWidth ((c.num.toNat * binaryCutoff N : Nat) : Int) : Real) <=
      decoderBitConstant (h : Real) (c : Real) * Real.log (N : Real)
  rank_denominator :
    (integerBitWidth ((c.den * iteratedBinaryCutoff N : Nat) : Int) : Real) <=
      decoderBitConstant (h : Real) (c : Real) * Real.log (N : Real)
  rank_quotient :
    (integerBitWidth (executableRationalRank c N : Int) : Real) <=
      decoderBitConstant (h : Real) (c : Real) * Real.log (N : Real)

theorem decoder_preprocessing_bit_certificate
    (h c : Rat) (hh : 0 < h) (hc : 0 < c) :
    Filter.Eventually (fun N : Nat => DecoderPreprocessingBitCertificate h c N) atTop := by
  have hhR : (0 : Real) < (h : Real) := by exact_mod_cast hh
  have hcR : (0 : Real) < (c : Real) := by exact_mod_cast hc
  let K := decoderPreprocessingScalar h c
  let E := decoderPreprocessingExponent h
  have hK : 1 <= K := by dsimp [K, decoderPreprocessingScalar]; omega
  have hE : 1 <= E := by dsimp [E, decoderPreprocessingExponent]; nlinarith
  have hnum : c.num.toNat <= K := by dsimp [K, decoderPreprocessingScalar]; omega
  have hden : c.den <= K := by dsimp [K, decoderPreprocessingScalar]; omega
  filter_upwards [preprocessing_polynomial_bits_eventual (h : Real) (c : Real) K E hhR hcR hK,
    binaryCutoff_atTop.eventually (eventually_ge_atTop 1)] with N hb hU
  have hwidth : forall t : Nat, t <= N + 1 + K * (binaryCutoff N + 1) ^ E ->
      (integerBitWidth (t : Int) : Real) <=
        decoderBitConstant (h : Real) (c : Real) * Real.log (N : Real) := by
    intro t ht
    apply hb (t : Int)
    push_cast
    rw [abs_of_nonneg (Nat.cast_nonneg t : (0 : Real) <= (t : Real))]
    exact_mod_cast ht
  have hpoly1 : 1 <= (binaryCutoff N + 1) ^ E := by
    calc
      1 = (1 : Nat) ^ E := by simp
      _ <= (binaryCutoff N + 1) ^ E := by gcongr; omega
  have hnumBound := preprocessing_linear_value_le (binaryCutoff N) c.num.toNat K E hnum hE
  have hdenBound := preprocessing_linear_value_le (binaryCutoff N) c.den K E hden hE
  have hV : iteratedBinaryCutoff N <= binaryCutoff N := Nat.log_le_self 2 (binaryCutoff N)
  have hdenActual : c.den * iteratedBinaryCutoff N <= K * (binaryCutoff N + 1) ^ E :=
    (Nat.mul_le_mul_left c.den hV).trans hdenBound
  apply DecoderPreprocessingBitCertificate.mk
  case binary_values =>
    intro t ht
    exact hwidth t (by omega)
  case fixed_values =>
    intro t ht
    have htK : t <= K := ht
    have hKpoly : K <= K * (binaryCutoff N + 1) ^ E := by
      calc
        K = K * 1 := by simp
        _ <= K * (binaryCutoff N + 1) ^ E := Nat.mul_le_mul_left K hpoly1
    exact hwidth t (by omega)
  case root_values =>
    intro t k ht hk
    have hroot := preprocessing_root_power_le (binaryCutoff N) h.num.toNat h.den t k hU ht hk
    have hrootE : t ^ k <= (binaryCutoff N + 1) ^ E := hroot
    have hscale : (binaryCutoff N + 1) ^ E <= K * (binaryCutoff N + 1) ^ E := by
      simpa only [one_mul] using Nat.mul_le_mul_right ((binaryCutoff N + 1) ^ E) hK
    have hbound : t ^ k <= N + 1 + K * (binaryCutoff N + 1) ^ E :=
      hrootE.trans (hscale.trans (Nat.le_add_left _ _))
    simpa only [Nat.cast_pow] using hwidth (t ^ k) hbound
  case rank_numerator =>
    exact hwidth (c.num.toNat * binaryCutoff N) (by omega)
  case rank_denominator =>
    exact hwidth (c.den * iteratedBinaryCutoff N) (by omega)
  case rank_quotient =>
    have hq : executableRationalRank c N =
        (c.num.toNat * binaryCutoff N) / (c.den * iteratedBinaryCutoff N) := by
      simp only [executableRationalRank, executableBinaryCutoff_eq]
      rfl
    have hqBound : executableRationalRank c N <= N + 1 + K * (binaryCutoff N + 1) ^ E := by
      rw [hq]
      exact (Nat.div_le_self (c.num.toNat * binaryCutoff N)
        (c.den * iteratedBinaryCutoff N)).trans (by omega)
    exact hwidth (executableRationalRank c N) hqBound

end PrimeFactorOscillations.PrimeClassDecoder

/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.FiniteFieldIntegerNativeMetric

/-!
# Recovering the endpoint-product character from a native probability weight

For every sufficiently large prime field, squaring the exact centered
native scalar weight removes the gap square and recovers the character
of the negative endpoint product. All opening masks are checked directly.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace PrimeFactorOscillations.FiniteFieldIntegerSignature
open IntegerQuadraticCharacter FiniteFieldIntegerCharacter

theorem real_kernel_square_of_nonzero (D : Int) (p : Nat) [Fact (Nat.Prime p)]
    (hp2 : 2 < p) (hD : Not ((D : ZMod p) = 0)) :
    (numeratorKernel D p).re ^ 2 = 1 := by
  rw [numerator_kernel_prime D p (by omega)]
  exact_mod_cast quadraticChar_sq_one hD

theorem native_weight_large_prime_trace (n h p : Nat) [Fact (Nat.Prime p)]
    (hn : 0 < n) (hp5 : 5 <= p) (hpnh : n + h < p) :
    ((p : Real) - 3) * integerNativeWeight n h p - ((p : Real) - 1) =
      nativeTrace n h p := by
  have hmod (N : Nat) (hN : 0 < N) (hNp : N < p) :
      Not ((N : ZMod p) = 0) := by
    intro hz
    exact (Nat.not_dvd_of_pos_of_lt hN hNp) ((ZMod.natCast_eq_zero_iff N p).mp hz)
  have hn0 := hmod n hn (by omega)
  have hnh0 := hmod (n + h) (by omega) hpnh
  have hnneg : Not ((n : ZMod p) = -(h : ZMod p)) := by
    intro he
    apply hnh0
    simp only [Nat.cast_add, he, neg_add_cancel]
  have hs := FiniteField.QuadraticPairTwistEuler.traceFreePairWeight_scalar
    (n : ZMod p) (h : ZMod p) hn0 hnneg
  have hden : Not ((p : Real) - 3 = 0) := by
    have hpR : (5 : Real) <= p := by exact_mod_cast hp5
    linarith only [hpR]
  have htrace : nativeTrace n h p =
      FiniteField.QuadraticPairTwistEuler.characterA (n : ZMod p) (h : ZMod p) +
        FiniteField.QuadraticPairTwistEuler.characterB (n : ZMod p) (h : ZMod p) := by
    have ha := congrArg Complex.re (integer_characterA h n p (by omega))
    have hb := congrArg Complex.re (integer_characterB h n p (by omega))
    simp only [Complex.ofReal_re] at ha hb
    unfold nativeTrace
    rw [<- ha, <- hb]
  have hp : Nat.Prime p := Fact.out
  simp only [integerNativeWeight, dite_eq_left hp]
  rw [hs, htrace]
  simp only [ZMod.card]
  field_simp [hden]
  ring

theorem native_trace_endpoint_readout (n h p : Nat) [Fact (Nat.Prime p)]
    (hn : 0 < n) (hh : 0 < h) (hp2 : 2 < p) (hpnh : n + h < p) :
    nativeTrace n h p ^ 2 =
      2 + 2 * (numeratorKernel (-((n : Int) * ((n + h : Nat) : Int))) p).re := by
  have hmod (N : Nat) (hN : 0 < N) (hNp : N < p) :
      Not ((N : ZMod p) = 0) := by
    intro hz
    exact (Nat.not_dvd_of_pos_of_lt hN hNp) ((ZMod.natCast_eq_zero_iff N p).mp hz)
  have hn0 := hmod n hn (by omega)
  have hh0 := hmod h hh (by omega)
  have hnh0 := hmod (n + h) (by omega) hpnh
  have hA : Not (((-((h : Int) * (n : Int)) : Int) : ZMod p) = 0) := by
    simpa only [Int.cast_neg, Int.cast_mul, Int.cast_natCast] using
      neg_ne_zero.mpr (mul_ne_zero hh0 hn0)
  have hB : Not (((((h : Int) * ((n + h : Nat) : Int)) : Int) : ZMod p) = 0) := by
    simpa only [Int.cast_mul, Int.cast_natCast] using mul_ne_zero hh0 hnh0
  have hH : Not (((h : Int) : ZMod p) = 0) := by
    simpa only [Int.cast_natCast] using hh0
  have hsA := real_kernel_square_of_nonzero (-((h : Int) * (n : Int))) p hp2 hA
  have hsB := real_kernel_square_of_nonzero ((h : Int) * ((n + h : Nat) : Int)) p hp2 hB
  have hsH := real_kernel_square_of_nonzero (h : Int) p hp2 hH
  have hprod : (-((h : Int) * (n : Int))) * ((h : Int) * ((n + h : Nat) : Int)) =
      ((h : Int) * (h : Int)) * (-((n : Int) * ((n + h : Nat) : Int))) := by ring
  have hab : (numeratorKernel (-((h : Int) * (n : Int))) p).re *
      (numeratorKernel ((h : Int) * ((n + h : Nat) : Int)) p).re =
      (numeratorKernel (-((n : Int) * ((n + h : Nat) : Int))) p).re := by
    rw [<- real_kernel_mul, hprod, real_kernel_mul, real_kernel_mul,
      <- pow_two, hsH, one_mul]
  unfold nativeTrace
  nlinarith only [hsA, hsB, hab]

theorem native_weight_endpoint_readout (n h p : Nat) [Fact (Nat.Prime p)]
    (hn : 0 < n) (hh : 0 < h) (hp5 : 5 <= p) (hpnh : n + h < p) :
    (((p : Real) - 3) * integerNativeWeight n h p - ((p : Real) - 1)) ^ 2 =
      2 + 2 * (numeratorKernel (-((n : Int) * ((n + h : Nat) : Int))) p).re := by
  rw [native_weight_large_prime_trace n h p hn hp5 hpnh]
  exact native_trace_endpoint_readout n h p hn hh (by omega) hpnh

theorem native_weight_match_product_one (n h m k p : Nat) [Fact (Nat.Prime p)]
    (hn : 0 < n) (hh : 0 < h) (hm : 0 < m) (hk : 0 < k)
    (hp5 : 5 <= p) (hpnh : n + h < p) (hpmk : m + k < p)
    (hmatch : integerNativeWeight n h p = integerNativeWeight m k p) :
    (numeratorKernel ((n * (n + h) * m * (m + k) : Nat) : Int) p).re = 1 := by
  have hN := native_weight_endpoint_readout n h p hn hh hp5 hpnh
  have hM := native_weight_endpoint_readout m k p hm hk hp5 hpmk
  rw [hmatch] at hN
  have heq : (numeratorKernel (-((n : Int) * ((n + h : Nat) : Int))) p).re =
      (numeratorKernel (-((m : Int) * ((m + k : Nat) : Int))) p).re := by
    linarith only [hN, hM]
  have hn0 : Not ((n : ZMod p) = 0) := by
    intro hz
    exact (Nat.not_dvd_of_pos_of_lt hn (by omega)) ((ZMod.natCast_eq_zero_iff n p).mp hz)
  have hnh0 : Not (((n + h : Nat) : ZMod p) = 0) := by
    intro hz
    exact (Nat.not_dvd_of_pos_of_lt (by omega) hpnh)
      ((ZMod.natCast_eq_zero_iff (n + h) p).mp hz)
  have hD : Not (((-((n : Int) * ((n + h : Nat) : Int)) : Int) : ZMod p) = 0) := by
    simpa only [Int.cast_neg, Int.cast_mul, Int.cast_natCast] using
      neg_ne_zero.mpr (mul_ne_zero hn0 hnh0)
  have hs := real_kernel_square_of_nonzero (-((n : Int) * ((n + h : Nat) : Int))) p
    (by omega) hD
  have hprod : ((n * (n + h) * m * (m + k) : Nat) : Int) =
      (-((n : Int) * ((n + h : Nat) : Int))) *
        (-((m : Int) * ((m + k : Nat) : Int))) := by
    push_cast
    ring
  rw [hprod, real_kernel_mul, <- heq, <- pow_two, hs]

end PrimeFactorOscillations.FiniteFieldIntegerSignature

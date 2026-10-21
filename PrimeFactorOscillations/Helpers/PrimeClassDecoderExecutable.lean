/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.PrimeClassDecoderBinaryAlgorithm
import PrimeFactorOscillations.Helpers.PrimeClassDecoderRationalProgram

/-!
# The decoder using only integer arithmetic and observed counts

The program computes both binary cutoffs by division, its radius by the
forward root search, and its rank by two integer multiplications and
division. It agrees with the analytic decoder on all natural inputs.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.PrimeClassDecoder

theorem natFloor_rat_div (A B : Nat) :
    Nat.floor ((A : Rat) / (B : Rat)) = A / B := by
  by_cases hB : B = 0
  case pos => simp [hB]
  case neg =>
    have hBp : 0 < B := Nat.pos_of_ne_zero hB
    have hBr : (0 : Rat) < (B : Rat) := by exact_mod_cast hBp
    apply (Nat.floor_eq_iff (div_nonneg (Nat.cast_nonneg A) (Nat.cast_nonneg B))).mpr
    have hlow : (A / B) * B <= A := Nat.div_mul_le_self A B
    have hhigh : A < (A / B + 1) * B := by
      have hrem := Nat.mod_lt A hBp
      have hid := Nat.mod_add_div A B
      nlinarith
    have hlowQ : ((A / B : Nat) : Rat) * (B : Rat) <= (A : Rat) := by exact_mod_cast hlow
    have hhighQ : (A : Rat) < (((A / B : Nat) : Rat) + 1) * (B : Rat) := by
      exact_mod_cast hhigh
    have hcancel : ((A : Rat) / (B : Rat)) * (B : Rat) = (A : Rat) := by
      field_simp [ne_of_gt hBr]
    exact And.intro (by nlinarith) (by nlinarith)

theorem rationalDecoderRank_eq_natural_quotient (c : Rat) (hc : 0 <= c) (N : Nat) :
    rationalDecoderRank c N =
      (c.num.toNat * binaryCutoff N) / (c.den * iteratedBinaryCutoff N) := by
  have hnum : (c.num.toNat : Rat) = (c.num : Rat) := by
    exact_mod_cast Int.toNat_of_nonneg (Rat.num_nonneg.mpr hc)
  have hrep : c = (c.num.toNat : Rat) / (c.den : Rat) := by
    calc
      c = (c.num : Rat) / (c.den : Rat) := (Rat.num_div_den c).symm
      _ = (c.num.toNat : Rat) / (c.den : Rat) := by rw [hnum]
  by_cases hV : iteratedBinaryCutoff N = 0
  case pos => simp [rationalDecoderRank, hV]
  case neg =>
    have hden : Not ((c.den : Rat) = 0) := Nat.cast_ne_zero.mpr (Rat.den_nz c)
    have hVQ : Not ((iteratedBinaryCutoff N : Rat) = 0) := Nat.cast_ne_zero.mpr hV
    have heq :
        c * ((binaryCutoff N : Rat) / (iteratedBinaryCutoff N : Rat)) =
        ((c.num.toNat * binaryCutoff N : Nat) : Rat) /
          ((c.den * iteratedBinaryCutoff N : Nat) : Rat) := by
      calc
        c * ((binaryCutoff N : Rat) / (iteratedBinaryCutoff N : Rat)) =
            ((c.num.toNat : Rat) / (c.den : Rat)) *
              ((binaryCutoff N : Rat) / (iteratedBinaryCutoff N : Rat)) :=
          congrArg (fun q : Rat =>
            q * ((binaryCutoff N : Rat) / (iteratedBinaryCutoff N : Rat))) hrep
        _ = _ := by
          push_cast
          field_simp [hden, hVQ]
    unfold rationalDecoderRank
    rw [heq, natFloor_rat_div]

def executableRationalRank (c : Rat) (N : Nat) : Nat :=
  let U := executableBinaryCutoff N
  let V := executableBinaryCutoff U
  (c.num.toNat * U) / (c.den * V)

def executableIntegerPrimeDecoder (h c : Rat) (N : Nat) (C : Nat -> Nat) : Finset Nat :=
  let U := executableBinaryCutoff N
  let V := executableBinaryCutoff U
  let M := (c.num.toNat * U) / (c.den * V)
  let R := fastIntegerRootCutoff (U ^ h.num.toNat) h.den
  integerPrimeDecoder R M C

theorem executableRationalRank_eq (c : Rat) (hc : 0 <= c) (N : Nat) :
    executableRationalRank c N = decoderRank (c : Real) N := by
  simp only [executableRationalRank, executableBinaryCutoff_eq]
  change (c.num.toNat * binaryCutoff N) / (c.den * iteratedBinaryCutoff N) = _
  rw [<- rationalDecoderRank_eq_natural_quotient c hc N]
  exact rationalDecoderRank_eq c hc N

theorem executableIntegerPrimeDecoder_eq
    (h c : Rat) (hc : 0 <= c) (N : Nat) (C : Nat -> Nat) :
    executableIntegerPrimeDecoder h c N C = rationalIntegerPrimeDecoder h c N C := by
  unfold executableIntegerPrimeDecoder rationalIntegerPrimeDecoder
    rationalDecoderRadiusFromRat fastRationalDecoderRadius
  simp only [executableBinaryCutoff_eq]
  rw [rationalDecoderRank_eq_natural_quotient c hc N]
  rfl

end PrimeFactorOscillations.PrimeClassDecoder

namespace PrimeFactorOscillations.PrimeClassSampling

open Filter
open PrimeFactorOscillations.PrimeClassDecoder

theorem executable_integer_prime_decoding
    (P : Set Nat) (sigma : Real) (h c : Rat) (hs : 0 < sigma) (hs1 : sigma < 1)
    (hsum : Summable (classPowerWeight P sigma))
    (hh : 0 < h) (hc : 0 < c) (hpower : (h : Real) * sigma < 1)
    (hcBound : (c : Real) < (1 - sigma) / (h : Real)) :
    Filter.Eventually (fun N : Nat =>
      And (FiniteIntegerDecoderCertificate P N (h : Real) (c : Real))
        (executableIntegerPrimeDecoder h c N (sampleCount P N) =
          primeClassPrefix P (rationalDecoderRadiusFromRat h N + 1))) atTop := by
  filter_upwards [rational_integer_prime_decoding P sigma h c hs hs1 hsum hh hc hpower hcBound]
    with N hN
  apply And.intro hN.1
  rw [executableIntegerPrimeDecoder_eq h c (le_of_lt hc)]
  exact hN.2

end PrimeFactorOscillations.PrimeClassSampling

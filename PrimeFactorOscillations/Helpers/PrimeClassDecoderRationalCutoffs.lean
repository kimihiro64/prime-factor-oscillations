/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.PrimeClassDecoderErrorExponents

/-!
# Computable rational-parameter selectors

The radius is a bounded search for an integer root, using only natural
powers and comparisons. The rank uses the computable rational floor.
They agree exactly with the analytic real selectors, including small
inputs and a zero iterated logarithmic denominator.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.PrimeClassDecoder

def integerRootCutoff (Y b : Nat) : Nat :=
  Nat.findGreatest (fun r => r ^ b <= Y) Y

def rationalDecoderRank (c : Rat) (N : Nat) : Nat :=
  Nat.floor (c * ((binaryCutoff N : Rat) / (iteratedBinaryCutoff N : Rat)))

def rationalDecoderRadius (a b N : Nat) : Nat :=
  integerRootCutoff (binaryCutoff N ^ a) b

theorem integerRootCutoff_pow_le (Y b : Nat) (hb : 1 <= b) :
    (integerRootCutoff Y b) ^ b <= Y := by
  unfold integerRootCutoff
  apply Nat.findGreatest_spec (P := fun r => r ^ b <= Y) (m := 0) (Nat.zero_le Y)
  simp [zero_pow (by omega : Not (b = 0))]

theorem integerRootCutoff_maximal (Y b r : Nat) (hb : 1 <= b) (hr : r ^ b <= Y) :
    r <= integerRootCutoff Y b := by
  have hrY : r <= Y := (Nat.le_self_pow (by omega : Not (b = 0)) r).trans hr
  exact Nat.le_findGreatest hrY hr

theorem integerRootCutoff_eq_floor (Y b : Nat) (hb : 1 <= b) :
    integerRootCutoff Y b = Nat.floor ((Y : Real) ^ (1 / (b : Real))) := by
  let X : Real := (Y : Real) ^ (1 / (b : Real))
  have hbR : (0 : Real) < (b : Real) := by exact_mod_cast (show 0 < b by omega)
  have hX : 0 <= X := Real.rpow_nonneg (Nat.cast_nonneg Y) _
  have hXpow : X ^ b = (Y : Real) := by
    dsimp [X]
    rw [<- Real.rpow_natCast, <- Real.rpow_mul (Nat.cast_nonneg Y)]
    have he : (1 / (b : Real)) * (b : Real) = 1 := by field_simp [ne_of_gt hbR]
    rw [he, Real.rpow_one]
  have hroot : (integerRootCutoff Y b : Real) ^ b <= (Y : Real) := by
    exact_mod_cast integerRootCutoff_pow_le Y b hb
  change integerRootCutoff Y b = Nat.floor X
  symm
  apply (Nat.floor_eq_iff hX).mpr
  apply And.intro
  case left =>
    by_contra hnot
    have hlt : X < (integerRootCutoff Y b : Real) := lt_of_not_ge hnot
    have hstrict : X ^ b < (integerRootCutoff Y b : Real) ^ b := by
      gcongr
    rw [hXpow] at hstrict
    linarith
  case right =>
    by_contra hnot
    have hge : (integerRootCutoff Y b : Real) + 1 <= X := le_of_not_gt hnot
    have hpow : ((integerRootCutoff Y b : Real) + 1) ^ b <= X ^ b := by
      gcongr
    rw [hXpow] at hpow
    have hnext : (integerRootCutoff Y b + 1) ^ b <= Y := by exact_mod_cast hpow
    have hmax := integerRootCutoff_maximal Y b (integerRootCutoff Y b + 1) hb hnext
    omega

theorem rationalDecoderRank_eq (c : Rat) (hc : 0 <= c) (N : Nat) :
    rationalDecoderRank c N = decoderRank (c : Real) N := by
  let q : Rat := c * ((binaryCutoff N : Rat) / (iteratedBinaryCutoff N : Rat))
  have hq : 0 <= q := mul_nonneg hc (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  have heq : (q : Real) = (c : Real) *
      ((binaryCutoff N : Real) / (iteratedBinaryCutoff N : Real)) := by
    dsimp [q]
    push_cast
    rfl
  unfold rationalDecoderRank decoderRank
  rw [<- heq]
  change Nat.floor q = Nat.floor (q : Real)
  symm
  apply (Nat.floor_eq_iff (Rat.cast_nonneg.mpr hq)).mpr
  have hlow : ((Nat.floor q : Nat) : Rat) <= q := Nat.floor_le hq
  have hhigh : q < ((Nat.floor q : Nat) : Rat) + 1 := Nat.lt_floor_add_one q
  exact And.intro (by exact_mod_cast hlow) (by exact_mod_cast hhigh)

theorem rationalDecoderRadius_eq (a b N : Nat) (hb : 1 <= b) :
    rationalDecoderRadius a b N = decoderRadius ((a : Real) / (b : Real)) N := by
  unfold rationalDecoderRadius decoderRadius
  rw [integerRootCutoff_eq_floor _ b hb]
  congr 1
  push_cast
  rw [<- Real.rpow_natCast, <- Real.rpow_mul (Nat.cast_nonneg (binaryCutoff N))]
  congr 1
  ring

end PrimeFactorOscillations.PrimeClassDecoder

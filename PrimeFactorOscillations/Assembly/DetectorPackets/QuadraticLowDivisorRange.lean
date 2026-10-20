/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Assembly.DetectorPackets.QuadraticInverseBand
import PrimeFactorOscillations.Assembly.DetectorPackets.QuadraticInverseUnit
import PrimeFactorOscillations.Proof.DetectorPackets.QuadraticDyadicCover

/-!
# QuadraticLowDivisorRange

Maintained extraction of completed detector/packet proof components.
All original theorem hypotheses and retained proof bodies are preserved.
This module alone asserts no improved zero-free boundary.
-/

set_option autoImplicit false
set_option Elab.async false

/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described by LICENSE.
Authors: Prime Factor Oscillations contributors
-/


noncomputable section
open scoped BigOperators Classical

namespace PrimeFactorOscillations.QuadraticLowDivisorRange

open QuadraticGaussCoefficient QuadraticDivisorMean IntegerQuadraticPrefix
open QuadraticProductDivisor QuadraticProductBand QuadraticDyadicCover

def divisorMean (R S T : Finset Nat) (a b : Nat -> Complex) (d : Nat) : Real :=
  R.sum (fun r => norm (divisorRow d S T a b r))

def lowDivisorMean (Z : Nat) (R S T : Finset Nat) (a b : Nat -> Complex) : Real :=
  (Finset.Icc 1 Z).sum (divisorMean R S T a b)

def dyadicPiece (R S T : Finset Nat) (a b : Nat -> Complex) (i : Nat) : Real :=
  if i = 0 then divisorMean R S T a b 1
  else productBandMean (2 ^ (i - 1)) R S T a b

def envelope (C eps : Real) (M N1 N2 L1 L2 : Nat) (U : Real)
    (S T : Finset Nat) (a b : Nat -> Complex) : Real :=
  C * ((max N1 N2 : Nat) : Real) ^ eps *
    Real.sqrt ((L1 : Real) * (L2 : Real)) * (1 / U) *
    Real.sqrt (prefixNorm M (N1 / L1) * maskedMass 1 S a) *
    Real.sqrt (prefixNorm M (N2 / L2) * maskedMass 1 T b)

theorem envelope_mono (C1 C2 eps : Real) (M N1 N2 L1 L2 : Nat) (U : Real)
    (S T : Finset Nat) (a b : Nat -> Complex) (hC : C1 <= C2) (hU : 0 < U) :
    envelope C1 eps M N1 N2 L1 L2 U S T a b <=
      envelope C2 eps M N1 N2 L1 L2 U S T a b := by
  unfold envelope
  apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
  apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
  apply mul_le_mul_of_nonneg_right _ (show 0 <= 1 / U by positivity)
  apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
  exact mul_le_mul_of_nonneg_right hC
    (Real.rpow_nonneg (Nat.cast_nonneg _) _)

theorem lowMean_le_pieces (Z : Nat) (R S T : Finset Nat) (a b : Nat -> Complex)
    (hZ : 0 < Z) :
    lowDivisorMean Z R S T a b <=
      (Finset.range (Z.log2 + 2)).sum (dyadicPiece R S T a b) := by
  have hn (d : Nat) : 0 <= divisorMean R S T a b d :=
    Finset.sum_nonneg (fun r hr => norm_nonneg _)
  have h := cutoff_sum_le (divisorMean R S T a b) Z hZ hn
  have hPieces :
      (Finset.range (Z.log2 + 2)).sum (dyadicPiece R S T a b) =
        divisorMean R S T a b 1 +
        (Finset.range (Z.log2 + 1)).sum
          (fun k => productBandMean (2 ^ k) R S T a b) := by
    rw [Finset.sum_range_succ']
    simp only [dyadicPiece, Nat.add_one_ne_zero, ite_false, Nat.add_sub_cancel_right,
      ite_true]
    exact add_comm _ _
  rw [hPieces]
  exact h

theorem low_inverse_divisor_mean (eps : Real) (heps : 0 < eps) :
    exists C : Real, 0 < C /\
      forall (Z M N1 N2 : Nat) (k1 k2 : Int) (R S T : Finset Nat)
        (a b : Nat -> Complex), 0 < Z -> 0 < N1 -> 0 < N2 ->
      (forall r, Membership.mem R r -> Membership.mem (columns M) r) ->
      (forall n, Membership.mem S n -> Membership.mem (columns N1) n) ->
      (forall m, Membership.mem T m -> Membership.mem (columns N2) m) ->
      exists L1 L2 : Nat, 0 < L1 /\ 0 < L2 /\ L1 * L2 <= 2 * Z /\
      forall U : Real, 0 < U ->
      (forall n, Membership.mem S n -> U <= (n : Real)) ->
      (forall m, Membership.mem T m -> U <= (m : Real)) ->
      lowDivisorMean Z R S T (inverseCoefficient a k1) (inverseCoefficient b k2) <=
        ((Z.log2 + 2 : Nat) : Real) *
          envelope C eps M N1 N2 L1 L2 U S T a b := by
  choose Cb hCb hb using QuadraticInverseBand.inverse_product_divisor_mean eps heps
  choose Cu hCu hu using QuadraticInverseUnit.inverse_unit_divisor_mean eps heps
  let C := max Cb Cu
  have hC : 0 < C := lt_of_lt_of_le hCb (le_max_left _ _)
  refine Exists.intro C (And.intro hC ?_)
  intro Z M N1 N2 k1 k2 R S T a b hZ hN1 hN2 hR hS hT
  let aa := inverseCoefficient a k1
  let bb := inverseCoefficient b k2
  have hNonempty : (Finset.range (Z.log2 + 2)).Nonempty :=
    Exists.intro 0 (Finset.mem_range.mpr (Nat.zero_lt_succ _))
  choose i hi hMax using Finset.exists_max_image
    (Finset.range (Z.log2 + 2)) (dyadicPiece R S T aa bb) hNonempty
  have hTotal : lowDivisorMean Z R S T aa bb <=
      ((Z.log2 + 2 : Nat) : Real) * dyadicPiece R S T aa bb i := by
    calc
      _ <= (Finset.range (Z.log2 + 2)).sum (dyadicPiece R S T aa bb) :=
        lowMean_le_pieces Z R S T aa bb hZ
      _ <= (Finset.range (Z.log2 + 2)).sum (fun _ => dyadicPiece R S T aa bb i) :=
        Finset.sum_le_sum hMax
      _ = _ := by simp
  by_cases hi0 : i = 0
  . refine Exists.intro 1 (Exists.intro 1
      (And.intro Nat.zero_lt_one (And.intro Nat.zero_lt_one
        (And.intro (show 1 * 1 <= 2 * Z from Nat.mul_pos (by decide) hZ) ?_))))
    intro U hU hSU hTU
    have hUnit : dyadicPiece R S T aa bb i <= envelope Cu eps M N1 N2 1 1 U S T a b := by
      simpa only [dyadicPiece, divisorMean, aa, bb, hi0, ite_true, envelope, Nat.cast_one, one_mul,
        Real.sqrt_one, mul_one, Nat.div_one] using
        hu M N1 N2 k1 k2 R S T a b hR hS hT U hU hSU hTU
    exact hTotal.trans (mul_le_mul_of_nonneg_left
      (hUnit.trans (envelope_mono Cu C eps M N1 N2 1 1 U S T a b
        (le_max_right _ _) hU)) (Nat.cast_nonneg _))
  . have hipos : 0 < i := Nat.pos_of_ne_zero hi0
    have hiUpper : i <= Z.log2 + 1 := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
    have hk : Membership.mem (Finset.range (Z.log2 + 1)) (i - 1) :=
      Finset.mem_range.mpr ((Nat.sub_lt hipos Nat.zero_lt_one).trans_le hiUpper)
    have hD : 0 < 2 ^ (i - 1) := Nat.pow_pos (by decide)
    choose L1 L2 hL using hb (2 ^ (i - 1)) M N1 N2 k1 k2 R S T a b
      hD hN1 hN2 hR hS hT
    have hPair : L1 * L2 <= 2 * Z :=
      hL.2.2.2.1.trans (Nat.mul_le_mul_left 2 (band_scale_le_cutoff Z (i - 1) hZ hk))
    refine Exists.intro L1 (Exists.intro L2
      (And.intro hL.1 (And.intro hL.2.1 (And.intro hPair ?_))))
    intro U hU hSU hTU
    have hBand : dyadicPiece R S T aa bb i <= envelope Cb eps M N1 N2 L1 L2 U S T a b := by
      simpa only [dyadicPiece, ite_eq_right hi0, envelope] using hL.2.2.2.2 U hU hSU hTU
    exact hTotal.trans (mul_le_mul_of_nonneg_left
      (hBand.trans (envelope_mono Cb C eps M N1 N2 L1 L2 U S T a b
        (le_max_left _ _) hU)) (Nat.cast_nonneg _))

end PrimeFactorOscillations.QuadraticLowDivisorRange


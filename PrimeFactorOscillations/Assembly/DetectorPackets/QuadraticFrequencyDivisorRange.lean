/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Assembly.DetectorPackets.QuadraticFrequencyDivisorRows
import PrimeFactorOscillations.Assembly.DetectorPackets.QuadraticHighDyadicCover
import PrimeFactorOscillations.Assembly.DetectorPackets.QuadraticRangePairEnvelope
import PrimeFactorOscillations.Assembly.DetectorPackets.QuadraticRootFrequency

/-!
# QuadraticFrequencyDivisorRange

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

namespace PrimeFactorOscillations.QuadraticFrequencyDivisorRange

open IntegerQuadraticPrefix QuadraticGaussCoefficient QuadraticRootFrequency
open QuadraticRangePairEnvelope QuadraticFrequencyDivisorRows
open QuadraticFullFrequencyBand QuadraticFullFrequencyUnit
open SchwartzQuadraticSource QuadraticDyadicCover QuadraticHighDyadicCover

theorem source_frequency_divisor_range (W : SchwartzMap Real Complex) (c : Real)
    (hc : Not (c = 0)) (A : Nat) (eps : Real) (heps : 0 < eps) :
    exists C : Real, 0 < C /\
      forall (Y Z rowCap N1 N2 : Nat) (k1 k2 : Int) (R S T : Finset Nat)
        (a b : Nat -> Complex), 0 < Z -> Y <= Z -> 0 < N1 -> 0 < N2 ->
      (forall r, Membership.mem R r -> Membership.mem (columns rowCap) r) ->
      (forall n, Membership.mem S n -> Membership.mem (columns N1) n) ->
      (forall m, Membership.mem T m -> Membership.mem (columns N2) m) ->
      exists p : Prod Nat Nat, Membership.mem (admissiblePairs Y Z) p /\
      forall (L : Nat) (e X B U V : Real),
      0 < e -> 0 < X -> 0 < B -> 0 < U -> 0 < V ->
      (forall r, Membership.mem R r -> B <= (r : Real) /\ (r : Real) <= 2 * B) ->
      (forall n, Membership.mem S n -> U <= (n : Real) /\ (n : Real) <= 2 * U) ->
      (forall m, Membership.mem T m -> V <= (m : Real) /\ (m : Real) <= 2 * V) ->
      rangeMean Y Z R S T (rootCoefficient a k1) (rootCoefficient b k2)
        (sourceRho W c hc) L e X <=
        ((Z.log2 + 2 : Nat) : Real) *
          (C * (L : Real) * ((max N1 N2 : Nat) : Real) ^ eps *
            pairEnvelope rowCap N1 N2 S T a b p) := by
  choose Cb hCb hb using source_root_frequency_band W c hc A eps heps
  choose Cu hCu hu using source_root_frequency_unit W c hc A eps heps
  let C := max Cb Cu
  have hC : 0 < C := lt_of_lt_of_le hCb (le_max_left _ _)
  refine Exists.intro C (And.intro hC ?_)
  intro Y Z rowCap N1 N2 k1 k2 R S T a b hZ hYZ hN1 hN2 hR hS hT
  choose p hp hMax using Finset.exists_max_image (admissiblePairs Y Z)
    (pairEnvelope rowCap N1 N2 S T a b) (admissiblePairs_nonempty Y Z hZ hYZ)
  refine Exists.intro p (And.intro hp ?_)
  intro L e X B U V he hX hB hU hV hRB hSU hTV
  let aa := rootCoefficient a k1
  let bb := rootCoefficient b k2
  let F := sourceRho W c hc
  let f := rowMean R S T aa bb F L e X
  let target := C * (L : Real) * ((max N1 N2 : Nat) : Real) ^ eps *
    pairEnvelope rowCap N1 N2 S T a b p
  have hTarget : 0 <= target := by
    exact mul_nonneg (by positivity) (pairEnvelope_nonneg rowCap N1 N2 S T a b p)
  have hConstant (K : Real) (hK : K <= C) :
      K * (L : Real) * ((max N1 N2 : Nat) : Real) ^ eps <=
        C * (L : Real) * ((max N1 N2 : Nat) : Real) ^ eps :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hK (Nat.cast_nonneg L))
      (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have hBand (j : Nat) (hY : Y < 2 * 2 ^ j) (hZscale : 2 ^ j <= Z) :
      fullFrequencyBandMean (2 ^ j) R S T aa bb F L e X <= target := by
    have hD : 0 < 2 ^ j := Nat.pow_pos (by decide)
    choose L1 L2 hL using hb (2 ^ j) rowCap N1 N2 k1 k2 R S T a b
      hD hN1 hN2 hR hS hT
    have hLower : Y < 8 * (L1 * L2) := by
      calc
        _ < 2 * 2 ^ j := hY
        _ < 2 * (4 * (L1 * L2)) := Nat.mul_lt_mul_of_pos_left hL.2.2.1 (by decide)
        _ = _ := by ring
    have hPair : Membership.mem (admissiblePairs Y Z) (Prod.mk L1 L2) :=
      (admissiblePairs_mem Y Z (Prod.mk L1 L2)).mpr
        (And.intro hL.1 (And.intro hL.2.1
          (And.intro hLower
            (hL.2.2.2.1.trans (Nat.mul_le_mul_left 2 hZscale)))))
    have hEstimate :
        fullFrequencyBandMean (2 ^ j) R S T aa bb F L e X <=
          (Cb * (L : Real) * ((max N1 N2 : Nat) : Real) ^ eps) *
            pairEnvelope rowCap N1 N2 S T a b (Prod.mk L1 L2) := by
      calc
        _ <= _ := hL.2.2.2.2 L e X B U V he hX hB hU hV hRB hSU hTV
        _ = _ := by unfold pairEnvelope; ring
    exact hEstimate.trans (mul_le_mul
      (hConstant Cb (le_max_left _ _)) (hMax (Prod.mk L1 L2) hPair)
      (pairEnvelope_nonneg rowCap N1 N2 S T a b (Prod.mk L1 L2)) (by positivity))
  by_cases hY0 : Y = 0
  . subst Y
    have h11 : Membership.mem (admissiblePairs 0 Z) (Prod.mk 1 1) :=
      (admissiblePairs_mem 0 Z (Prod.mk 1 1)).mpr
        (And.intro Nat.zero_lt_one (And.intro Nat.zero_lt_one
          (And.intro (by decide)
            (show 1 * 1 <= 2 * Z from Nat.mul_pos (by decide) hZ))))
    have hUnit : f 1 <= target := by
      have hEstimate : f 1 <=
          (Cu * (L : Real) * ((max N1 N2 : Nat) : Real) ^ eps) *
            pairEnvelope rowCap N1 N2 S T a b (Prod.mk 1 1) := by
        dsimp only [f]
        rw [rowMean_one]
        calc
          _ <= _ := hu rowCap N1 N2 k1 k2 R S T a b hR hS hT
            L e X B U V he hX hB hU hV hRB hSU hTV
          _ = _ := by
            simp only [pairEnvelope, Nat.cast_one, one_mul, Real.sqrt_one,
              div_one, Nat.div_one]
            ring
      exact hEstimate.trans (mul_le_mul
        (hConstant Cu (le_max_right _ _)) (hMax (Prod.mk 1 1) h11)
        (pairEnvelope_nonneg rowCap N1 N2 S T a b (Prod.mk 1 1)) (by positivity))
    have hSet : Finset.Ioc 0 Z = Finset.Icc 1 Z := by
      ext d
      constructor
      . intro hd
        exact Finset.mem_Icc.mpr (Finset.mem_Ioc.mp hd)
      . intro hd
        exact Finset.mem_Ioc.mpr (Finset.mem_Icc.mp hd)
    have hCover := cutoff_sum_le f Z hZ
      (rowMean_nonneg R S T aa bb F L e X)
    change (Finset.Ioc 0 Z).sum f <= ((Z.log2 + 2 : Nat) : Real) * target
    rw [hSet]
    calc
      _ <= f 1 + (Finset.range (Z.log2 + 1)).sum
          (fun j => (Finset.Ioc (2 ^ j) (2 * 2 ^ j)).sum f) := hCover
      _ <= target + (Finset.range (Z.log2 + 1)).sum (fun _ => target) := by
        apply add_le_add hUnit
        apply Finset.sum_le_sum
        intro j hj
        dsimp only [f]
        rw [band_sum]
        exact hBand j (Nat.mul_pos (by decide) (Nat.pow_pos (by decide)))
          (band_scale_le_cutoff Z j hZ hj)
      _ = _ := by
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        simp [Nat.cast_add] <;> ring
  . have hYpos : 0 < Y := Nat.pos_of_ne_zero hY0
    have hSub : Finset.Icc Y.log2 Z.log2 <= Finset.range (Z.log2 + 2) := by
      intro j hj
      exact Finset.mem_range.mpr
        ((Finset.mem_Icc.mp hj).2.trans_lt
          ((Nat.lt_succ_self Z.log2).trans (Nat.lt_succ_self (Z.log2 + 1))))
    change (Finset.Ioc Y Z).sum f <= ((Z.log2 + 2 : Nat) : Real) * target
    calc
      _ <= (Finset.Icc Y.log2 Z.log2).sum
          (fun j => (Finset.Ioc (2 ^ j) (2 * 2 ^ j)).sum f) :=
        high_sum_le f Y Z hYpos hYZ (rowMean_nonneg R S T aa bb F L e X)
      _ <= (Finset.Icc Y.log2 Z.log2).sum (fun _ => target) := by
        apply Finset.sum_le_sum
        intro j hj
        dsimp only [f]
        rw [band_sum]
        have hScale := high_band_scale Y Z j hYpos hYZ hj
        exact hBand j hScale.1 hScale.2
      _ <= (Finset.range (Z.log2 + 2)).sum (fun _ => target) :=
        Finset.sum_le_sum_of_subset_of_nonneg hSub (fun j hj hnot => hTarget)
      _ = _ := by simp

end PrimeFactorOscillations.QuadraticFrequencyDivisorRange


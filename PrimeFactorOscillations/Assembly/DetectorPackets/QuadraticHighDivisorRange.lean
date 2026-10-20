/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Assembly.DetectorPackets.QuadraticHighDyadicCover
import PrimeFactorOscillations.Assembly.DetectorPackets.QuadraticRootWeightedBand

/-!
# QuadraticHighDivisorRange

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

namespace PrimeFactorOscillations.QuadraticHighDivisorRange

open QuadraticGaussCoefficient QuadraticDivisorMean IntegerQuadraticPrefix
open QuadraticProductDivisor QuadraticRootWeightedBand QuadraticHighDyadicCover

def highWeightedMean (Z V : Nat) (R S T : Finset Nat) (a b : Nat -> Complex) : Real :=
  (Finset.Ioc Z V).sum (fun d =>
    (1 / (d : Real)) * R.sum (fun r => norm (divisorRow d S T a b r)))

theorem high_root_divisor_mean (eps : Real) (heps : 0 < eps) :
    exists C : Real, 0 < C /\
      forall (Z V M N1 N2 : Nat) (k1 k2 : Int) (R S T : Finset Nat)
        (a b : Nat -> Complex), 0 < Z -> Z <= V -> 0 < N1 -> 0 < N2 ->
      (forall r, Membership.mem R r -> Membership.mem (columns M) r) ->
      (forall n, Membership.mem S n -> Membership.mem (columns N1) n) ->
      (forall m, Membership.mem T m -> Membership.mem (columns N2) m) ->
      exists L1 L2 : Nat, 0 < L1 /\ 0 < L2 /\
        Z < 8 * (L1 * L2) /\ L1 * L2 <= 2 * V /\
      highWeightedMean Z V R S T (rootCoefficient a k1) (rootCoefficient b k2) <=
        ((V.log2 + 1 : Nat) : Real) *
          (C * ((max N1 N2 : Nat) : Real) ^ eps /
            Real.sqrt ((L1 : Real) * (L2 : Real)) *
            Real.sqrt (prefixNorm M (N1 / L1) * maskedMass 1 S a) *
            Real.sqrt (prefixNorm M (N2 / L2) * maskedMass 1 T b)) := by
  choose C hC hc using root_weighted_divisor_band eps heps
  refine Exists.intro C (And.intro hC ?_)
  intro Z V M N1 N2 k1 k2 R S T a b hZ hZV hN1 hN2 hR hS hT
  let aa := rootCoefficient a k1
  let bb := rootCoefficient b k2
  have hNonempty : (Finset.Icc Z.log2 V.log2).Nonempty :=
    Exists.intro Z.log2 (Finset.mem_Icc.mpr
      (And.intro (le_refl _) (log2_mono_pos Z V hZ hZV)))
  choose k hk hMax using Finset.exists_max_image
    (Finset.Icc Z.log2 V.log2)
    (fun j => weightedBandMean (2 ^ j) R S T aa bb) hNonempty
  have hBandNonneg : 0 <= weightedBandMean (2 ^ k) R S T aa bb := by
    unfold weightedBandMean
    apply Finset.sum_nonneg
    intro d hd
    exact mul_nonneg (by positivity) (Finset.sum_nonneg (fun r hr => norm_nonneg _))
  have hSub : Finset.Icc Z.log2 V.log2 <= Finset.range (V.log2 + 1) := by
    intro j hj
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.mem_Icc.mp hj).2)
  have hTotal : highWeightedMean Z V R S T aa bb <=
      ((V.log2 + 1 : Nat) : Real) * weightedBandMean (2 ^ k) R S T aa bb := by
    calc
      _ <= (Finset.Icc Z.log2 V.log2).sum
          (fun j => weightedBandMean (2 ^ j) R S T aa bb) :=
        high_sum_le
          (fun d => (1 / (d : Real)) *
            R.sum (fun r => norm (divisorRow d S T aa bb r)))
          Z V hZ hZV
          (fun d => mul_nonneg (by positivity)
            (Finset.sum_nonneg (fun r hr => norm_nonneg _)))
      _ <= (Finset.Icc Z.log2 V.log2).sum
          (fun _ => weightedBandMean (2 ^ k) R S T aa bb) :=
        Finset.sum_le_sum hMax
      _ <= (Finset.range (V.log2 + 1)).sum
          (fun _ => weightedBandMean (2 ^ k) R S T aa bb) :=
        Finset.sum_le_sum_of_subset_of_nonneg hSub (fun j hj hnot => hBandNonneg)
      _ = _ := by simp
  have hD : 0 < 2 ^ k := Nat.pow_pos (by decide)
  choose L1 L2 hL using hc (2 ^ k) M N1 N2 k1 k2 R S T a b
    hD hN1 hN2 hR hS hT
  have hScale := high_band_scale Z V k hZ hZV hk
  have hLower : Z < 8 * (L1 * L2) := by
    calc
      _ < 2 * 2 ^ k := hScale.1
      _ < 2 * (4 * (L1 * L2)) := Nat.mul_lt_mul_of_pos_left hL.2.2.1 (by decide)
      _ = _ := by ring
  have hUpper : L1 * L2 <= 2 * V :=
    hL.2.2.2.1.trans (Nat.mul_le_mul_left 2 hScale.2)
  exact Exists.intro L1 (Exists.intro L2
    (And.intro hL.1 (And.intro hL.2.1
      (And.intro hLower (And.intro hUpper
        (hTotal.trans (mul_le_mul_of_nonneg_left hL.2.2.2.2 (Nat.cast_nonneg _))))))))

end PrimeFactorOscillations.QuadraticHighDivisorRange


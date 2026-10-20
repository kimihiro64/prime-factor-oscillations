/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Assembly.DetectorPackets.QuadraticPhysicalBandWeight
import PrimeFactorOscillations.Assembly.DetectorPackets.QuadraticProductBandSubpower
import PrimeFactorOscillations.Assembly.DetectorPackets.QuadraticRootFrequency

/-!
# QuadraticRootWeightedBand

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

namespace PrimeFactorOscillations.QuadraticRootWeightedBand

open QuadraticGaussCoefficient QuadraticDivisorMean IntegerQuadraticPrefix
open QuadraticProductDivisor QuadraticProductBand QuadraticRootFrequency

def weightedBandMean (D : Nat) (R S T : Finset Nat) (a b : Nat -> Complex) : Real :=
  (Finset.Ioc D (2 * D)).sum (fun d =>
    (1 / (d : Real)) * R.sum (fun r => norm (divisorRow d S T a b r)))

theorem weightedBandMean_le (D : Nat) (hD : 0 < D) (R S T : Finset Nat)
    (a b : Nat -> Complex) :
    weightedBandMean D R S T a b <= (1 / (D : Real)) * productBandMean D R S T a b := by
  have hpD : 0 < (D : Real) := by exact_mod_cast hD
  calc
    _ <= (Finset.Ioc D (2 * D)).sum (fun d =>
        (1 / (D : Real)) * R.sum (fun r => norm (divisorRow d S T a b r))) := by
      apply Finset.sum_le_sum
      intro d hd
      have hDd : (D : Real) <= (d : Real) := by
        exact_mod_cast (Finset.mem_Ioc.mp hd).1.le
      exact mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_left zero_le_one hpD hDd)
        (Finset.sum_nonneg (fun r hr => norm_nonneg _))
    _ = _ := by
      exact (Finset.mul_sum (Finset.Ioc D (2 * D))
        (fun d => R.sum (fun r => norm (divisorRow d S T a b r)))
        (1 / (D : Real))).symm

theorem root_weighted_divisor_band (eps : Real) (heps : 0 < eps) :
    exists C : Real, 0 < C /\
      forall (D M N1 N2 : Nat) (k1 k2 : Int) (R S T : Finset Nat)
        (a b : Nat -> Complex), 0 < D -> 0 < N1 -> 0 < N2 ->
      (forall r, Membership.mem R r -> Membership.mem (columns M) r) ->
      (forall n, Membership.mem S n -> Membership.mem (columns N1) n) ->
      (forall m, Membership.mem T m -> Membership.mem (columns N2) m) ->
      exists L1 L2 : Nat, 0 < L1 /\ 0 < L2 /\
        D < 4 * (L1 * L2) /\ L1 * L2 <= 2 * D /\
      weightedBandMean D R S T (rootCoefficient a k1) (rootCoefficient b k2) <=
        C * ((max N1 N2 : Nat) : Real) ^ eps /
          Real.sqrt ((L1 : Real) * (L2 : Real)) *
          Real.sqrt (prefixNorm M (N1 / L1) * maskedMass 1 S a) *
          Real.sqrt (prefixNorm M (N2 / L2) * maskedMass 1 T b) := by
  choose C hC hc using QuadraticProductBandSubpower.source_product_divisor_mean eps heps
  refine Exists.intro (2 * C) (And.intro (by positivity) ?_)
  intro D M N1 N2 k1 k2 R S T a b hD hN1 hN2 hR hS hT
  choose L1 L2 hL using hc D M N1 N2 R S T
    (rootCoefficient a k1) (rootCoefficient b k2) hD hN1 hN2 hR hS hT
  refine Exists.intro L1 (Exists.intro L2
    (And.intro hL.1 (And.intro hL.2.1
      (And.intro hL.2.2.1 (And.intro hL.2.2.2.1 ?_)))))
  have h1 := root_mass_factor M N1 L1 k1 S a hS
  have h2 := root_mass_factor M N2 L2 k2 T b hT
  have hScale : 0 <= C * ((max N1 N2 : Nat) : Real) ^ eps *
      Real.sqrt ((L1 : Real) * (L2 : Real)) := by positivity
  have hProduct :
      productBandMean D R S T (rootCoefficient a k1) (rootCoefficient b k2) <=
      C * ((max N1 N2 : Nat) : Real) ^ eps *
        Real.sqrt ((L1 : Real) * (L2 : Real)) *
        Real.sqrt (prefixNorm M (N1 / L1) * maskedMass 1 S a) *
        Real.sqrt (prefixNorm M (N2 / L2) * maskedMass 1 T b) :=
    hL.2.2.2.2.trans (mul_le_mul (mul_le_mul_of_nonneg_left h1 hScale) h2
      (Real.sqrt_nonneg _) (by positivity))
  have hDiv := QuadraticPhysicalBandWeight.sqrt_pair_div_band
    D L1 L2 hD hL.1 hL.2.1 hL.2.2.2.1
  calc
    _ <= (1 / (D : Real)) *
        productBandMean D R S T (rootCoefficient a k1) (rootCoefficient b k2) :=
      weightedBandMean_le D hD R S T (rootCoefficient a k1) (rootCoefficient b k2)
    _ <= (1 / (D : Real)) *
        (C * ((max N1 N2 : Nat) : Real) ^ eps *
          Real.sqrt ((L1 : Real) * (L2 : Real)) *
          Real.sqrt (prefixNorm M (N1 / L1) * maskedMass 1 S a) *
          Real.sqrt (prefixNorm M (N2 / L2) * maskedMass 1 T b)) :=
      mul_le_mul_of_nonneg_left hProduct (by positivity)
    _ = (C * ((max N1 N2 : Nat) : Real) ^ eps) *
        (Real.sqrt ((L1 : Real) * (L2 : Real)) / (D : Real)) *
        Real.sqrt (prefixNorm M (N1 / L1) * maskedMass 1 S a) *
        Real.sqrt (prefixNorm M (N2 / L2) * maskedMass 1 T b) := by ring
    _ <= (C * ((max N1 N2 : Nat) : Real) ^ eps) *
        (2 / Real.sqrt ((L1 : Real) * (L2 : Real))) *
        Real.sqrt (prefixNorm M (N1 / L1) * maskedMass 1 S a) *
        Real.sqrt (prefixNorm M (N2 / L2) * maskedMass 1 T b) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hDiv (by positivity))
          (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)
    _ = _ := by ring

end PrimeFactorOscillations.QuadraticRootWeightedBand


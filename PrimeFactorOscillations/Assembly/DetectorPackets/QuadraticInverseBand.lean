/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Assembly.DetectorPackets.QuadraticGaussCoefficient
import PrimeFactorOscillations.Assembly.DetectorPackets.QuadraticProductBandSubpower

/-!
# QuadraticInverseBand

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

namespace PrimeFactorOscillations.QuadraticInverseBand

open QuadraticGaussCoefficient QuadraticDivisorMean IntegerQuadraticPrefix
open QuadraticProductBand

theorem inverse_product_divisor_mean (eps : Real) (heps : 0 < eps) :
    exists C : Real, 0 < C /\
      forall (D M N1 N2 : Nat) (k1 k2 : Int) (R S T : Finset Nat)
        (a b : Nat -> Complex), 0 < D -> 0 < N1 -> 0 < N2 ->
      (forall r, Membership.mem R r -> Membership.mem (columns M) r) ->
      (forall n, Membership.mem S n -> Membership.mem (columns N1) n) ->
      (forall m, Membership.mem T m -> Membership.mem (columns N2) m) ->
      exists L1 L2 : Nat, 0 < L1 /\ 0 < L2 /\
        D < 4 * (L1 * L2) /\ L1 * L2 <= 2 * D /\
      forall U : Real, 0 < U ->
      (forall n, Membership.mem S n -> U <= (n : Real)) ->
      (forall m, Membership.mem T m -> U <= (m : Real)) ->
      productBandMean D R S T (inverseCoefficient a k1) (inverseCoefficient b k2) <=
        C * ((max N1 N2 : Nat) : Real) ^ eps *
          Real.sqrt ((L1 : Real) * (L2 : Real)) * (1 / U) *
          Real.sqrt (prefixNorm M (N1 / L1) * maskedMass 1 S a) *
          Real.sqrt (prefixNorm M (N2 / L2) * maskedMass 1 T b) := by
  choose C hC hc using QuadraticProductBandSubpower.source_product_divisor_mean eps heps
  refine Exists.intro C (And.intro hC ?_)
  intro D M N1 N2 k1 k2 R S T a b hD hN1 hN2 hR hS hT
  choose L1 L2 hL using
    hc D M N1 N2 R S T (inverseCoefficient a k1) (inverseCoefficient b k2)
      hD hN1 hN2 hR hS hT
  refine Exists.intro L1 (Exists.intro L2
    (And.intro hL.1 (And.intro hL.2.1
      (And.intro hL.2.2.1 (And.intro hL.2.2.2.1 ?_)))))
  intro U hU hSU hTU
  have ha := inverseCoefficient_mass 1 N1 k1 S a U hU hS hSU
  have hb := inverseCoefficient_mass 1 N2 k2 T b U hU hT hTU
  have hp1 : 0 <= prefixNorm M (N1 / L1) := by
    unfold prefixNorm
    exact sq_nonneg _
  have hp2 : 0 <= prefixNorm M (N2 / L2) := by
    unfold prefixNorm
    exact sq_nonneg _
  have hq : 0 <= 1 / U := by positivity
  have h1 :
      Real.sqrt (prefixNorm M (N1 / L1) *
        maskedMass 1 S (inverseCoefficient a k1)) <=
      Real.sqrt (1 / U) *
        Real.sqrt (prefixNorm M (N1 / L1) * maskedMass 1 S a) := by
    calc
      _ <= Real.sqrt (prefixNorm M (N1 / L1) * ((1 / U) * maskedMass 1 S a)) :=
        Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left ha hp1)
      _ = _ := by
        rw [show prefixNorm M (N1 / L1) * ((1 / U) * maskedMass 1 S a) =
          (1 / U) * (prefixNorm M (N1 / L1) * maskedMass 1 S a) from by ring,
          Real.sqrt_mul hq]
  have h2 :
      Real.sqrt (prefixNorm M (N2 / L2) *
        maskedMass 1 T (inverseCoefficient b k2)) <=
      Real.sqrt (1 / U) *
        Real.sqrt (prefixNorm M (N2 / L2) * maskedMass 1 T b) := by
    calc
      _ <= Real.sqrt (prefixNorm M (N2 / L2) * ((1 / U) * maskedMass 1 T b)) :=
        Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hb hp2)
      _ = _ := by
        rw [show prefixNorm M (N2 / L2) * ((1 / U) * maskedMass 1 T b) =
          (1 / U) * (prefixNorm M (N2 / L2) * maskedMass 1 T b) from by ring,
          Real.sqrt_mul hq]
  have hscale : 0 <= C * ((max N1 N2 : Nat) : Real) ^ eps *
      Real.sqrt ((L1 : Real) * (L2 : Real)) := by positivity
  apply hL.2.2.2.2.trans
  calc
    _ <= (C * ((max N1 N2 : Nat) : Real) ^ eps *
        Real.sqrt ((L1 : Real) * (L2 : Real))) *
        (Real.sqrt (1 / U) *
          Real.sqrt (prefixNorm M (N1 / L1) * maskedMass 1 S a)) *
        (Real.sqrt (1 / U) *
          Real.sqrt (prefixNorm M (N2 / L2) * maskedMass 1 T b)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left h1 hscale) h2
        (Real.sqrt_nonneg _) (by positivity)
    _ = _ := by
      have hsq : Real.sqrt (1 / U) * Real.sqrt (1 / U) = 1 / U := by
        simpa only [pow_two] using Real.sq_sqrt hq
      calc
        _ = (C * ((max N1 N2 : Nat) : Real) ^ eps *
          Real.sqrt ((L1 : Real) * (L2 : Real))) *
          (Real.sqrt (1 / U) * Real.sqrt (1 / U)) *
          Real.sqrt (prefixNorm M (N1 / L1) * maskedMass 1 S a) *
          Real.sqrt (prefixNorm M (N2 / L2) * maskedMass 1 T b) := by ring
        _ = _ := by rw [hsq]

end PrimeFactorOscillations.QuadraticInverseBand


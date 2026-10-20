/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Assembly.DetectorPackets.QuadraticGaussCoefficient
import PrimeFactorOscillations.Assembly.DetectorPackets.QuadraticProductBandSubpower

/-!
# QuadraticInverseUnit

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

namespace PrimeFactorOscillations.QuadraticInverseUnit

open QuadraticGaussCoefficient QuadraticDivisorMean IntegerQuadraticPrefix
open QuadraticProductDivisor

theorem inverse_mass_factor (M N L : Nat) (k : Int) (S : Finset Nat)
    (a : Nat -> Complex) (U : Real) (hU : 0 < U)
    (hS : forall n, Membership.mem S n -> Membership.mem (columns N) n)
    (hLower : forall n, Membership.mem S n -> U <= (n : Real)) :
    Real.sqrt (prefixNorm M (N / L) * maskedMass 1 S (inverseCoefficient a k)) <=
      Real.sqrt (1 / U) * Real.sqrt (prefixNorm M (N / L) * maskedMass 1 S a) := by
  have hp : 0 <= prefixNorm M (N / L) := by
    unfold prefixNorm
    exact sq_nonneg _
  have hq : 0 <= 1 / U := by positivity
  calc
    _ <= Real.sqrt (prefixNorm M (N / L) * ((1 / U) * maskedMass 1 S a)) :=
      Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left
        (inverseCoefficient_mass 1 N k S a U hU hS hLower) hp)
    _ = _ := by
      rw [show prefixNorm M (N / L) * ((1 / U) * maskedMass 1 S a) =
        (1 / U) * (prefixNorm M (N / L) * maskedMass 1 S a) from by ring,
        Real.sqrt_mul hq]

theorem inverse_unit_divisor_mean (eps : Real) (heps : 0 < eps) :
    exists C : Real, 0 < C /\
      forall (M N1 N2 : Nat) (k1 k2 : Int) (R S T : Finset Nat)
        (a b : Nat -> Complex),
      (forall r, Membership.mem R r -> Membership.mem (columns M) r) ->
      (forall n, Membership.mem S n -> Membership.mem (columns N1) n) ->
      (forall m, Membership.mem T m -> Membership.mem (columns N2) m) ->
      forall U : Real, 0 < U ->
      (forall n, Membership.mem S n -> U <= (n : Real)) ->
      (forall m, Membership.mem T m -> U <= (m : Real)) ->
      R.sum (fun r => norm (divisorRow 1 S T
        (inverseCoefficient a k1) (inverseCoefficient b k2) r)) <=
        C * ((max N1 N2 : Nat) : Real) ^ eps * (1 / U) *
          Real.sqrt (prefixNorm M N1 * maskedMass 1 S a) *
          Real.sqrt (prefixNorm M N2 * maskedMass 1 T b) := by
  choose C hC hc using QuadraticProductBandSubpower.unit_divisor_mean eps heps
  refine Exists.intro C (And.intro hC ?_)
  intro M N1 N2 k1 k2 R S T a b hR hS hT U hU hSU hTU
  have h1 := inverse_mass_factor M N1 1 k1 S a U hU hS hSU
  have h2 := inverse_mass_factor M N2 1 k2 T b U hU hT hTU
  simp only [Nat.div_one] at h1 h2
  have hscale : 0 <= C * ((max N1 N2 : Nat) : Real) ^ eps := by positivity
  apply (hc M N1 N2 R S T (inverseCoefficient a k1) (inverseCoefficient b k2)
    hR hS hT).trans
  calc
    _ <= (C * ((max N1 N2 : Nat) : Real) ^ eps) *
        (Real.sqrt (1 / U) * Real.sqrt (prefixNorm M N1 * maskedMass 1 S a)) *
        (Real.sqrt (1 / U) * Real.sqrt (prefixNorm M N2 * maskedMass 1 T b)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left h1 hscale) h2
        (Real.sqrt_nonneg _) (by positivity)
    _ = _ := by
      have hsq : Real.sqrt (1 / U) * Real.sqrt (1 / U) = 1 / U := by
        simpa only [pow_two] using Real.sq_sqrt (show 0 <= 1 / U by positivity)
      calc
        _ = (C * ((max N1 N2 : Nat) : Real) ^ eps) *
          (Real.sqrt (1 / U) * Real.sqrt (1 / U)) *
          Real.sqrt (prefixNorm M N1 * maskedMass 1 S a) *
          Real.sqrt (prefixNorm M N2 * maskedMass 1 T b) := by ring
        _ = _ := by rw [hsq]

end PrimeFactorOscillations.QuadraticInverseUnit


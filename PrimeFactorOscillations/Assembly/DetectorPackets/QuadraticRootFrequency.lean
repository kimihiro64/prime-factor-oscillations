/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Assembly.DetectorPackets.QuadraticFullFrequencyBand
import PrimeFactorOscillations.Assembly.DetectorPackets.QuadraticFullFrequencyUnit
import PrimeFactorOscillations.Assembly.DetectorPackets.QuadraticGaussCoefficient

/-!
# QuadraticRootFrequency

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

namespace PrimeFactorOscillations.QuadraticRootFrequency

open QuadraticGaussCoefficient QuadraticDivisorMean IntegerQuadraticPrefix
open QuadraticFullFrequencyBand QuadraticFullFrequencyUnit SchwartzQuadraticSource

theorem root_mass_factor (M N L : Nat) (k : Int) (S : Finset Nat) (a : Nat -> Complex)
    (hS : forall n, Membership.mem S n -> Membership.mem (columns N) n) :
    Real.sqrt (prefixNorm M (N / L) * maskedMass 1 S (rootCoefficient a k)) <=
      Real.sqrt (prefixNorm M (N / L) * maskedMass 1 S a) := by
  apply Real.sqrt_le_sqrt
  apply mul_le_mul_of_nonneg_left (rootCoefficient_mass 1 N k S a hS)
  unfold prefixNorm
  exact sq_nonneg _

theorem source_root_frequency_band (W : SchwartzMap Real Complex) (c : Real)
    (hc : Not (c = 0)) (A : Nat) (eps : Real) (heps : 0 < eps) :
    exists C : Real, 0 < C /\
      forall (D rowCap N1 N2 : Nat) (k1 k2 : Int) (R S T : Finset Nat)
        (a b : Nat -> Complex), 0 < D -> 0 < N1 -> 0 < N2 ->
      (forall r, Membership.mem R r -> Membership.mem (columns rowCap) r) ->
      (forall n, Membership.mem S n -> Membership.mem (columns N1) n) ->
      (forall m, Membership.mem T m -> Membership.mem (columns N2) m) ->
      exists L1 L2 : Nat, 0 < L1 /\ 0 < L2 /\
        D < 4 * (L1 * L2) /\ L1 * L2 <= 2 * D /\
      forall (L : Nat) (e X B U V : Real),
      0 < e -> 0 < X -> 0 < B -> 0 < U -> 0 < V ->
      (forall r, Membership.mem R r -> B <= (r : Real) /\ (r : Real) <= 2 * B) ->
      (forall n, Membership.mem S n -> U <= (n : Real) /\ (n : Real) <= 2 * U) ->
      (forall m, Membership.mem T m -> V <= (m : Real) /\ (m : Real) <= 2 * V) ->
      fullFrequencyBandMean D R S T (rootCoefficient a k1) (rootCoefficient b k2)
        (sourceRho W c hc) L e X <=
        C * (L : Real) * ((max N1 N2 : Nat) : Real) ^ eps /
          Real.sqrt ((L1 : Real) * (L2 : Real)) *
          Real.sqrt (prefixNorm rowCap (N1 / L1) * maskedMass 1 S a) *
          Real.sqrt (prefixNorm rowCap (N2 / L2) * maskedMass 1 T b) := by
  choose C hC hCbound using source_full_frequency_band W c hc A eps heps
  refine Exists.intro C (And.intro hC ?_)
  intro D rowCap N1 N2 k1 k2 R S T a b hD hN1 hN2 hR hS hT
  choose L1 L2 hL using
    hCbound D rowCap N1 N2 R S T (rootCoefficient a k1) (rootCoefficient b k2)
      hD hN1 hN2 hR hS hT
  refine Exists.intro L1 (Exists.intro L2
    (And.intro hL.1 (And.intro hL.2.1
      (And.intro hL.2.2.1 (And.intro hL.2.2.2.1 ?_)))))
  intro L e X B U V he hX hB hU hV hRB hSU hTV
  have h1 := root_mass_factor rowCap N1 L1 k1 S a hS
  have h2 := root_mass_factor rowCap N2 L2 k2 T b hT
  have hscale : 0 <= C * (L : Real) * ((max N1 N2 : Nat) : Real) ^ eps /
      Real.sqrt ((L1 : Real) * (L2 : Real)) := by positivity
  apply (hL.2.2.2.2 L e X B U V he hX hB hU hV hRB hSU hTV).trans
  exact mul_le_mul (mul_le_mul_of_nonneg_left h1 hscale) h2
    (Real.sqrt_nonneg _) (by positivity)

theorem source_root_frequency_unit (W : SchwartzMap Real Complex) (c : Real)
    (hc : Not (c = 0)) (A : Nat) (eps : Real) (heps : 0 < eps) :
    exists C : Real, 0 < C /\
      forall (M N1 N2 : Nat) (k1 k2 : Int) (R S T : Finset Nat) (a b : Nat -> Complex),
      (forall r, Membership.mem R r -> Membership.mem (columns M) r) ->
      (forall n, Membership.mem S n -> Membership.mem (columns N1) n) ->
      (forall m, Membership.mem T m -> Membership.mem (columns N2) m) ->
      forall (L : Nat) (e X B U V : Real),
      0 < e -> 0 < X -> 0 < B -> 0 < U -> 0 < V ->
      (forall r, Membership.mem R r -> B <= (r : Real) /\ (r : Real) <= 2 * B) ->
      (forall n, Membership.mem S n -> U <= (n : Real) /\ (n : Real) <= 2 * U) ->
      (forall m, Membership.mem T m -> V <= (m : Real) /\ (m : Real) <= 2 * V) ->
      fullFrequencyUnitMean R S T (rootCoefficient a k1) (rootCoefficient b k2)
        (sourceRho W c hc) L e X <=
        C * (L : Real) * ((max N1 N2 : Nat) : Real) ^ eps *
          Real.sqrt (prefixNorm M N1 * maskedMass 1 S a) *
          Real.sqrt (prefixNorm M N2 * maskedMass 1 T b) := by
  choose C hC hCbound using source_full_frequency_unit W c hc A eps heps
  refine Exists.intro C (And.intro hC ?_)
  intro M N1 N2 k1 k2 R S T a b hR hS hT L e X B U V he hX hB hU hV hRB hSU hTV
  have h1 := root_mass_factor M N1 1 k1 S a hS
  have h2 := root_mass_factor M N2 1 k2 T b hT
  simp only [Nat.div_one] at h1 h2
  have hscale : 0 <= C * (L : Real) * ((max N1 N2 : Nat) : Real) ^ eps := by positivity
  apply (hCbound M N1 N2 R S T (rootCoefficient a k1) (rootCoefficient b k2)
    hR hS hT L e X B U V he hX hB hU hV hRB hSU hTV).trans
  exact mul_le_mul (mul_le_mul_of_nonneg_left h1 hscale) h2
    (Real.sqrt_nonneg _) (by positivity)

end PrimeFactorOscillations.QuadraticRootFrequency


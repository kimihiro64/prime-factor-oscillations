/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Assembly.DetectorPackets.EvenPacketRowBound
import PrimeFactorOscillations.Assembly.DetectorPackets.QuadraticPhysicalFrequency

/-!
# QuadraticFullFrequencyBand

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

namespace PrimeFactorOscillations.QuadraticFullFrequencyBand

open IntegerQuadraticPrefix QuadraticDivisorMean QuadraticBandUniformPhase
open QuadraticSmoothBandRows QuadraticPhysicalBandWeight QuadraticPhysicalFrequency
open CoprimeSchwartzSplit SchwartzQuadraticSource EvenPacketRowBound

def fullFrequencyBandMean (D : Nat) (R S T : Finset Nat) (a b : Nat -> Complex)
    (F : SchwartzMap Real Complex) (L : Nat) (e X : Real) : Real :=
  (bandRows D R).sum (fun p => (1 / (p.1 : Real)) *
    norm ((S.product T).sum (fun q => coefficient a b p.1 p.2 q.1 q.2 *
      frequencyPacket L F
        (Real.sqrt (e * (q.1 : Real) * (q.2 : Real) / (X * (p.2 : Real))) / (p.1 : Real)))))

theorem fullFrequencyBandMean_le_positive (D : Nat) (R S T : Finset Nat)
    (a b : Nat -> Complex) (F : SchwartzMap Real Complex)
    (hF : forall x : Real, F (-x) = F x) (L : Nat) (e X : Real) :
    fullFrequencyBandMean D R S T a b F L e X <=
      2 * (Finset.Ioc 0 L).sum (fun ell =>
        weightedPhysicalBandMean D R S T a b F (ell : Real) e X) := by
  have h := weighted_even_packet_rows (bandRows D R) (S.product T)
    (fun p => 1 / (p.1 : Real)) (fun p hp => by positivity)
    (fun p q => coefficient a b p.1 p.2 q.1 q.2)
    (fun p q => Real.sqrt (e * (q.1 : Real) * (q.2 : Real) / (X * (p.2 : Real))) /
      (p.1 : Real)) F hF L
  have heq :
      2 * (Finset.Ioc 0 L).sum (fun ell => (bandRows D R).sum (fun p =>
        (1 / (p.1 : Real)) * norm ((S.product T).sum (fun q =>
          coefficient a b p.1 p.2 q.1 q.2 *
            F ((ell : Real) *
              (Real.sqrt (e * (q.1 : Real) * (q.2 : Real) / (X * (p.2 : Real))) /
                (p.1 : Real))))))) =
      2 * (Finset.Ioc 0 L).sum (fun ell =>
        weightedPhysicalBandMean D R S T a b F (ell : Real) e X) := by
    apply congrArg (fun y : Real => 2 * y)
    apply Finset.sum_congr rfl
    intro ell hell
    unfold weightedPhysicalBandMean
    apply Finset.sum_congr rfl
    intro p hp
    apply congrArg (fun z : Complex => (1 / (p.1 : Real)) * norm z)
    apply Finset.sum_congr rfl
    intro q hq
    apply congrArg (fun y : Real => coefficient a b p.1 p.2 q.1 q.2 * F y)
    ring
  exact h.trans_eq heq

theorem source_full_frequency_band (W : SchwartzMap Real Complex) (c : Real)
    (hc : Not (c = 0)) (A : Nat) (eps : Real) (heps : 0 < eps) :
    exists C : Real, 0 < C /\
      forall (D rowCap N1 N2 : Nat) (R S T : Finset Nat) (a b : Nat -> Complex),
      0 < D -> 0 < N1 -> 0 < N2 ->
      (forall r, Membership.mem R r -> Membership.mem (columns rowCap) r) ->
      (forall n, Membership.mem S n -> Membership.mem (columns N1) n) ->
      (forall m, Membership.mem T m -> Membership.mem (columns N2) m) ->
      exists L1 L2 : Nat,
        0 < L1 /\ 0 < L2 /\ D < 4 * (L1 * L2) /\ L1 * L2 <= 2 * D /\
        forall (L : Nat) (e X B U V : Real), 0 < e -> 0 < X ->
          0 < B -> 0 < U -> 0 < V ->
          (forall r, Membership.mem R r -> B <= (r : Real) /\ (r : Real) <= 2 * B) ->
          (forall n, Membership.mem S n -> U <= (n : Real) /\ (n : Real) <= 2 * U) ->
          (forall m, Membership.mem T m -> V <= (m : Real) /\ (m : Real) <= 2 * V) ->
          fullFrequencyBandMean D R S T a b (sourceRho W c hc) L e X <=
            C * (L : Real) * ((max N1 N2 : Nat) : Real) ^ eps /
              Real.sqrt ((L1 : Real) * (L2 : Real)) *
              Real.sqrt (prefixNorm rowCap (N1 / L1) * maskedMass 1 S a) *
              Real.sqrt (prefixNorm rowCap (N2 / L2) * maskedMass 1 T b) := by
  choose C hC hbound using physical_frequency_sum (sourceRho W c hc) A eps heps
  refine Exists.intro (2 * C) (And.intro (by positivity) ?_)
  intro D rowCap N1 N2 R S T a b hD hN1 hN2 hR hS hT
  choose L1 L2 h1 h2 hlo hhi hb using hbound D rowCap N1 N2 R S T a b
    hD hN1 hN2 hR hS hT
  refine Exists.intro L1 (Exists.intro L2
    (And.intro h1 (And.intro h2 (And.intro hlo (And.intro hhi ?_)))))
  intro L e X B U V he hX hB hU hV hRows hNs hMs
  calc
    _ <= 2 * (Finset.Ioc 0 L).sum (fun ell =>
        weightedPhysicalBandMean D R S T a b (sourceRho W c hc) (ell : Real) e X) :=
      fullFrequencyBandMean_le_positive D R S T a b (sourceRho W c hc)
        (sourceRho_even W c hc) L e X
    _ <= 2 * (C * (L : Real) * ((max N1 N2 : Nat) : Real) ^ eps /
        Real.sqrt ((L1 : Real) * (L2 : Real)) *
        Real.sqrt (prefixNorm rowCap (N1 / L1) * maskedMass 1 S a) *
        Real.sqrt (prefixNorm rowCap (N2 / L2) * maskedMass 1 T b)) :=
      mul_le_mul_of_nonneg_left (hb L e X B U V he hX hB hU hV hRows hNs hMs) (by norm_num)
    _ = _ := by ring

end PrimeFactorOscillations.QuadraticFullFrequencyBand


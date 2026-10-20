/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Assembly.DetectorPackets.EvenPacketRowBound
import PrimeFactorOscillations.Assembly.DetectorPackets.QuadraticUnitFrequency

/-!
# QuadraticFullFrequencyUnit

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

namespace PrimeFactorOscillations.QuadraticFullFrequencyUnit

open IntegerQuadraticPrefix QuadraticDivisorMean QuadraticSmoothBandRows
open QuadraticPhysicalUnit QuadraticUnitFrequency CoprimeSchwartzSplit
open SchwartzQuadraticSource EvenPacketRowBound

def fullFrequencyUnitMean (R S T : Finset Nat) (a b : Nat -> Complex)
    (F : SchwartzMap Real Complex) (L : Nat) (e X : Real) : Real :=
  R.sum (fun r => norm ((S.product T).sum (fun q => coefficient a b 1 r q.1 q.2 *
    frequencyPacket L F (Real.sqrt (e * (q.1 : Real) * (q.2 : Real) / (X * (r : Real)))))))

theorem fullFrequencyUnitMean_le_positive (R S T : Finset Nat)
    (a b : Nat -> Complex) (F : SchwartzMap Real Complex)
    (hF : forall x : Real, F (-x) = F x) (L : Nat) (e X : Real) :
    fullFrequencyUnitMean R S T a b F L e X <=
      2 * (Finset.Ioc 0 L).sum (fun ell => physicalUnitMean R S T a b F (ell : Real) e X) := by
  have h := weighted_even_packet_rows R (S.product T)
    (fun _ => (1 : Real)) (fun r hr => by norm_num)
    (fun r q => coefficient a b 1 r q.1 q.2)
    (fun r q => Real.sqrt (e * (q.1 : Real) * (q.2 : Real) / (X * (r : Real)))) F hF L
  simpa only [fullFrequencyUnitMean, physicalUnitMean, one_mul] using h

theorem source_full_frequency_unit (W : SchwartzMap Real Complex) (c : Real)
    (hc : Not (c = 0)) (A : Nat) (eps : Real) (heps : 0 < eps) :
    exists C : Real, 0 < C /\
      forall (M N1 N2 : Nat) (R S T : Finset Nat) (a b : Nat -> Complex),
      (forall r, Membership.mem R r -> Membership.mem (columns M) r) ->
      (forall n, Membership.mem S n -> Membership.mem (columns N1) n) ->
      (forall m, Membership.mem T m -> Membership.mem (columns N2) m) ->
      forall (L : Nat) (e X B U V : Real), 0 < e -> 0 < X ->
        0 < B -> 0 < U -> 0 < V ->
        (forall r, Membership.mem R r -> B <= (r : Real) /\ (r : Real) <= 2 * B) ->
        (forall n, Membership.mem S n -> U <= (n : Real) /\ (n : Real) <= 2 * U) ->
        (forall m, Membership.mem T m -> V <= (m : Real) /\ (m : Real) <= 2 * V) ->
        fullFrequencyUnitMean R S T a b (sourceRho W c hc) L e X <=
          C * (L : Real) * ((max N1 N2 : Nat) : Real) ^ eps *
            Real.sqrt (prefixNorm M N1 * maskedMass 1 S a) *
            Real.sqrt (prefixNorm M N2 * maskedMass 1 T b) := by
  choose C hC hbound using physical_unit_frequency_sum (sourceRho W c hc) A eps heps
  refine Exists.intro (2 * C) (And.intro (by positivity) ?_)
  intro M N1 N2 R S T a b hR hS hT L e X B U V he hX hB hU hV hRows hNs hMs
  calc
    _ <= 2 * (Finset.Ioc 0 L).sum (fun ell =>
        physicalUnitMean R S T a b (sourceRho W c hc) (ell : Real) e X) :=
      fullFrequencyUnitMean_le_positive R S T a b (sourceRho W c hc)
        (sourceRho_even W c hc) L e X
    _ <= 2 * (C * (L : Real) * ((max N1 N2 : Nat) : Real) ^ eps *
        Real.sqrt (prefixNorm M N1 * maskedMass 1 S a) *
        Real.sqrt (prefixNorm M N2 * maskedMass 1 T b)) :=
      mul_le_mul_of_nonneg_left
        (hbound M N1 N2 R S T a b hR hS hT L e X B U V he hX hB hU hV hRows hNs hMs)
        (by norm_num)
    _ = _ := by ring

end PrimeFactorOscillations.QuadraticFullFrequencyUnit


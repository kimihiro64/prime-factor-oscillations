/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Assembly.DetectorPackets.QuadraticPhysicalBand
import PrimeFactorOscillations.Assembly.DetectorPackets.QuadraticSmoothUnit

/-!
# QuadraticPhysicalUnit

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

namespace PrimeFactorOscillations.QuadraticPhysicalUnit

open IntegerQuadraticPrefix QuadraticDivisorMean QuadraticSmoothBandRows
open QuadraticSmoothBandCoordinates QuadraticPhysicalBand QuadraticSmoothUnit

def physicalUnitMean (R S T : Finset Nat) (a b : Nat -> Complex)
    (F : SchwartzMap Real Complex) (ell e X : Real) : Real :=
  R.sum (fun r => norm ((S.product T).sum (fun q =>
    coefficient a b 1 r q.1 q.2 *
      F (ell * Real.sqrt (e * (q.1 : Real) * (q.2 : Real) / (X * (r : Real)))))))

theorem physical_unit_divisor_mean (F : SchwartzMap Real Complex)
    (A : Nat) (eps : Real) (heps : 0 < eps) :
    exists C : Real, 0 < C /\
      forall (M N1 N2 : Nat) (R S T : Finset Nat) (a b : Nat -> Complex),
      (forall r, Membership.mem R r -> Membership.mem (columns M) r) ->
      (forall n, Membership.mem S n -> Membership.mem (columns N1) n) ->
      (forall m, Membership.mem T m -> Membership.mem (columns N2) m) ->
      forall (ell e X B U V : Real), 0 <= ell -> 0 < e -> 0 < X ->
        0 < B -> 0 < U -> 0 < V ->
        (forall r, Membership.mem R r -> B <= (r : Real) /\ (r : Real) <= 2 * B) ->
        (forall n, Membership.mem S n -> U <= (n : Real) /\ (n : Real) <= 2 * U) ->
        (forall m, Membership.mem T m -> V <= (m : Real) /\ (m : Real) <= 2 * V) ->
        physicalUnitMean R S T a b F ell e X <=
          C * ((max N1 N2 : Nat) : Real) ^ eps /
            (1 + ell * Real.sqrt (e * U * V / (X * B))) ^ A *
            Real.sqrt (prefixNorm M N1 * maskedMass 1 S a) *
            Real.sqrt (prefixNorm M N2 * maskedMass 1 T b) := by
  choose C hC hc using smooth_unit_divisor_mean F 3 (by norm_num) A eps heps
  refine Exists.intro C (And.intro hC ?_)
  intro M N1 N2 R S T a b hR hS hT ell e X B U V hell he hX hB hU hV hRows hNs hMs
  let scale : Real := ell * Real.sqrt (e * U * V / (X * B))
  let eta : Nat -> Real := fun n => Real.log ((n : Real) / U) / 2
  let theta : Nat -> Real := fun m => Real.log ((m : Real) / V) / 2
  let epsilon : Nat -> Real := fun r => -Real.log ((r : Real) / B) / 2
  have hscale : 0 <= scale := by dsimp only [scale]; positivity
  have hcoord (r : Nat) (q : Prod Nat Nat) :
      logArgument eta theta (fun _ => 0) epsilon (Prod.mk 1 r) q =
        coordinate ((q.1 : Real) / U) ((q.2 : Real) / V) 1 ((r : Real) / B) := by
    dsimp only [logArgument, eta, theta, epsilon, coordinate]
    rw [Real.log_one]
    ring
  have hArgs (r : Nat) (hr : Membership.mem R r)
      (q : Prod Nat Nat) (hq : Membership.mem (S.product T) q) :
      abs (logArgument eta theta (fun _ => 0) epsilon (Prod.mk 1 r) q) <= 3 := by
    rw [hcoord]
    exact coordinate_bound _ _ _ _ (ratio_bounds U _ hU (hNs _ (Finset.mem_product.mp hq).1))
      (ratio_bounds V _ hV (hMs _ (Finset.mem_product.mp hq).2))
      (And.intro (le_refl 1) (by norm_num)) (ratio_bounds B _ hB (hRows r hr))
  have hEstimate := hc M N1 N2 R S T a b hR hS hT scale eta theta epsilon hscale hArgs
  have hExact : smoothUnitMean R S T a b F scale eta theta epsilon =
      physicalUnitMean R S T a b F ell e X := by
    unfold smoothUnitMean physicalUnitMean
    apply Finset.sum_congr rfl
    intro r hr
    apply congrArg norm
    apply Finset.sum_congr rfl
    intro q hq
    have hn := hNs q.1 (Finset.mem_product.mp hq).1
    have hm := hMs q.2 (Finset.mem_product.mp hq).2
    have hrb := hRows r hr
    have harg := physical_argument ell e X B U V 1 (q.1 : Real) (q.2 : Real)
      (r : Real) 1 he hX hB hU hV (by norm_num)
      (lt_of_lt_of_le hU hn.1) (lt_of_lt_of_le hV hm.1)
      (lt_of_lt_of_le hB hrb.1) (by norm_num)
    rw [hcoord]
    dsimp only [scale]
    have harg' :
        (ell * Real.sqrt (e * U * V / (X * B))) *
          Real.exp (coordinate ((q.1 : Real) / U) ((q.2 : Real) / V) 1 ((r : Real) / B)) =
        ell * Real.sqrt (e * (q.1 : Real) * (q.2 : Real) / (X * (r : Real))) := by
      simpa only [div_one] using harg
    rw [harg']
  rw [hExact] at hEstimate
  exact hEstimate

end PrimeFactorOscillations.QuadraticPhysicalUnit


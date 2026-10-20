/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Assembly.DetectorPackets.QuadraticSmoothBandEstimate
import PrimeFactorOscillations.Proof.DetectorPackets.QuadraticSmoothBandCoordinates

/-!
# QuadraticPhysicalBand

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

namespace PrimeFactorOscillations.QuadraticPhysicalBand

open IntegerQuadraticPrefix QuadraticBandUniformPhase QuadraticSmoothBandRows
open QuadraticSmoothBandEstimate QuadraticSmoothBandCoordinates

def physicalBandMean (D : Nat) (R S T : Finset Nat) (a b : Nat -> Complex)
    (F : SchwartzMap Real Complex) (ell e X : Real) : Real :=
  (bandRows D R).sum (fun p => norm ((S.product T).sum (fun q =>
    coefficient a b p.1 p.2 q.1 q.2 *
      F (ell / (p.1 : Real) *
        Real.sqrt (e * (q.1 : Real) * (q.2 : Real) / (X * (p.2 : Real)))))))

theorem ratio_bounds (U x : Real) (hU : 0 < U) (hx : U <= x /\ x <= 2 * U) :
    1 <= x / U /\ x / U <= 2 := by
  have hlo := div_le_div_of_nonneg_right hx.1 hU.le
  have hhi := div_le_div_of_nonneg_right hx.2 hU.le
  refine And.intro ?_ ?_
  next => simpa only [div_self (ne_of_gt hU)] using hlo
  next =>
    calc
      _ <= 2 * U / U := hhi
      _ = _ := by field_simp

theorem physical_product_divisor_mean (F : SchwartzMap Real Complex)
    (A : Nat) (eps : Real) (heps : 0 < eps) :
    exists C : Real, 0 < C /\
      forall (D rowCap N1 N2 : Nat) (R S T : Finset Nat) (a b : Nat -> Complex),
      0 < D -> 0 < N1 -> 0 < N2 ->
      (forall r, Membership.mem R r -> Membership.mem (columns rowCap) r) ->
      (forall n, Membership.mem S n -> Membership.mem (columns N1) n) ->
      (forall m, Membership.mem T m -> Membership.mem (columns N2) m) ->
      exists L1 L2 : Nat,
        0 < L1 /\ 0 < L2 /\ D < 4 * (L1 * L2) /\ L1 * L2 <= 2 * D /\
        forall (ell e X B U V : Real), 0 <= ell -> 0 < e -> 0 < X ->
          0 < B -> 0 < U -> 0 < V ->
          (forall r, Membership.mem R r -> B <= (r : Real) /\ (r : Real) <= 2 * B) ->
          (forall n, Membership.mem S n -> U <= (n : Real) /\ (n : Real) <= 2 * U) ->
          (forall m, Membership.mem T m -> V <= (m : Real) /\ (m : Real) <= 2 * V) ->
          physicalBandMean D R S T a b F ell e X <=
            C * ((max N1 N2 : Nat) : Real) ^ eps /
              (1 + ell / (D : Real) * Real.sqrt (e * U * V / (X * B))) ^ A *
              pairBound rowCap N1 N2 S T a b (Prod.mk L1 L2) := by
  choose C hC hc using smooth_product_divisor_mean F 3 (by norm_num) A eps heps
  refine Exists.intro C (And.intro hC ?_)
  intro D rowCap N1 N2 R S T a b hD hN1 hN2 hR hS hT
  choose L1 L2 h1 h2 hlo hhi hb using
    hc D rowCap N1 N2 R S T a b hD hN1 hN2 hR hS hT
  refine Exists.intro L1 (Exists.intro L2
    (And.intro h1 (And.intro h2 (And.intro hlo (And.intro hhi ?_)))))
  intro ell e X B U V hell he hX hB hU hV hRows hNs hMs
  have hDR : (0 : Real) < (D : Real) := by exact_mod_cast hD
  let scale : Real := ell / (D : Real) * Real.sqrt (e * U * V / (X * B))
  let eta : Nat -> Real := fun n => Real.log ((n : Real) / U) / 2
  let theta : Nat -> Real := fun m => Real.log ((m : Real) / V) / 2
  let delta : Nat -> Real := fun d => -Real.log ((d : Real) / (D : Real))
  let epsilon : Nat -> Real := fun r => -Real.log ((r : Real) / B) / 2
  have hscale : 0 <= scale := by dsimp only [scale]; positivity
  have hcoord (p q : Prod Nat Nat) :
      logArgument eta theta delta epsilon p q =
        coordinate ((q.1 : Real) / U) ((q.2 : Real) / V)
          ((p.1 : Real) / (D : Real)) ((p.2 : Real) / B) := by
    dsimp only [logArgument, eta, theta, delta, epsilon, coordinate]
    ring
  have hdBounds (p : Prod Nat Nat) (hp : Membership.mem (bandRows D R) p) :
      (D : Real) <= (p.1 : Real) /\ (p.1 : Real) <= 2 * (D : Real) := by
    have h := Finset.mem_Ioc.mp (Finset.mem_product.mp hp).1
    exact And.intro (by exact_mod_cast h.1.le) (by exact_mod_cast h.2)
  have hArgs (p : Prod Nat Nat) (hp : Membership.mem (bandRows D R) p)
      (q : Prod Nat Nat) (hq : Membership.mem (S.product T) q) :
      abs (logArgument eta theta delta epsilon p q) <= 3 := by
    have hn := hNs q.1 (Finset.mem_product.mp hq).1
    have hm := hMs q.2 (Finset.mem_product.mp hq).2
    have hr := hRows p.2 (Finset.mem_product.mp hp).2
    rw [hcoord]
    exact coordinate_bound _ _ _ _ (ratio_bounds U _ hU hn)
      (ratio_bounds V _ hV hm) (ratio_bounds (D : Real) _ hDR (hdBounds p hp))
      (ratio_bounds B _ hB hr)
  have hEstimate := hb scale eta theta delta epsilon hscale hArgs
  have hExact : smoothBandMean D R S T a b F scale eta theta delta epsilon =
      physicalBandMean D R S T a b F ell e X := by
    unfold smoothBandMean physicalBandMean
    apply Finset.sum_congr rfl
    intro p hp
    apply congrArg norm
    apply Finset.sum_congr rfl
    intro q hq
    have hn := hNs q.1 (Finset.mem_product.mp hq).1
    have hm := hMs q.2 (Finset.mem_product.mp hq).2
    have hr := hRows p.2 (Finset.mem_product.mp hp).2
    have hd := hdBounds p hp
    rw [hcoord]
    dsimp only [scale]
    rw [physical_argument ell e X B U V (D : Real) (q.1 : Real) (q.2 : Real)
      (p.2 : Real) (p.1 : Real) he hX hB hU hV hDR
      (lt_of_lt_of_le hU hn.1) (lt_of_lt_of_le hV hm.1)
      (lt_of_lt_of_le hB hr.1) (lt_of_lt_of_le hDR hd.1)]
  rw [hExact] at hEstimate
  exact hEstimate

end PrimeFactorOscillations.QuadraticPhysicalBand


/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Assembly.DetectorPackets.QuadraticPhysicalBand

/-!
# QuadraticPhysicalBandWeight

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

namespace PrimeFactorOscillations.QuadraticPhysicalBandWeight

open QuadraticSmoothBandRows QuadraticPhysicalBand QuadraticBandUniformPhase
open IntegerQuadraticPrefix QuadraticDivisorMean

def weightedPhysicalBandMean (D : Nat) (R S T : Finset Nat) (a b : Nat -> Complex)
    (F : SchwartzMap Real Complex) (ell e X : Real) : Real :=
  (bandRows D R).sum (fun p => (1 / (p.1 : Real)) *
    norm ((S.product T).sum (fun q => coefficient a b p.1 p.2 q.1 q.2 *
      F (ell / (p.1 : Real) *
        Real.sqrt (e * (q.1 : Real) * (q.2 : Real) / (X * (p.2 : Real)))))))

theorem weightedPhysicalBandMean_le (D : Nat) (hD : 0 < D)
    (R S T : Finset Nat) (a b : Nat -> Complex)
    (F : SchwartzMap Real Complex) (ell e X : Real) :
    weightedPhysicalBandMean D R S T a b F ell e X <=
      (1 / (D : Real)) * physicalBandMean D R S T a b F ell e X := by
  have hDR : (0 : Real) < (D : Real) := by exact_mod_cast hD
  unfold weightedPhysicalBandMean physicalBandMean
  calc
    _ <= (bandRows D R).sum (fun p => (1 / (D : Real)) *
        norm ((S.product T).sum (fun q => coefficient a b p.1 p.2 q.1 q.2 *
          F (ell / (p.1 : Real) *
            Real.sqrt (e * (q.1 : Real) * (q.2 : Real) / (X * (p.2 : Real))))))) := by
      apply Finset.sum_le_sum
      intro p hp
      have hd := (Finset.mem_Ioc.mp (Finset.mem_product.mp hp).1).1
      have hdR : (D : Real) <= (p.1 : Real) := by exact_mod_cast hd.le
      exact mul_le_mul_of_nonneg_right (one_div_le_one_div_of_le hDR hdR) (norm_nonneg _)
    _ = _ := (Finset.mul_sum _ _ _).symm

theorem sqrt_pair_div_band (D L1 L2 : Nat) (hD : 0 < D)
    (h1 : 0 < L1) (h2 : 0 < L2) (hhi : L1 * L2 <= 2 * D) :
    Real.sqrt ((L1 : Real) * (L2 : Real)) / (D : Real) <=
      2 / Real.sqrt ((L1 : Real) * (L2 : Real)) := by
  let P : Real := (L1 : Real) * (L2 : Real)
  have hDR : (0 : Real) < (D : Real) := by exact_mod_cast hD
  have hP : 0 < P := by dsimp only [P]; exact_mod_cast Nat.mul_pos h1 h2
  have hPD : P <= 2 * (D : Real) := by dsimp only [P]; exact_mod_cast hhi
  have hroot : 0 < Real.sqrt P := Real.sqrt_pos.mpr hP
  have hsquare : Real.sqrt P ^ 2 = P := Real.sq_sqrt hP.le
  have hratio : P / (D : Real) <= 2 := by
    calc
      _ <= 2 * (D : Real) / (D : Real) :=
        div_le_div_of_nonneg_right hPD hDR.le
      _ = _ := by field_simp
  calc
    _ = (P / (D : Real)) / Real.sqrt P := by
      field_simp [ne_of_gt hDR, ne_of_gt hroot]
      nlinarith [hsquare]
    _ <= _ := div_le_div_of_nonneg_right hratio hroot.le

theorem weighted_physical_product_divisor_mean (F : SchwartzMap Real Complex)
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
          weightedPhysicalBandMean D R S T a b F ell e X <=
            C * ((max N1 N2 : Nat) : Real) ^ eps /
              (Real.sqrt ((L1 : Real) * (L2 : Real)) *
                (1 + ell / (D : Real) * Real.sqrt (e * U * V / (X * B))) ^ A) *
              Real.sqrt (prefixNorm rowCap (N1 / L1) * maskedMass 1 S a) *
              Real.sqrt (prefixNorm rowCap (N2 / L2) * maskedMass 1 T b) := by
  choose C hC hc using physical_product_divisor_mean F A eps heps
  refine Exists.intro (2 * C) (And.intro (by positivity) ?_)
  intro D rowCap N1 N2 R S T a b hD hN1 hN2 hR hS hT
  choose L1 L2 h1 h2 hlo hhi hb using
    hc D rowCap N1 N2 R S T a b hD hN1 hN2 hR hS hT
  refine Exists.intro L1 (Exists.intro L2
    (And.intro h1 (And.intro h2 (And.intro hlo (And.intro hhi ?_)))))
  intro ell e X B U V hell he hX hB hU hV hRows hNs hMs
  let Q : Real := (1 + ell / (D : Real) * Real.sqrt (e * U * V / (X * B))) ^ A
  let K : Real := C * ((max N1 N2 : Nat) : Real) ^ eps / Q *
    Real.sqrt (prefixNorm rowCap (N1 / L1) * maskedMass 1 S a) *
    Real.sqrt (prefixNorm rowCap (N2 / L2) * maskedMass 1 T b)
  have hK : 0 <= K := by dsimp only [K, Q]; positivity
  have hDR : (0 : Real) < (D : Real) := by exact_mod_cast hD
  have hphysical := hb ell e X B U V hell he hX hB hU hV hRows hNs hMs
  calc
    _ <= (1 / (D : Real)) * physicalBandMean D R S T a b F ell e X :=
      weightedPhysicalBandMean_le D hD R S T a b F ell e X
    _ <= (1 / (D : Real)) *
        (C * ((max N1 N2 : Nat) : Real) ^ eps / Q *
          pairBound rowCap N1 N2 S T a b (Prod.mk L1 L2)) :=
      mul_le_mul_of_nonneg_left hphysical (by positivity)
    _ = K * (Real.sqrt ((L1 : Real) * (L2 : Real)) / (D : Real)) := by
      dsimp only [K, pairBound]
      ring
    _ <= K * (2 / Real.sqrt ((L1 : Real) * (L2 : Real))) :=
      mul_le_mul_of_nonneg_left (sqrt_pair_div_band D L1 L2 hD h1 h2 hhi) hK
    _ = _ := by dsimp only [K, Q]; ring

end PrimeFactorOscillations.QuadraticPhysicalBandWeight


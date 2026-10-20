/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Assembly.DetectorPackets.QuadraticDyadicBand

/-!
# QuadraticProductBandEstimate

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

namespace PrimeFactorOscillations.QuadraticProductBandEstimate

open QuadraticCarrierPacket QuadraticCoprimeMean IntegerQuadraticPrefix
open QuadraticDivisorMean QuadraticDivisorBand QuadraticProductDivisor
open QuadraticProductBand QuadraticDyadicBand

def boxCost (M N1 N2 : Nat) (S T : Finset Nat) (a b : Nat -> Complex)
    (i : Prod Nat Nat) : Real :=
  Real.sqrt (((2 ^ i.1 : Nat) : Real) * ((2 ^ i.2 : Nat) : Real)) *
    Real.sqrt (prefixNorm M (N1 / 2 ^ i.1) * maskedMass 1 S a) *
    Real.sqrt (prefixNorm M (N2 / 2 ^ i.2) * maskedMass 1 T b)

theorem boxCost_nonneg (M N1 N2 : Nat) (S T : Finset Nat)
    (a b : Nat -> Complex) (i : Prod Nat Nat) :
    0 <= boxCost M N1 N2 S T a b i := by
  unfold boxCost
  positivity

theorem dyadic_box_mean (eps : Real) (heps : 0 < eps) :
    exists C : Real, 0 < C /\
      forall (M N1 N2 : Nat) (R S T : Finset Nat) (a b : Nat -> Complex),
      0 < N1 -> 0 < N2 ->
      (forall r, Membership.mem R r -> Membership.mem (columns M) r) ->
      (forall n, Membership.mem S n -> Membership.mem (columns N1) n) ->
      (forall m, Membership.mem T m -> Membership.mem (columns N2) m) ->
      forall i : Prod Nat Nat,
      (dyadicBox i).sum (fun p => maskedRowMean R S T a b p.1 p.2) <=
        C * ((max N1 N2 : Nat) : Real) ^ eps * boxCost M N1 N2 S T a b i := by
  choose C hC hc using divisor_band_mean eps heps
  refine Exists.intro C (And.intro hC ?_)
  intro M N1 N2 R S T a b hN1 hN2 hR hS hT i
  calc
    _ = (dyadicBlock i.1).sum (fun e1 =>
        (dyadicBlock i.2).sum (fun e2 => maskedRowMean R S T a b e1 e2)) :=
      Finset.sum_product _ _ _
    _ <= C * ((max N1 N2 : Nat) : Real) ^ eps *
        Real.sqrt (((dyadicBlock i.1).card : Real) * ((dyadicBlock i.2).card : Real)) *
          Real.sqrt (prefixNorm M (N1 / 2 ^ i.1) * maskedMass 1 S a) *
            Real.sqrt (prefixNorm M (N2 / 2 ^ i.2) * maskedMass 1 T b) :=
      hc M N1 N2 (2 ^ i.1) (2 ^ i.2) R S T (dyadicBlock i.1) (dyadicBlock i.2)
        a b hN1 hN2 (by positivity) (by positivity)
        (fun e he => (Finset.mem_Ico.mp he).1)
        (fun e he => (Finset.mem_Ico.mp he).1) hR hS hT
    _ = _ := by
      rw [dyadicBlock_card, dyadicBlock_card]
      unfold boxCost
      ring

theorem product_band_sum_bound (eps : Real) (heps : 0 < eps) :
    exists C : Real, 0 < C /\
      forall (D M N1 N2 : Nat) (R S T : Finset Nat) (a b : Nat -> Complex),
      0 < N1 -> 0 < N2 ->
      (forall r, Membership.mem R r -> Membership.mem (columns M) r) ->
      (forall n, Membership.mem S n -> Membership.mem (columns N1) n) ->
      (forall m, Membership.mem T m -> Membership.mem (columns N2) m) ->
      productBandMean D R S T a b <=
        C * ((max N1 N2 : Nat) : Real) ^ eps *
          (dyadicIndices D).sum (boxCost M N1 N2 S T a b) := by
  choose C hC hc using dyadic_box_mean eps heps
  refine Exists.intro C (And.intro hC ?_)
  intro D M N1 N2 R S T a b hN1 hN2 hR hS hT
  have hnonneg : forall p : Prod Nat Nat, 0 <= maskedRowMean R S T a b p.1 p.2 := by
    intro p
    unfold maskedRowMean
    exact Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  calc
    _ <= (factorBand D).sum (fun p => maskedRowMean R S T a b p.1 p.2) :=
      product_band_mean_le D R S T a b
    _ <= (dyadicIndices D).sum (fun i =>
        (dyadicBox i).sum (fun p => maskedRowMean R S T a b p.1 p.2)) :=
      factorBand_sum_le_boxes D _ hnonneg
    _ <= (dyadicIndices D).sum (fun i =>
        C * ((max N1 N2 : Nat) : Real) ^ eps * boxCost M N1 N2 S T a b i) := by
      apply Finset.sum_le_sum
      intro i hi
      exact hc M N1 N2 R S T a b hN1 hN2 hR hS hT i
    _ = _ := (Finset.mul_sum _ _ _).symm

theorem product_divisor_band_estimate (eps : Real) (heps : 0 < eps) :
    exists C : Real, 0 < C /\
      forall (D M N1 N2 : Nat) (R S T : Finset Nat) (a b : Nat -> Complex),
      0 < D -> 0 < N1 -> 0 < N2 ->
      (forall r, Membership.mem R r -> Membership.mem (columns M) r) ->
      (forall n, Membership.mem S n -> Membership.mem (columns N1) n) ->
      (forall m, Membership.mem T m -> Membership.mem (columns N2) m) ->
      exists L1 L2 : Nat,
        0 < L1 /\ 0 < L2 /\ D < 4 * (L1 * L2) /\ L1 * L2 <= 2 * D /\
        productBandMean D R S T a b <=
          C * ((max N1 N2 : Nat) : Real) ^ eps * (indexBound D : Real) ^ 2 *
            Real.sqrt ((L1 : Real) * (L2 : Real)) *
            Real.sqrt (prefixNorm M (N1 / L1) * maskedMass 1 S a) *
            Real.sqrt (prefixNorm M (N2 / L2) * maskedMass 1 T b) := by
  choose C hC hc using product_band_sum_bound eps heps
  refine Exists.intro C (And.intro hC ?_)
  intro D M N1 N2 R S T a b hD hN1 hN2 hR hS hT
  let F := boxCost M N1 N2 S T a b
  choose i hi hmax using
    Finset.exists_max_image (dyadicIndices D) F (dyadicIndices_nonempty D hD)
  have hsum : (dyadicIndices D).sum F <=
      ((dyadicIndices D).card : Real) * F i := by
    simpa only [nsmul_eq_mul] using
      Finset.sum_le_card_nsmul (dyadicIndices D) F (F i) hmax
  have hcard : ((dyadicIndices D).card : Real) <= (indexBound D : Real) ^ 2 := by
    exact_mod_cast dyadicIndices_card D
  have hF : 0 <= F i := boxCost_nonneg M N1 N2 S T a b i
  have hsum' : (dyadicIndices D).sum F <= (indexBound D : Real) ^ 2 * F i :=
    hsum.trans (mul_le_mul_of_nonneg_right hcard hF)
  have hscale : 0 <= C * ((max N1 N2 : Nat) : Real) ^ eps := by positivity
  have hbound : productBandMean D R S T a b <=
      C * ((max N1 N2 : Nat) : Real) ^ eps * (indexBound D : Real) ^ 2 * F i := by
    calc
      _ <= C * ((max N1 N2 : Nat) : Real) ^ eps * (dyadicIndices D).sum F :=
        hc D M N1 N2 R S T a b hN1 hN2 hR hS hT
      _ <= C * ((max N1 N2 : Nat) : Real) ^ eps * ((indexBound D : Real) ^ 2 * F i) :=
        mul_le_mul_of_nonneg_left hsum' hscale
      _ = _ := by ring
  have hgeometry := (Finset.mem_filter.mp hi).2
  refine Exists.intro (2 ^ i.1) (Exists.intro (2 ^ i.2) ?_)
  refine And.intro (by positivity) (And.intro (by positivity)
    (And.intro hgeometry.1 (And.intro hgeometry.2 ?_)))
  dsimp only [F, boxCost] at hbound
  calc
    _ <= C * ((max N1 N2 : Nat) : Real) ^ eps * (indexBound D : Real) ^ 2 *
        (Real.sqrt (((2 ^ i.1 : Nat) : Real) * ((2 ^ i.2 : Nat) : Real)) *
          Real.sqrt (prefixNorm M (N1 / 2 ^ i.1) * maskedMass 1 S a) *
          Real.sqrt (prefixNorm M (N2 / 2 ^ i.2) * maskedMass 1 T b)) := hbound
    _ = _ := by ring

end PrimeFactorOscillations.QuadraticProductBandEstimate

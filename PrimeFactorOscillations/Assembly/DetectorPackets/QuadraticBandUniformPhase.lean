/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Assembly.DetectorPackets.QuadraticProductBandSubpower

/-!
# QuadraticBandUniformPhase

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

namespace PrimeFactorOscillations.QuadraticBandUniformPhase

open QuadraticDivisorMean QuadraticProductBand QuadraticProductBandSubpower
open IntegerQuadraticPrefix

def pairChoices (D : Nat) : Finset (Prod Nat Nat) :=
  ((Finset.Icc 1 (2 * D)).product (Finset.Icc 1 (2 * D))).filter
    (fun p => D < 4 * (p.1 * p.2) /\ p.1 * p.2 <= 2 * D)

def pairBound (M N1 N2 : Nat) (S T : Finset Nat) (a b : Nat -> Complex)
    (p : Prod Nat Nat) : Real :=
  Real.sqrt ((p.1 : Real) * (p.2 : Real)) *
    Real.sqrt (prefixNorm M (N1 / p.1) * maskedMass 1 S a) *
    Real.sqrt (prefixNorm M (N2 / p.2) * maskedMass 1 T b)

theorem pairChoices_nonempty (D : Nat) (hD : 0 < D) : (pairChoices D).Nonempty := by
  refine Exists.intro (Prod.mk D 1) ?_
  unfold pairChoices
  apply Finset.mem_filter.mpr
  refine And.intro (Finset.mem_product.mpr (And.intro
    (Finset.mem_Icc.mpr (And.intro hD (by omega)))
    (Finset.mem_Icc.mpr (And.intro (by omega) (by omega))))) ?_
  simp only [Nat.mul_one]
  omega

theorem mem_pairChoices (D L1 L2 : Nat) (h1 : 0 < L1) (h2 : 0 < L2)
    (hlo : D < 4 * (L1 * L2)) (hhi : L1 * L2 <= 2 * D) :
    Membership.mem (pairChoices D) (Prod.mk L1 L2) := by
  have h1one : 1 <= L1 := by omega
  have h2one : 1 <= L2 := by omega
  have h1D : L1 <= 2 * D := by nlinarith
  have h2D : L2 <= 2 * D := by nlinarith
  unfold pairChoices
  exact Finset.mem_filter.mpr (And.intro (Finset.mem_product.mpr
    (And.intro (Finset.mem_Icc.mpr (And.intro h1one h1D))
      (Finset.mem_Icc.mpr (And.intro h2one h2D)))) (And.intro hlo hhi))

theorem maskedMass_unit_phase (e : Nat) (S : Finset Nat)
    (a : Nat -> Complex) (u : Nat -> Circle) :
    maskedMass e S (fun n => a n * (u n : Complex)) = maskedMass e S a := by
  unfold maskedMass
  apply Finset.sum_congr rfl
  intro n hn
  simp only [norm_mul, Circle.norm_coe, mul_one]

theorem product_divisor_mean_uniform_phase (eps : Real) (heps : 0 < eps) :
    exists C : Real, 0 < C /\
      forall (D M N1 N2 : Nat) (R S T : Finset Nat) (a b : Nat -> Complex),
      0 < D -> 0 < N1 -> 0 < N2 ->
      (forall r, Membership.mem R r -> Membership.mem (columns M) r) ->
      (forall n, Membership.mem S n -> Membership.mem (columns N1) n) ->
      (forall m, Membership.mem T m -> Membership.mem (columns N2) m) ->
      exists L1 L2 : Nat,
        0 < L1 /\ 0 < L2 /\ D < 4 * (L1 * L2) /\ L1 * L2 <= 2 * D /\
        forall u v : Nat -> Circle,
          productBandMean D R S T (fun n => a n * (u n : Complex))
            (fun m => b m * (v m : Complex)) <=
          C * ((max N1 N2 : Nat) : Real) ^ eps *
            pairBound M N1 N2 S T a b (Prod.mk L1 L2) := by
  choose C hC hc using source_product_divisor_mean eps heps
  refine Exists.intro C (And.intro hC ?_)
  intro D M N1 N2 R S T a b hD hN1 hN2 hR hS hT
  choose p hp hmax using (pairChoices D).exists_max_image
    (pairBound M N1 N2 S T a b) (pairChoices_nonempty D hD)
  have hmem := Finset.mem_filter.mp hp
  have hproduct := Finset.mem_product.mp hmem.1
  have h1 : 0 < p.1 := (Finset.mem_Icc.mp hproduct.1).1
  have h2 : 0 < p.2 := (Finset.mem_Icc.mp hproduct.2).1
  refine Exists.intro p.1 (Exists.intro p.2
    (And.intro h1 (And.intro h2 (And.intro hmem.2.1 (And.intro hmem.2.2 ?_)))))
  intro u v
  choose L1 L2 hL1 hL2 hlo hhi hb using
    hc D M N1 N2 R S T (fun n => a n * (u n : Complex))
      (fun m => b m * (v m : Complex)) hD hN1 hN2 hR hS hT
  rw [maskedMass_unit_phase 1 S a u, maskedMass_unit_phase 1 T b v] at hb
  have hcomp := hmax (Prod.mk L1 L2) (mem_pairChoices D L1 L2 hL1 hL2 hlo hhi)
  calc
    _ <= C * ((max N1 N2 : Nat) : Real) ^ eps *
        Real.sqrt ((L1 : Real) * (L2 : Real)) *
        Real.sqrt (prefixNorm M (N1 / L1) * maskedMass 1 S a) *
        Real.sqrt (prefixNorm M (N2 / L2) * maskedMass 1 T b) := hb
    _ = C * ((max N1 N2 : Nat) : Real) ^ eps *
        pairBound M N1 N2 S T a b (Prod.mk L1 L2) := by
      unfold pairBound
      ring
    _ <= _ := mul_le_mul_of_nonneg_left hcomp (by positivity)

end PrimeFactorOscillations.QuadraticBandUniformPhase


/-
Copyright (c) 2026 Prime Factor Oscillations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import Mathlib.NumberTheory.Harmonic.Bounds
import PrimeFactorOscillations.Mathlib.RingTheory.MvPolynomial.Symmetric.LargestWeightBounds

/-! # Largest inverse-label weights have a uniform harmonic bound -/

set_option autoImplicit false
set_option Elab.async false

namespace Finset

/-- The excess above C/r can only come from labels at most r; its total
is bounded by the harmonic budget independently of the input support. -/
theorem sum_positive_excess_le_harmonic (E : Finset Nat) (w : Nat -> Real)
    (C : Real) (hC : 0 <= C)
    (hpos : forall p, Membership.mem E p -> 0 < p)
    (hweight : forall p, Membership.mem E p -> w p <= C / p)
    (r : Nat) (hr : 1 <= r) :
    E.sum (fun p => max (w p - C / r) 0) <= C * (harmonic r : Real) := by
  have hrR : 0 < (r : Real) := by exact_mod_cast (show 0 < r by omega)
  let f := fun p : Nat => max (w p - C / r) 0
  have hexcess : E.sum f <= (Finset.Icc 1 r).sum (fun p => C / (p : Real)) := by
    have hrestrict : E.sum f = (E.filter (fun p => p <= r)).sum f := by
      symm
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro p hp hnot
      have hpr : r <= p := by
        have : Not (p <= r) := by
          intro hle
          exact hnot (Finset.mem_filter.mpr (And.intro hp hle))
        omega
      have hprR : (r : Real) <= p := by exact_mod_cast hpr
      have hw : w p <= C / r :=
        (hweight p hp).trans (div_le_div_of_nonneg_left hC hrR hprR)
      exact max_eq_right (sub_nonpos.mpr hw)
    rw [hrestrict]
    calc
      _ <= (E.filter (fun p => p <= r)).sum (fun p => C / (p : Real)) := by
        apply Finset.sum_le_sum
        intro p hp
        have he := (Finset.mem_filter.mp hp).1
        have hpR : 0 <= (p : Real) := Nat.cast_nonneg p
        have hnonneg := div_nonneg hC hpR
        have hw := hweight p he
        apply max_le
        next => linarith only [hw, div_nonneg hC hrR.le]
        next => exact hnonneg
      _ <= (Finset.Icc 1 r).sum (fun p => C / (p : Real)) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        next =>
          intro p hp
          have he := Finset.mem_filter.mp hp
          exact Finset.mem_Icc.mpr (And.intro (hpos p he.1) he.2)
        next =>
          intro p _ _
          exact div_nonneg hC (Nat.cast_nonneg p)
  have hharmonic : (Finset.Icc 1 r).sum (fun p => C / (p : Real)) =
      C * (harmonic r : Real) := by
    rw [harmonic_eq_sum_Icc]
    simp only [Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p _
    exact div_eq_mul_inv C (p : Real)
  rw [hharmonic] at hexcess
  exact hexcess

end Finset

namespace List

/-- A finite set of distinct positive labels with inverse-label weight
majorants has only harmonic total mass in its largest r weights. -/
theorem largestWeightSum_le_harmonic (E : Finset Nat) (w : Nat -> Real)
    (C : Real) (hC : 0 <= C)
    (hpos : forall p, Membership.mem E p -> 0 < p)
    (hweight : forall p, Membership.mem E p -> w p <= C / p)
    (r : Nat) (hr : 1 <= r) :
    largestWeightSum (E.toList.map w) r <= C * (1 + (harmonic r : Real)) := by
  have hrR : 0 < (r : Real) := by exact_mod_cast (show 0 < r by omega)
  let f := fun p : Nat => max (w p - C / r) 0
  have hcap := largestWeightSum_le_threshold_excess (E.toList.map w) r
    (C / r) (div_nonneg hC hrR.le)
  have hsum : ((E.toList.map w).map (fun a => max (a - C / r) 0)).sum =
      E.sum f := by simp [f]
  have hexcess := Finset.sum_positive_excess_le_harmonic E w C hC hpos hweight r hr
  have hcancel : (r : Real) * (C / r) = C := by field_simp
  rw [hsum, hcancel] at hcap
  nlinarith only [hcap, hexcess]

/-- Explicit logarithmic version, uniform in the finite input set. -/
theorem largestWeightSum_le_log (E : Finset Nat) (w : Nat -> Real)
    (C : Real) (hC : 0 <= C)
    (hpos : forall p, Membership.mem E p -> 0 < p)
    (hweight : forall p, Membership.mem E p -> w p <= C / p)
    (r : Nat) (hr : 1 <= r) :
    largestWeightSum (E.toList.map w) r <= C * (2 + Real.log r) := by
  have h := largestWeightSum_le_harmonic E w C hC hpos hweight r hr
  have hh := harmonic_le_one_add_log r
  have hm := mul_le_mul_of_nonneg_left hh hC
  nlinarith only [h, hm]

end List

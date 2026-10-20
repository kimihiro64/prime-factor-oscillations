/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Assembly.DetectorPackets.QuadraticDivisorMean

/-!
# QuadraticRangePairEnvelope

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

namespace PrimeFactorOscillations.QuadraticRangePairEnvelope

open IntegerQuadraticPrefix QuadraticDivisorMean

def admissiblePairs (Y Z : Nat) : Finset (Prod Nat Nat) :=
  ((Finset.Icc 1 (2 * Z)).product (Finset.Icc 1 (2 * Z))).filter
    (fun p => Y < 8 * (p.1 * p.2) /\ p.1 * p.2 <= 2 * Z)

theorem admissiblePairs_mem (Y Z : Nat) (p : Prod Nat Nat) :
    Membership.mem (admissiblePairs Y Z) p <->
      0 < p.1 /\ 0 < p.2 /\ Y < 8 * (p.1 * p.2) /\ p.1 * p.2 <= 2 * Z := by
  constructor
  . intro h
    have hf := Finset.mem_filter.mp h
    have hb := Finset.mem_product.mp hf.1
    exact And.intro (Finset.mem_Icc.mp hb.1).1
      (And.intro (Finset.mem_Icc.mp hb.2).1 hf.2)
  . intro h
    have h1 : p.1 <= p.1 * p.2 := by
      have hp2 : 1 <= p.2 := h.2.1
      simpa only [mul_one] using Nat.mul_le_mul_left p.1 hp2
    have h2 : p.2 <= p.1 * p.2 := by
      have hp1 : 1 <= p.1 := h.1
      simpa only [one_mul] using Nat.mul_le_mul_right p.2 hp1
    exact Finset.mem_filter.mpr (And.intro
      (Finset.mem_product.mpr (And.intro
        (Finset.mem_Icc.mpr (And.intro h.1 (h1.trans h.2.2.2)))
        (Finset.mem_Icc.mpr (And.intro h.2.1 (h2.trans h.2.2.2))))) h.2.2)

theorem admissiblePairs_nonempty (Y Z : Nat) (hZ : 0 < Z) (hYZ : Y <= Z) :
    (admissiblePairs Y Z).Nonempty := by
  have hZ8 : Z < 8 * Z := by
    calc
      _ = 1 * Z := by simp
      _ < 8 * Z := Nat.mul_lt_mul_of_pos_right (by decide) hZ
  have hZ2 : Z <= 2 * Z := by
    calc
      _ = 1 * Z := by simp
      _ <= 2 * Z := Nat.mul_le_mul_right Z (by decide)
  refine Exists.intro (Prod.mk Z 1) ((admissiblePairs_mem Y Z (Prod.mk Z 1)).mpr ?_)
  change 0 < Z /\ 0 < 1 /\ Y < 8 * (Z * 1) /\ Z * 1 <= 2 * Z
  simpa only [mul_one] using
    And.intro hZ (And.intro Nat.zero_lt_one (And.intro (hYZ.trans_lt hZ8) hZ2))

def pairEnvelope (M N1 N2 : Nat) (S T : Finset Nat) (a b : Nat -> Complex)
    (p : Prod Nat Nat) : Real :=
  (1 / Real.sqrt ((p.1 : Real) * (p.2 : Real))) *
    Real.sqrt (prefixNorm M (N1 / p.1) * maskedMass 1 S a) *
    Real.sqrt (prefixNorm M (N2 / p.2) * maskedMass 1 T b)

theorem pairEnvelope_nonneg (M N1 N2 : Nat) (S T : Finset Nat)
    (a b : Nat -> Complex) (p : Prod Nat Nat) :
    0 <= pairEnvelope M N1 N2 S T a b p := by
  unfold pairEnvelope
  positivity

end PrimeFactorOscillations.QuadraticRangePairEnvelope


/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# QuadraticNeutralLocal

Maintained extraction of completed detector/packet proof components.
All original theorem hypotheses and retained proof bodies are preserved.
This module alone asserts no improved zero-free boundary.
-/

set_option autoImplicit false
set_option Elab.async false

/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

/-!
# The common local main term in quadratic Poisson transport

The variables A and B are the two target Euler coordinates, q is the
prime norm, r is the square-frequency coordinate, and t is 1/q.
At r=t the local numerator is exactly the primal square-density
numerator. This algebra does not assert a bound for the neutral packet.
-/


noncomputable section
namespace PrimeFactorOscillations.QuadraticNeutralLocal

def localSeries (q r A B : Complex) : Complex :=
  (1 + (q - 1) * r * A * B) / (1 - r) - A - B

def squareDensity (t A B : Complex) : Complex :=
  1 - (1 - t) * (A + B) + (1 - t) * A * B

theorem local_numerator (q r A B : Complex) (hr : Not (1 - r = 0)) :
    (1 - r) * localSeries q r A B =
      1 - (1 - r) * (A + B) + (q - 1) * r * A * B := by
  unfold localSeries
  field_simp [hr]
  ring

theorem common_residue_numerator (q t A B : Complex)
    (hqt : q * t = 1) (ht : Not (1 - t = 0)) :
    (1 - t) * localSeries q t A B = squareDensity t A B := by
  rw [local_numerator q t A B ht]
  have hrel : (q - 1) * t = 1 - t := by
    calc
      _ = q * t - t := by ring
      _ = 1 - t := by rw [hqt]
  rw [hrel]
  rfl

theorem full_correction_at_residue (t A B : Complex)
    (hA : Not (1 - A = 0)) (hB : Not (1 - B = 0)) :
    squareDensity t A B / ((1 - A) * (1 - B)) =
      (1 - t) + t / ((1 - A) * (1 - B)) := by
  unfold squareDensity
  field_simp [hA, hB]
  ring

end PrimeFactorOscillations.QuadraticNeutralLocal


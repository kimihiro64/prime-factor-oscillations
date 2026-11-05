/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Algebra for the septic Jacobi edge candidate

The eight-term signed product is retained before using the Jacobi relations.
These are supporting algebraic lemmas, not a new prime-field theorem.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

namespace Metaplectic.G2Seven.Edge

theorem signed_beta_identity {R : Type*} [CommRing R]
    (a aa b bb c cc d dd p : R)
    (hb : b * bb = p) (hc : c * cc = p) (hd : d * dd = p)
    (hac : a * c = b * d) (haac : aa * cc = bb * dd) :
    (b - c) * (d - bb) * (cc - dd) =
      p * ((a + c - b - d) - (aa + cc - bb - dd)) := by
  calc
    (b - c) * (d - bb) * (cc - dd) =
        cc * (b * d - a * c) - c * (bb * dd - aa * cc) +
        (a - aa - d + bb) * (c * cc) +
        (c - b) * (d * dd) + (dd - cc) * (b * bb) := by ring
    _ = p * ((a + c - b - d) - (aa + cc - bb - dd)) := by
      rw [hac, haac, hb, hc, hd]
      ring

theorem triple_product_bound (a b c : Real)
    (ha : 0 <= a) (hb : 0 <= b) (hc : 0 <= c) :
    27 * a * b * c <= (a + b + c) ^ 3 := by
  have h1 : 0 <= (a - b) ^ 2 * (a + b + 7 * c) :=
    mul_nonneg (sq_nonneg _) (by linarith)
  have h2 : 0 <= (b - c) ^ 2 * (b + c + 7 * a) :=
    mul_nonneg (sq_nonneg _) (by linarith)
  have h3 : 0 <= (c - a) ^ 2 * (c + a + 7 * b) :=
    mul_nonneg (sq_nonneg _) (by linarith)
  have hid : 2 * ((a + b + c) ^ 3 - 27 * a * b * c) =
      (a - b) ^ 2 * (a + b + 7 * c) +
      (b - c) ^ 2 * (b + c + 7 * a) +
      (c - a) ^ 2 * (c + a + 7 * b) := by ring
  nlinarith only [h1, h2, h3, hid]

end Metaplectic.G2Seven.Edge

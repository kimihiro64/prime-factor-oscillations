/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring

/-! Signed quadratic control identities and their cross comparison. -/

/-
Symbolic audit of the old-packet covariance cancellation.
This checks universal algebra, not any finite orbit sample or growth theorem.
Normalized interpretations require positive denominators as in the paper note.
-/
set_option autoImplicit false

namespace Real

theorem control_square_identity
    (mu nu v w c alpha : Real) :
    (mu ^ 2 * w - 2 * mu * nu * c + nu ^ 2 * v) *
        (v - 2 * alpha * c + alpha ^ 2 * w) -
      (v * w - c ^ 2) * (mu - alpha * nu) ^ 2 =
      ((mu * w - nu * c) * alpha - (mu * c - nu * v)) ^ 2 := by
  ring

theorem gain_square_identity
    (mu nu v w c : Real) :
    v * (mu ^ 2 * w - 2 * mu * nu * c + nu ^ 2 * v) -
      (v * w - c ^ 2) * mu ^ 2 =
      (nu * v - mu * c) ^ 2 := by
  ring

theorem gain_cross_nonnegative
    (mu nu v w c : Real) :
    (v * w - c ^ 2) * mu ^ 2 <=
      v * (mu ^ 2 * w - 2 * mu * nu * c + nu ^ 2 * v) := by
  calc
    (v * w - c ^ 2) * mu ^ 2 <=
        (v * w - c ^ 2) * mu ^ 2 + (nu * v - mu * c) ^ 2 :=
      le_add_of_nonneg_right (sq_nonneg (nu * v - mu * c))
    _ = v * (mu ^ 2 * w - 2 * mu * nu * c + nu ^ 2 * v) := by
      ring

theorem positive_intercept_cross_identity
    (mu nu v w c : Real) :
    mu * (mu * w - nu * c) - nu * (mu * c - nu * v) =
      mu ^ 2 * w - 2 * mu * nu * c + nu ^ 2 * v := by
  ring

end Real

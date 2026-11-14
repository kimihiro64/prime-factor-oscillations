/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.Linarith

/-! # A cross-multiplied Neumann inverse bound

The inverse is obtained from the convergent geometric series. Its norm bound
is kept in multiplicative form, with the positive gap hypothesis explicit.
The matrix consumer uses the checked Euclidean operator norm, not a different
matrix norm inferred from a type alias.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

variable {A : Type*} [NormedRing A] [HasSummableGeomSeries A]

theorem neumann_norm_certificate (x : A) (rho : Real)
    (hNorm : norm x <= rho) (hRho : rho < 1) :
    (1 - rho) * norm (Ring.inverse (1 - x)) <= norm (1 : A) := by
  have hx : norm x < 1 := lt_of_le_of_lt hNorm hRho
  have hUnit : IsUnit (1 - x) := isUnit_one_sub_of_norm_lt_one hx
  have hCancel : (1 - x) * Ring.inverse (1 - x) = 1 :=
    Ring.mul_inverse_cancel (1 - x) hUnit
  have hEq : Ring.inverse (1 - x) = 1 + x * Ring.inverse (1 - x) := by
    apply sub_eq_iff_eq_add.mp
    simpa only [sub_mul, one_mul] using hCancel
  have hBound : norm (Ring.inverse (1 - x)) <=
      norm (1 : A) + norm x * norm (Ring.inverse (1 - x)) := by
    calc
      _ = norm (1 + x * Ring.inverse (1 - x)) := congrArg norm hEq
      _ <= norm (1 : A) + norm (x * Ring.inverse (1 - x)) := norm_add_le _ _
      _ <= _ := add_le_add (le_refl (norm (1 : A)))
        (norm_mul_le x (Ring.inverse (1 - x)))
  have hSharp : (1 - norm x) * norm (Ring.inverse (1 - x)) <= norm (1 : A) := by
    nlinarith only [hBound]
  calc
    _ <= (1 - norm x) * norm (Ring.inverse (1 - x)) :=
      mul_le_mul_of_nonneg_right (sub_le_sub_left hNorm 1) (norm_nonneg _)
    _ <= _ := hSharp

end PrimeFactorOscillations

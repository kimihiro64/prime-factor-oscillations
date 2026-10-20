/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import Mathlib.Algebra.Polynomial.Div
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# Polynomial square filters for reciprocal transport

A polynomial filter with value one at zero gives a finite reciprocal-polynomial
observable with exact unit displacement response. Its complete remainder is
the displacement multiplied by the square of the filter.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace Polynomial

/-- Realize a square-filtered displacement using at most twice the filter degree. -/
theorem exists_square_filter_transport_polynomial (H : Polynomial Real)
    (hH0 : Polynomial.eval 0 H = 1) :
    exists G : Polynomial Real,
      G.natDegree <= 2 * H.natDegree /\
      forall r p : Real, Not (p = 0) ->
        r * Polynomial.eval (r / p) G =
          (p - r) * (1 - (Polynomial.eval (r / p) H) ^ 2) := by
  let R : Polynomial Real := 1 - H ^ 2
  have hR0 : R.coeff 0 = 0 := by
    rw [Polynomial.coeff_zero_eq_eval_zero]
    simp [R, hH0]
  have hdiv := Polynomial.X_dvd_iff.mpr hR0
  let q : Polynomial Real := Classical.choose hdiv
  have hq : R = Polynomial.X * q := Classical.choose_spec hdiv
  have hRdeg : R.natDegree <= 2 * H.natDegree := by
    calc
      R.natDegree <= max (1 : Polynomial Real).natDegree (H ^ 2).natDegree :=
        Polynomial.natDegree_sub_le 1 (H ^ 2)
      _ = 2 * H.natDegree := by simp
  have hqdeg : q.natDegree <= R.natDegree := by
    by_cases hq0 : q = 0
    case pos => simp [hq0]
    case neg =>
      rw [hq, Polynomial.natDegree_X_mul hq0]
      exact Nat.le_succ q.natDegree
  have hxqdeg : (Polynomial.X * q).natDegree <= R.natDegree := by
    rw [<- hq]
  refine Exists.intro (q - Polynomial.X * q) ?_
  constructor
  case left =>
    exact le_trans (Polynomial.natDegree_sub_le q (Polynomial.X * q))
      (le_trans (max_le hqdeg hxqdeg) hRdeg)
  case right =>
    intro r p hp
    have heval := congrArg (Polynomial.eval (r / p)) hq
    simp only [R, Polynomial.eval_sub, Polynomial.eval_one,
      Polynomial.eval_pow, Polynomial.eval_mul, Polynomial.eval_X] at heval
    rw [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_X, heval]
    field_simp [hp]

end Polynomial

namespace Real

/-- A bounded square filter preserves the complete signed displacement factor. -/
theorem reciprocal_square_filter_mul_bounds (d h eta : Real)
    (hd : 0 <= d) (hh : abs h <= eta) :
    (1 - eta ^ 2) * d <= d * (1 - h ^ 2) /\
      d * (1 - h ^ 2) <= d := by
  have hbounds := abs_le.mp hh
  have hsq : h ^ 2 <= eta ^ 2 := by
    have hprod := mul_nonneg (sub_nonneg.mpr hbounds.2)
      (by linarith only [hbounds.1] : 0 <= eta + h)
    nlinarith only [hprod]
  have hscaled := mul_le_mul_of_nonneg_left hsq hd
  have hnonneg := mul_nonneg hd (sq_nonneg h)
  exact And.intro (by nlinarith only [hscaled])
    (by nlinarith only [hnonneg])

end Real

/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# QuadraticSmoothBandCoordinates

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

namespace PrimeFactorOscillations.QuadraticSmoothBandCoordinates

def coordinate (u v w z : Real) : Real :=
  Real.log u / 2 + Real.log v / 2 - Real.log w - Real.log z / 2

theorem coordinate_bound (u v w z : Real)
    (hu : 1 <= u /\ u <= 2) (hv : 1 <= v /\ v <= 2)
    (hw : 1 <= w /\ w <= 2) (hz : 1 <= z /\ z <= 2) :
    abs (coordinate u v w z) <= 3 := by
  have hb (x : Real) (hx : 1 <= x /\ x <= 2) : 0 <= Real.log x /\ Real.log x <= 1 := by
    have hp : 0 < x := by linarith [hx.1]
    have h := Real.log_le_sub_one_of_pos hp
    exact And.intro (Real.log_nonneg hx.1) (by linarith [hx.2])
  have h1 := hb u hu
  have h2 := hb v hv
  have h3 := hb w hw
  have h4 := hb z hz
  unfold coordinate
  apply abs_le.mpr
  constructor <;> linarith

theorem exp_coordinate (u v w z : Real)
    (hu : 0 < u) (hv : 0 < v) (hw : 0 < w) (hz : 0 < z) :
    Real.exp (coordinate u v w z) =
      Real.sqrt u * Real.sqrt v / (w * Real.sqrt z) := by
  unfold coordinate
  rw [Real.exp_sub, Real.exp_sub, Real.exp_add,
    Real.exp_half (Real.log u), Real.exp_half (Real.log v), Real.exp_half (Real.log z),
    Real.exp_log hu, Real.exp_log hv, Real.exp_log hw, Real.exp_log hz]
  ring

theorem physical_argument (ell e M B U V D n m r d : Real)
    (he : 0 < e) (hM : 0 < M) (hB : 0 < B) (hU : 0 < U) (hV : 0 < V)
    (hD : 0 < D) (hn : 0 < n) (hm : 0 < m) (hr : 0 < r) (hd : 0 < d) :
    (ell / D * Real.sqrt (e * U * V / (M * B))) *
        Real.exp (coordinate (n / U) (m / V) (d / D) (r / B)) =
      ell / d * Real.sqrt (e * n * m / (M * r)) := by
  let base : Real := e * U * V / (M * B)
  have hb : 0 < base := by dsimp only [base]; positivity
  have hroot : Real.sqrt base * Real.sqrt (n / U) * Real.sqrt (m / V) /
      Real.sqrt (r / B) = Real.sqrt (e * n * m / (M * r)) := by
    calc
      _ = Real.sqrt (base * (n / U) * (m / V) / (r / B)) := by
        rw [Real.sqrt_div (by positivity : 0 <= base * (n / U) * (m / V)) (r / B),
          Real.sqrt_mul (by positivity : 0 <= base * (n / U)) (m / V),
          Real.sqrt_mul (by positivity : 0 <= base) (n / U)]
      _ = _ := congrArg Real.sqrt (by
        dsimp only [base]
        field_simp [ne_of_gt hU, ne_of_gt hV, ne_of_gt hM, ne_of_gt hB, ne_of_gt hr] <;> ring)
  have hsqrt : 0 < Real.sqrt (r / B) := Real.sqrt_pos.mpr (div_pos hr hB)
  rw [exp_coordinate (n / U) (m / V) (d / D) (r / B)
    (div_pos hn hU) (div_pos hm hV) (div_pos hd hD) (div_pos hr hB)]
  change (ell / D * Real.sqrt base) *
    (Real.sqrt (n / U) * Real.sqrt (m / V) / ((d / D) * Real.sqrt (r / B))) = _
  calc
    _ = (ell / d) * (Real.sqrt base * Real.sqrt (n / U) * Real.sqrt (m / V) /
        Real.sqrt (r / B)) := by
      field_simp [ne_of_gt hD, ne_of_gt hd, ne_of_gt hsqrt] <;> ring
    _ = _ := by rw [hroot]

end PrimeFactorOscillations.QuadraticSmoothBandCoordinates


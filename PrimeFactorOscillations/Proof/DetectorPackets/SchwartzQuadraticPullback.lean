/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# SchwartzQuadraticPullback

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

namespace PrimeFactorOscillations.SchwartzQuadraticPullback

theorem quadratic_temperate (a : Real) :
    Function.HasTemperateGrowth (fun x : Real => a * x ^ 2) := by
  have hi : Function.HasTemperateGrowth (fun x : Real => x) :=
    Function.HasTemperateGrowth.id
  have hc : Function.HasTemperateGrowth (fun _ : Real => a) :=
    Function.HasTemperateGrowth.const a
  exact hc.mul (hi.fun_pow 2)

theorem quadratic_upper (a : Real) (ha : Not (a = 0)) :
    exists (k : Nat) (C : Real), forall x : Real,
      norm x <= C * (1 + norm (a * x ^ 2)) ^ k := by
  refine Exists.intro 1 (Exists.intro (1 + 1 / abs a) ?_)
  intro x
  have hA : 0 < abs a := abs_pos.mpr ha
  have hx : abs x <= 1 + x ^ 2 := by
    have hsq : abs x ^ 2 = x ^ 2 := sq_abs x
    nlinarith [sq_nonneg (abs x - 1 / 2)]
  have heq : (1 + 1 / abs a) * (1 + abs a * x ^ 2) =
      1 + x ^ 2 + (1 / abs a + abs a * x ^ 2) := by
    field_simp [ne_of_gt hA]
    ring
  simp only [Real.norm_eq_abs, pow_one, abs_mul, abs_of_nonneg (sq_nonneg x)]
  calc
    _ <= 1 + x ^ 2 := hx
    _ <= _ := by
      rw [heq]
      have h1 : 0 <= 1 / abs a := by positivity
      have h2 : 0 <= abs a * x ^ 2 := mul_nonneg (abs_nonneg a) (sq_nonneg x)
      linarith

def quadraticProfile (a : Real) (ha : Not (a = 0)) (F : SchwartzMap Real Complex) :
    SchwartzMap Real Complex :=
  (SchwartzMap.compCLM Complex (quadratic_temperate a) (quadratic_upper a ha)) F

theorem quadraticProfile_apply (a : Real) (ha : Not (a = 0))
    (F : SchwartzMap Real Complex) (x : Real) :
    quadraticProfile a ha F x = F (a * x ^ 2) := by
  exact congrFun
    (SchwartzMap.compCLM_apply Complex (quadratic_temperate a) (quadratic_upper a ha) F) x

theorem quadraticProfile_even (a : Real) (ha : Not (a = 0))
    (F : SchwartzMap Real Complex) (x : Real) :
    quadraticProfile a ha F (-x) = quadraticProfile a ha F x := by
  rw [quadraticProfile_apply, quadraticProfile_apply, neg_sq]

end PrimeFactorOscillations.SchwartzQuadraticPullback


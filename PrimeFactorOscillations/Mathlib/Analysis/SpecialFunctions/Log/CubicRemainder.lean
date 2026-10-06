/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import PrimeFactorOscillations.Mathlib.Analysis.SpecialFunctions.Log.NormalizedLinearProduct

/-!
# Cubic remainder for the real logarithm

Explicit two-sided Taylor control on the full nonnegative half-line.
-/

set_option autoImplicit false
set_option Elab.async false
open Set
namespace Real

theorem log_one_add_cubic_remainder_bounds (u : Real) (hu : 0 <= u) :
    0 <= Real.log (1 + u) - u + u ^ (2 : Nat) / 2 /\
      Real.log (1 + u) - u + u ^ (2 : Nat) / 2 <= u ^ (3 : Nat) / 3 := by
  have hQuadratic := Real.sub_log_one_add_bounds u hu
  refine And.intro (by nlinarith [hQuadratic.2]) ?_
  let g : Real -> Real := fun x => x ^ (3 : Nat) / 3 -
    (Real.log (1 + x) - x + x ^ (2 : Nat) / 2)
  have hDeriv (x : Real) (hx : 0 <= x) :
      HasDerivAt g (x ^ (3 : Nat) / (1 + x)) x := by
    have hOne : Not (1 + x = 0) := by linarith
    have hLog := (Real.hasDerivAt_log hOne).comp x
      ((hasDerivAt_const x (1 : Real)).add (hasDerivAt_id x))
    have ht := (((hasDerivAt_id x).pow 3).div_const 3).sub
      ((hLog.sub (hasDerivAt_id x)).add (((hasDerivAt_id x).pow 2).div_const 2))
    convert ht using 1
    . funext t
      rfl
    . norm_num
      field_simp
      <;> ring
  have hMono : MonotoneOn g (Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    . intro x hx
      exact (hDeriv x hx).continuousAt.continuousWithinAt
    . intro x hx
      have hx0 : 0 <= x := interior_subset hx
      exact (hDeriv x hx0).differentiableAt.differentiableWithinAt
    . intro x hx
      have hx0 : 0 <= x := interior_subset hx
      rw [(hDeriv x hx0).deriv]
      positivity
  have ht := hMono (show Membership.mem (Ici (0 : Real)) 0 by simp) hu hu
  dsimp [g] at ht
  norm_num at ht
  linarith

end Real

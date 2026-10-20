/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import Mathlib.Analysis.MellinTransform
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# MellinPoleFilter

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
# Finite Mellin dilation filters and the live bad-zero strip

Finite dilation combinations give actual windows with the computed Mellin
multiplier. A reflected denominator filter is nonzero on the target
3/4 < Re(rho) <= 7/8 strip and at the principal window moment 1,
provided the source denominator has zeros only on its two stated lines.
This is a filter construction, not a moment or zero-free estimate.
-/


noncomputable section
namespace PrimeFactorOscillations.MellinPoleFilter

def window {I : Type} (S : Finset I) (c : I -> Complex)
    (a : I -> Real) (W : Real -> Complex) (t : Real) : Complex :=
  S.sum (fun i => c i * W (a i * t))

theorem mellin_window {I : Type} (S : Finset I) (c : I -> Complex)
    (a : I -> Real) (W : Real -> Complex) (s : Complex)
    (ha : forall i, Membership.mem S i -> 0 < a i)
    (hc : forall i, Membership.mem S i ->
      MellinConvergent (fun t => c i * W (a i * t)) s) :
    mellin (window S c a W) s =
      (S.sum (fun i => c i * (a i : Complex)^(-s))) * mellin W s := by
  classical
  unfold window mellin
  simp_rw [smul_eq_mul, Finset.mul_sum]
  rw [MeasureTheory.integral_finsetSum S]
  . calc
      _ = S.sum (fun i => c i * ((a i : Complex)^(-s) * mellin W s)) := by
        apply Finset.sum_congr rfl
        intro i hi
        change mellin (fun t => c i * W (a i * t)) s = _
        have he := mellin_const_smul (fun t => W (a i * t)) s (c i)
        simpa only [smul_eq_mul, mellin_comp_mul_left W s (ha i hi)] using he
      _ = _ := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i hi
        simp only [mellin, smul_eq_mul, mul_assoc]
  . intro i hi
    simpa only [MellinConvergent, MeasureTheory.IntegrableOn, smul_eq_mul] using hc i hi

def reflected (D : Complex -> Complex) (z : Complex) : Complex :=
  D (z + 1/2) * D (3/2 - z)

theorem reflected_symm (D : Complex -> Complex) (z : Complex) :
    reflected D (1-z) = reflected D z := by
  unfold reflected
  have h1 : (1-z)+1/2 = 3/2-z := by ring
  have h2 : 3/2-(1-z) = z+1/2 := by ring
  rw [h1,h2,mul_comm]

theorem reflected_bad_zero_nonzero (D : Complex -> Complex)
    (hD : forall s : Complex, Not (s.re = 1) -> Not (s.re = 5/4) ->
      Not (D s = 0))
    (rho : Complex) (hlo : 3/4 < rho.re) (hhi : rho.re <= 7/8) :
    Not (reflected D (rho-1/2) = 0) := by
  unfold reflected
  have h1 : (rho-1/2)+1/2 = rho := by ring
  have h2 : 3/2-(rho-1/2) = 2-rho := by ring
  rw [h1,h2]
  apply mul_ne_zero
  . exact hD rho (by linarith) (by linarith)
  . apply hD (2-rho)
    all_goals
      have hre : (2-rho).re = 2-rho.re := by simp
      rw [hre]
      linarith

theorem reflected_principal_nonzero (D : Complex -> Complex)
    (hD : forall s : Complex, Not (s.re = 1) -> Not (s.re = 5/4) ->
      Not (D s = 0)) :
    Not (reflected D 1 = 0) := by
  unfold reflected
  apply mul_ne_zero
  . apply hD
    all_goals norm_num
  . apply hD
    all_goals norm_num

end PrimeFactorOscillations.MellinPoleFilter

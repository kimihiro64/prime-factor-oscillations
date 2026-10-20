/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Assembly.DetectorPackets.IntegerGaussianPhase

/-!
# IntegerGaussianAbelPhase

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

namespace PrimeFactorOscillations.IntegerGaussianAbelPhase

open IntegerGaussianPhase

def damping (eps lambda : Real) : Real :=
  Real.pi * eps / (eps ^ 2 + lambda ^ 2)

def basePhase (lambda : Real) : Real := -Real.pi / lambda

def phaseShift (eps lambda : Real) : Real :=
  Real.pi * eps ^ 2 / (lambda * (eps ^ 2 + lambda ^ 2))

def remainder (eps lambda : Real) : Complex :=
  tsum (phaseError (damping eps lambda) (basePhase lambda) (phaseShift eps lambda))

theorem exact_dual_phase (eps lambda : Real) (he : 0 < eps) (hl : 0 < lambda) :
    basePhase lambda + phaseShift eps lambda =
      -Real.pi * lambda / (eps ^ 2 + lambda ^ 2) := by
  have hd : 0 < eps ^ 2 + lambda ^ 2 := by positivity
  unfold basePhase phaseShift
  field_simp
  <;> ring

theorem exact_error_ratio (C eps lambda : Real) (he : 0 < eps) (hl : 0 < lambda) :
    C * abs (phaseShift eps lambda) / (damping eps lambda) ^ 2 =
      C * (eps ^ 2 + lambda ^ 2) / (Real.pi * lambda) := by
  have hd : 0 < eps ^ 2 + lambda ^ 2 := by positivity
  have hs : 0 < phaseShift eps lambda := by unfold phaseShift; positivity
  rw [abs_of_pos hs]
  unfold phaseShift damping
  field_simp
  <;> ring

theorem normalized_phase_error_bound :
    exists C : Real, 0 < C /\ forall (lambda eps : Real), 0 < lambda ->
      0 < eps -> eps <= 1 ->
      Summable (phaseError (damping eps lambda) (basePhase lambda) (phaseShift eps lambda)) /\
      Real.sqrt eps * norm (remainder eps lambda) <=
        (C * (1 + lambda ^ 2) / (Real.pi * lambda)) * Real.sqrt eps := by
  choose C hC hc using gaussian_phase_error
  refine Exists.intro C (And.intro hC ?_)
  intro lambda eps hl he he1
  have hd : 0 < damping eps lambda := by unfold damping; positivity
  have h := hc (damping eps lambda) (basePhase lambda) (phaseShift eps lambda) hd
  refine And.intro h.1 ?_
  have hNorm : norm (remainder eps lambda) <=
      C * (eps ^ 2 + lambda ^ 2) / (Real.pi * lambda) := by
    exact h.2.trans_eq (exact_error_ratio C eps lambda he hl)
  have hsquare : eps ^ 2 <= 1 := by nlinarith
  have hUpper : C * (eps ^ 2 + lambda ^ 2) / (Real.pi * lambda) <=
      C * (1 + lambda ^ 2) / (Real.pi * lambda) :=
    div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (add_le_add hsquare (le_refl _)) hC.le) (by positivity)
  calc
    _ <= Real.sqrt eps * (C * (1 + lambda ^ 2) / (Real.pi * lambda)) :=
      mul_le_mul_of_nonneg_left (hNorm.trans hUpper) (Real.sqrt_nonneg _)
    _ = _ := by ring

theorem normalized_phase_error_tendsto_zero (lambda : Real) (hl : 0 < lambda) :
    Filter.Tendsto (fun eps : Real => (Real.sqrt eps : Complex) * remainder eps lambda)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  choose C hC hc using normalized_phase_error_bound
  let K := C * (1 + lambda ^ 2) / (Real.pi * lambda)
  have hPos : Filter.Eventually (fun eps : Real => 0 < eps) (nhdsWithin 0 (Set.Ioi 0)) :=
    self_mem_nhdsWithin
  have hOne : Filter.Eventually (fun eps : Real => eps < 1) (nhdsWithin 0 (Set.Ioi 0)) :=
    (eventually_lt_nhds (show (0 : Real) < 1 by norm_num)).filter_mono nhdsWithin_le_nhds
  have hBound : Filter.Eventually
      (fun eps : Real => norm ((Real.sqrt eps : Complex) * remainder eps lambda) <=
        K * Real.sqrt eps) (nhdsWithin 0 (Set.Ioi 0)) :=
    (hPos.and hOne).mono (fun eps he => by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.sqrt_nonneg _)]
      exact (hc lambda eps hl he.1 he.2.le).2)
  have hsBase : Filter.Tendsto (fun eps : Real => Real.sqrt eps)
      (nhds 0) (nhds (Real.sqrt 0)) := Real.continuous_sqrt.continuousAt
  have hs : Filter.Tendsto (fun eps : Real => Real.sqrt eps)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    simpa only [Real.sqrt_zero] using hsBase.mono_left nhdsWithin_le_nhds
  have hConst : Filter.Tendsto (fun _ : Real => K)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds K) := tendsto_const_nhds
  have hLimit : Filter.Tendsto (fun eps : Real => K * Real.sqrt eps)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    simpa only [mul_zero] using hConst.mul hs
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  exact squeeze_zero' (Filter.Eventually.of_forall (fun eps => norm_nonneg _)) hBound hLimit

theorem conductor_phase_error_bound :
    exists C : Real, 0 < C /\ forall (q : Nat) (eps : Real), 0 < q ->
      0 < eps -> eps <= 1 ->
      Real.sqrt eps * norm (remainder eps (2 / (q : Real))) <=
        (C * ((q : Real) ^ 2 + 4) / (2 * Real.pi * (q : Real))) * Real.sqrt eps := by
  choose C hC hc using normalized_phase_error_bound
  refine Exists.intro C (And.intro hC ?_)
  intro q eps hq he he1
  have hqR : 0 < (q : Real) := by exact_mod_cast hq
  have hl : 0 < 2 / (q : Real) := by positivity
  calc
    _ <= (C * (1 + (2 / (q : Real)) ^ 2) / (Real.pi * (2 / (q : Real)))) *
        Real.sqrt eps := (hc (2 / (q : Real)) eps hl he he1).2
    _ = _ := by field_simp; ring

end PrimeFactorOscillations.IntegerGaussianAbelPhase


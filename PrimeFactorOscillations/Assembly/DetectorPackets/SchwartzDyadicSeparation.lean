/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Assembly.DetectorPackets.CoprimeSchwartzUniform

/-!
# SchwartzDyadicSeparation

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

namespace PrimeFactorOscillations.SchwartzDyadicSeparation

open MeasureTheory OAI.FourierBridge

theorem local_log_separation (F : SchwartzMap Real Complex)
    (T : Real) (hT : 0 <= T) (A : Nat) :
    exists C : Real, 0 < C /\
      forall R : Real, 0 <= R -> exists g : SchwartzMap Real Complex,
      (forall y : Real, abs y <= T -> g y = F (R * Real.exp y)) /\
      (integral volume (fun t : Real => norm ((FourierTransform.fourier g) t)) <=
        C / (1 + R) ^ A) /\
      (forall y : Real, abs y <= T ->
        F (R * Real.exp y) =
          integral volume (fun t : Real =>
            Real.fourierChar (t * y) * (FourierTransform.fourier g) t)) := by
  let K : Nat := (volume : Measure Real).integrablePower
  choose V CW hVc hVs hVone hCW hVDeriv hSupport using
    exists_complex_smooth_cutoff_with_derivative_bounds T K hT
  let CF : Real := schwartzDerivativeDecayConstant F (A + K) K
  have hCF : 0 <= CF := schwartzDerivativeDecayConstant_nonneg F _ _
  have hFs : ContDiff Real ((Top.top : ENat) : WithTop ENat) (F : Real -> Complex) :=
    F.smooth (Top.top : ENat)
  let m : Real := Real.exp (-(T + 1))
  let H : Real := Real.exp (T + 1)
  have hm : 0 < m := Real.exp_pos _
  have hm1 : m <= 1 := by
    calc
      _ <= Real.exp 0 := Real.exp_le_exp.mpr (by linarith)
      _ = _ := Real.exp_zero
  have hH : 1 <= H := by
    calc
      _ = Real.exp 0 := Real.exp_zero.symm
      _ <= _ := Real.exp_le_exp.mpr (by linarith)
  let D : Real := 2 ^ (0 : Nat) *
    (coefficientMomentBound 0 (profileMomentConstant K (T + 1) H CW CF) +
      coefficientMomentBound 0 (profileMomentConstant K (T + 1) H CW CF))
  let C : Real := (abs D + 1) / m ^ (A + K)
  have hC : 0 < C := by dsimp only [C]; positivity
  refine Exists.intro C (And.intro hC ?_)
  intro R hR
  let g : SchwartzMap Real Complex := logProfile V F R 1 hVc hVs hFs
  have hpoint (y : Real) (hy : abs y <= T) : g y = F (R * Real.exp y) := by
    dsimp only [g]
    rw [logProfile_apply, hVone y hy, one_mul, one_mul]
  have hbound := coupled_log_coefficient_bound V F R m H (T + 1) CW CF A 0
    hVc hVs hFs hR hm hm1 hH (by linarith) hCW hCF
    (by simpa only [zero_add] using hVDeriv)
    (by simpa only [zero_add] using hSupport)
    (by
      intro j hj i hi u hu
      exact schwartz_derivative_decay_finite F A K j i u
        (by simpa only [zero_add] using hj) hi hu)
  have hb : m ^ (A + K) * (1 + R) ^ A *
      integral volume (fun t : Real => norm ((FourierTransform.fourier g) t)) <= D := by
    simpa only [K, g, D, zero_add, pow_zero, one_mul] using hbound
  have hmass : integral volume (fun t : Real =>
      norm ((FourierTransform.fourier g) t)) <= C / (1 + R) ^ A := by
    apply le_of_mul_le_mul_left (a := m ^ (A + K) * (1 + R) ^ A) ?_ (by positivity)
    calc
      _ <= D := hb
      _ <= abs D + 1 := by have h := le_abs_self D; linarith
      _ = _ := by dsimp only [C]; field_simp
  refine Exists.intro g (And.intro hpoint (And.intro hmass ?_))
  intro y hy
  have hFourier : Integrable (FourierTransform.fourier (g : Real -> Complex)) volume := by
    rw [<- SchwartzMap.fourier_coe]
    exact (FourierTransform.fourier g).integrable
  have hi := g.integrable.fourierInv_fourier_eq hFourier (g.continuous.continuousAt (x := y))
  rw [Real.fourierInv_eq] at hi
  have hi' : integral volume (fun t : Real =>
      Real.fourierChar (t * y) * (FourierTransform.fourier g) t) = g y := by
    simpa only [<- SchwartzMap.fourier_coe, Real.inner_apply, Circle.smul_def,
      smul_eq_mul] using hi
  exact (hpoint y hy).symm.trans hi'.symm

end PrimeFactorOscillations.SchwartzDyadicSeparation


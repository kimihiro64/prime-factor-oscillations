/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Assembly.DetectorPackets.SchwartzDyadicSeparation

/-!
# SchwartzFiniteSeparation

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

namespace PrimeFactorOscillations.SchwartzFiniteSeparation

open MeasureTheory

def phase (t x : Real) : Circle := Real.fourierChar (t * x)

theorem phase_add (t x y : Real) : phase t (x + y) = phase t x * phase t y := by
  unfold phase
  rw [mul_add, AddChar.map_add_eq_mul]

theorem phase_norm (t x : Real) : norm (phase t x : Complex) = 1 := Circle.norm_coe _

theorem phase_continuous (x : Real) :
    Continuous (fun t : Real => (phase t x : Complex)) :=
  continuous_subtype_val.comp
    (Real.continuous_fourierChar.comp (continuous_id.mul continuous_const))

theorem phase_term_integrable (c : SchwartzMap Real Complex) (x : Real) (z : Complex) :
    Integrable (fun t : Real => z * (phase t x : Complex) * c t) volume := by
  apply (c.integrable.norm.mul_const (norm z)).mono'
    (((continuous_const.mul (phase_continuous x)).mul c.continuous).aestronglyMeasurable)
  apply Filter.Eventually.of_forall
  intro t
  change norm (z * (phase t x : Complex) * c t) <= norm (c t) * norm z
  simp only [norm_mul, phase_norm, mul_one]
  exact le_of_eq (mul_comm _ _)

theorem schwartz_inverse (g : SchwartzMap Real Complex) (y : Real) :
    g y = integral volume (fun t : Real =>
      (phase t y : Complex) * (FourierTransform.fourier g) t) := by
  have hc : Integrable (FourierTransform.fourier (g : Real -> Complex)) volume := by
    rw [<- SchwartzMap.fourier_coe]
    exact (FourierTransform.fourier g).integrable
  have h := g.integrable.fourierInv_fourier_eq hc (g.continuous.continuousAt (x := y))
  rw [Real.fourierInv_eq] at h
  symm
  simpa only [phase, <- SchwartzMap.fourier_coe, Real.inner_apply,
    Circle.smul_def, smul_eq_mul] using h

theorem finite_sum_separation {I : Type} (g : SchwartzMap Real Complex)
    (S : Finset I) (z : I -> Complex) (y : I -> Real) :
    S.sum (fun i => z i * g (y i)) =
      integral volume (fun t : Real => (FourierTransform.fourier g) t *
        S.sum (fun i => z i * (phase t (y i) : Complex))) := by
  have hi (i : I) : Integrable (fun t : Real =>
      z i * (phase t (y i) : Complex) * (FourierTransform.fourier g) t) volume :=
    phase_term_integrable (FourierTransform.fourier g) (y i) (z i)
  calc
    _ = S.sum (fun i => integral volume (fun t : Real =>
        z i * (phase t (y i) : Complex) * (FourierTransform.fourier g) t)) := by
      apply Finset.sum_congr rfl
      intro i hiS
      rw [schwartz_inverse g (y i), <- integral_const_mul]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun t => by ring)
    _ = integral volume (fun t : Real => S.sum (fun i =>
        z i * (phase t (y i) : Complex) * (FourierTransform.fourier g) t)) :=
      (integral_finset_sum S (fun i hiS => hi i)).symm
    _ = _ := by
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro t
      change S.sum (fun i => z i * (phase t (y i) : Complex) *
        (FourierTransform.fourier g) t) =
        (FourierTransform.fourier g) t *
          S.sum (fun i => z i * (phase t (y i) : Complex))
      calc
        _ = S.sum (fun i => (FourierTransform.fourier g) t *
            (z i * (phase t (y i) : Complex))) := by
          apply Finset.sum_congr rfl
          intro i hiS
          ring
        _ = _ := (Finset.mul_sum _ _ _).symm

end PrimeFactorOscillations.SchwartzFiniteSeparation


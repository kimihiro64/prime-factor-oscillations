/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Assembly.DetectorPackets.SchwartzFiniteSeparation

/-!
# SchwartzFinitePacket

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

namespace PrimeFactorOscillations.SchwartzFinitePacket

open MeasureTheory SchwartzFiniteSeparation

theorem finite_phase_integrable {I : Type} (c : SchwartzMap Real Complex)
    (S : Finset I) (z : I -> Complex) (y : I -> Real) :
    Integrable (fun t : Real => c t *
      S.sum (fun i => z i * (phase t (y i) : Complex))) volume := by
  have hi := integrable_finsetSum S
    (fun i hiS => phase_term_integrable c (y i) (z i))
  have he (t : Real) :
      S.sum (fun i => z i * (phase t (y i) : Complex) * c t) =
        c t * S.sum (fun i => z i * (phase t (y i) : Complex)) := by
    calc
      _ = S.sum (fun i => c t * (z i * (phase t (y i) : Complex))) := by
        apply Finset.sum_congr rfl
        intro i hiS
        ring
      _ = _ := (Finset.mul_sum _ _ _).symm
  exact hi.congr (Filter.Eventually.of_forall he)

theorem finite_integral_l1_bound {I J : Type} (g : SchwartzMap Real Complex)
    (E : Finset I) (S : Finset J) (z : I -> J -> Complex) (y : I -> J -> Real)
    (H : Real)
    (hH : forall t : Real,
      E.sum (fun i => norm (S.sum (fun j => z i j * (phase t (y i j) : Complex)))) <= H) :
    E.sum (fun i => norm (S.sum (fun j => z i j * g (y i j)))) <=
      H * integral volume (fun t : Real => norm ((FourierTransform.fourier g) t)) := by
  let c : SchwartzMap Real Complex := FourierTransform.fourier g
  let U : I -> Real -> Complex := fun i t =>
    c t * S.sum (fun j => z i j * (phase t (y i j) : Complex))
  have hi (i : I) : Integrable (U i) volume :=
    finite_phase_integrable c S (z i) (y i)
  have heq (i : I) : S.sum (fun j => z i j * g (y i j)) =
      integral volume (U i) := finite_sum_separation g S (z i) (y i)
  have hsumInt : Integrable (fun t : Real => E.sum (fun i => norm (U i t))) volume :=
    integrable_finsetSum E (fun i hiE => (hi i).norm)
  calc
    _ <= E.sum (fun i => integral volume (fun t : Real => norm (U i t))) := by
      apply Finset.sum_le_sum
      intro i hiE
      rw [heq i]
      exact norm_integral_le_integral_norm (U i)
    _ = integral volume (fun t : Real => E.sum (fun i => norm (U i t))) :=
      (integral_finsetSum E (fun i hiE => (hi i).norm)).symm
    _ <= integral volume (fun t : Real => norm (c t) * H) := by
      apply integral_mono hsumInt (c.integrable.norm.mul_const H)
      intro t
      change E.sum (fun i => norm (c t *
        S.sum (fun j => z i j * (phase t (y i j) : Complex)))) <= norm (c t) * H
      calc
        _ = E.sum (fun i => norm (c t) *
            norm (S.sum (fun j => z i j * (phase t (y i j) : Complex)))) := by
          apply Finset.sum_congr rfl
          intro i hiE
          exact norm_mul _ _
        _ = norm (c t) * E.sum (fun i =>
            norm (S.sum (fun j => z i j * (phase t (y i j) : Complex)))) :=
          (Finset.mul_sum _ _ _).symm
        _ <= _ := mul_le_mul_of_nonneg_left (hH t) (norm_nonneg _)
    _ = _ := by rw [integral_mul_const]; ring

end PrimeFactorOscillations.SchwartzFinitePacket


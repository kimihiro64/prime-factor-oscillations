/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import Mathlib.Tactic.FieldSimp
import PrimeFactorOscillations.Assembly.DetectorPackets.CoprimeDivisorKernel

/-!
# CoprimeMobiusWave

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
# Sign of the local coprime Mobius wave factor

For z=eta(p)*p^(-rho), this is the diagonal Euler correction after
coprimality inversion. Applying it to a growing divisor cutoff still
requires the actual joint wave extraction and its signed remainder.
-/


noncomputable section
namespace PrimeFactorOscillations.CoprimeMobiusWave

def waveFactor (z : Complex) : Real :=
  1 - Complex.normSq z / Complex.normSq (1 - z)

theorem normSq_difference (z : Complex) :
    Complex.normSq (1 - z) - Complex.normSq z = 1 - 2 * z.re := by
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.one_re, Complex.one_im]
  ring

theorem waveFactor_identity (z : Complex) (h : z.re < 1 / 2) :
    waveFactor z = (1 - 2 * z.re) / Complex.normSq (1 - z) := by
  have hn : 0 <= Complex.normSq z := by
    rw [Complex.normSq_apply]
    nlinarith [sq_nonneg z.re, sq_nonneg z.im]
  have hd : 0 < Complex.normSq (1 - z) := by
    nlinarith [normSq_difference z]
  unfold waveFactor
  apply (eq_div_iff (ne_of_gt hd)).mpr
  have hc : Complex.normSq z / Complex.normSq (1 - z) *
      Complex.normSq (1 - z) = Complex.normSq z := by
    field_simp
  rw [sub_mul, one_mul, hc]
  exact normSq_difference z

theorem waveFactor_pos (z : Complex) (h : z.re < 1 / 2) :
    0 < waveFactor z := by
  have hn : 0 <= Complex.normSq z := by
    rw [Complex.normSq_apply]
    nlinarith [sq_nonneg z.re, sq_nonneg z.im]
  have hd : 0 < Complex.normSq (1 - z) := by
    nlinarith [normSq_difference z]
  rw [waveFactor_identity z h]
  exact div_pos (by linarith) hd

theorem finite_wave_product_pos (P : Finset Nat) (z : Nat -> Complex)
    (h : forall p, Membership.mem P p -> (z p).re < 1 / 2) :
    0 < P.prod (fun p => waveFactor (z p)) := by
  apply Finset.prod_pos
  intro p hp
  exact waveFactor_pos (z p) (h p hp)

end PrimeFactorOscillations.CoprimeMobiusWave


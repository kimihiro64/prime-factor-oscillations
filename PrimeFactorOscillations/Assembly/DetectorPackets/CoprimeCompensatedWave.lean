/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Assembly.DetectorPackets.CoprimeMobiusWave
import PrimeFactorOscillations.Assembly.DetectorPackets.QuadraticRetainedBeta

/-!
# CoprimeCompensatedWave

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

namespace PrimeFactorOscillations.CoprimeCompensatedWave

open QuadraticCoprimeMean

/- Compensate the coefficients before forming the energy. The two cross
terms are part of the observable and are retained exactly. -/

theorem compensated_coprime_form
    (S : Finset Nat) (a b : Nat -> Complex) (c : Complex) :
    coprimeForm S S (fun n => a n - c * b n)
        (fun n => star (a n - c * b n)) =
      coprimeForm S S a (fun n => star (a n)) -
        c * coprimeForm S S b (fun n => star (a n)) -
        star c * coprimeForm S S a (fun n => star (b n)) +
        (c * star c) * coprimeForm S S b (fun n => star (b n)) := by
  have hterm (n m : Nat) :
      (if Nat.Coprime n m then
        (a n - c * b n) * star (a m - c * b m) else 0) =
      (if Nat.Coprime n m then a n * star (a m) else 0) -
        c * (if Nat.Coprime n m then b n * star (a m) else 0) -
        star c * (if Nat.Coprime n m then a n * star (b m) else 0) +
        (c * star c) * (if Nat.Coprime n m then b n * star (b m) else 0) := by
    by_cases h : Nat.Coprime n m
    . simp only [if_pos h, star_sub, star_mul]
      ring
    . simp only [if_neg h]
      ring
  unfold coprimeForm
  simp_rw [hterm]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, <- Finset.mul_sum]

theorem signal_multiplier_lower (z : Complex) (r : Real)
    (hr : 0 <= r) (hlt : r < 1) (hz : norm z <= r) :
    (1 - r) ^ 2 <= norm (1 - z) ^ 2 := by
  have htri : (1 : Real) <= norm (1 - z) + norm z := by
    calc
      _ = norm ((1 - z) + z) := by simp
      _ <= _ := norm_add_le _ _
  have hlo : 1 - r <= norm (1 - z) := by linarith
  have hp : 0 <= 1 - r := by linarith
  simpa only [sq] using mul_self_le_mul_self hp hlo

theorem signal_multiplier_nonzero (z : Complex) (hz : norm z < 1) :
    Not (1 - z = 0) := by
  intro h
  have he : z = 1 := (sub_eq_zero.mp h).symm
  rw [he] at hz
  simpa only [norm_one, lt_self_iff_false] using hz

def selectedWaveFactor (t : Real) (z : Complex) : Real :=
  (1 - t - 2 * z.re) / Complex.normSq (1 - z)

theorem selectedWaveFactor_pos (t : Real) (z : Complex)
    (ht : t <= 1 / 5) (hz : z.re <= 1 / 3) :
    0 < selectedWaveFactor t z := by
  have hn : 0 < 1 - t - 2 * z.re := by linarith
  have hbase : 0 < 1 - 2 * z.re := by linarith
  have hs : 0 <= Complex.normSq z := by
    rw [Complex.normSq_apply]
    nlinarith [sq_nonneg z.re, sq_nonneg z.im]
  have hd : 0 < Complex.normSq (1 - z) := by
    nlinarith [CoprimeMobiusWave.normSq_difference z]
  exact div_pos hn hd

end PrimeFactorOscillations.CoprimeCompensatedWave


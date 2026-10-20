/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Proof.DetectorPackets.PeriodicCompanionGrowth

/-!
# DirichletCompanionIntegral

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
open MeasureTheory Filter Asymptotics

namespace PrimeFactorOscillations.PeriodicCompanion

def characterSequence {q : Nat} (chi : DirichletCharacter Complex q) (n : Nat) : Complex :=
  chi ((n + 1 : Nat) : ZMod q)

theorem characterSequence_periodic {q : Nat} (chi : DirichletCharacter Complex q) (n : Nat) :
    characterSequence chi (n + q) = characterSequence chi n := by
  unfold characterSequence
  simp only [Nat.cast_add, Nat.cast_one, ZMod.natCast_self, add_zero]

theorem characterSequence_norm_le {q : Nat} (chi : DirichletCharacter Complex q) (n : Nat) :
    norm (characterSequence chi n) <= 1 :=
  chi.norm_le_one _

theorem character_prefix_norm_le {q : Nat} (chi : DirichletCharacter Complex q) (N : Nat) :
    norm (blockPrefix (characterSequence chi) N) <= (N : Real) := by
  unfold blockPrefix
  calc
    _ <= (Finset.range N).sum (fun n => norm (characterSequence chi n)) := norm_sum_le _ _
    _ <= (Finset.range N).sum (fun _ => (1 : Real)) :=
      Finset.sum_le_sum (fun n _ => characterSequence_norm_le chi n)
    _ = _ := by simp

theorem character_mean_norm_le {q : Nat} (chi : DirichletCharacter Complex q) (hq : 0 < q) :
    norm (mean (characterSequence chi) q) <= 1 := by
  have hqnorm : norm (q : Complex) = (q : Real) := by
    rw [<- Complex.ofReal_natCast, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Nat.cast_nonneg q)]
  rw [mean, norm_div, hqnorm]
  calc
    _ <= (q : Real) / (q : Real) :=
      div_le_div_of_nonneg_right (character_prefix_norm_le chi q) (Nat.cast_nonneg q)
    _ = 1 := div_self (by exact_mod_cast Nat.ne_of_gt hq)

theorem character_errorMellin_norm_bound {q : Nat}
    (chi : DirichletCharacter Complex q) (hq : 0 < q) (s : Complex) (hs : 0 < s.re) :
    norm (errorMellin (characterSequence chi) q s) <= (2 * (q : Real) + 1) / s.re := by
  apply (errorMellin_norm_bound (characterSequence chi) q hq
    (characterSequence_periodic chi) (characterSequence_norm_le chi) s hs).trans
  apply div_le_div_of_nonneg_right _ hs.le
  have hm := character_mean_norm_le chi hq
  have hqreal : 0 <= (q : Real) := Nat.cast_nonneg q
  nlinarith [norm_nonneg (mean (characterSequence chi) q)]

def companionContinuation {q : Nat} (chi : DirichletCharacter Complex q) (s : Complex) : Complex :=
  mean (characterSequence chi) q * s / (s - 1) +
    s * errorMellin (characterSequence chi) q s

theorem companionContinuation_differentiableAt {q : Nat}
    (chi : DirichletCharacter Complex q) (hq : 0 < q)
    (s : Complex) (hs : 0 < s.re) (hs1 : Not (s = 1)) :
    DifferentiableAt Complex (companionContinuation chi) s := by
  exact (((differentiableAt_const (mean (characterSequence chi) q)).mul
    differentiableAt_id).div (differentiableAt_id.sub_const 1)
      (sub_ne_zero.mpr hs1)).add
    (differentiableAt_id.mul (errorMellin_differentiableAt (characterSequence chi) q hq
      (characterSequence_periodic chi) (characterSequence_norm_le chi) s hs))

theorem companionContinuation_norm_bound {q : Nat}
    (chi : DirichletCharacter Complex q) (hq : 0 < q) (s : Complex) (hs : 0 < s.re) :
    norm (companionContinuation chi s) <=
      norm s * (1 / norm (s - 1) + (2 * (q : Real) + 1) / s.re) := by
  unfold companionContinuation
  apply (norm_add_le _ _).trans
  rw [norm_div, norm_mul, norm_mul]
  calc
    _ <= 1 * norm s / norm (s - 1) +
        norm s * ((2 * (q : Real) + 1) / s.re) :=
      add_le_add
        (div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right (character_mean_norm_le chi hq) (norm_nonneg _))
          (norm_nonneg _))
        (mul_le_mul_of_nonneg_left (character_errorMellin_norm_bound chi hq s hs)
          (norm_nonneg _))
    _ = _ := by ring

end PrimeFactorOscillations.PeriodicCompanion

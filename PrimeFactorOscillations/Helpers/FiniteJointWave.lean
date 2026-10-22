/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import PrimeFactorOscillations.Helpers.DampedWaveRecurrence
import PrimeFactorOscillations.Helpers.FiniteUnitCharacterRecurrence

/-!
# Arbitrary finite joint trigonometric waves

Boundedness, uniform continuity and relatively dense simultaneous almost
periods hold without commensurability assumptions on the frequencies.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.PrimeClassDeletion

noncomputable def finiteJointWave (m : Nat) (A frequency phase : Fin m -> Real) (v : Real) : Real :=
  Finset.univ.sum (fun j => A j * Real.cos (frequency j * v + phase j))

def finiteJointAmplitude (m : Nat) (A : Fin m -> Real) : Real :=
  Finset.univ.sum (fun j => abs (A j))

theorem finiteJointAmplitude_nonneg (m : Nat) (A : Fin m -> Real) :
    0 <= finiteJointAmplitude m A :=
  Finset.sum_nonneg (fun j _ => abs_nonneg (A j))

theorem finiteJointWave_abs_le (m : Nat) (A frequency phase : Fin m -> Real) (v : Real) :
    abs (finiteJointWave m A frequency phase v) <= finiteJointAmplitude m A := by
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro j _
  rw [abs_mul]
  exact (mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (abs_nonneg _)).trans_eq
    (mul_one _)

theorem finiteJointWave_uniformContinuous (m : Nat) (A frequency phase : Fin m -> Real) :
    UniformContinuous (finiteJointWave m A frequency phase) := by
  apply Finset.uniformContinuous_sum
  intro j _
  exact (Real.lipschitzWith_cos.uniformContinuous.comp
    (Real.uniformContinuous_const_mul.add_const (phase j))).const_mul' (A j)

theorem cosine_shift_abs_le_unit_phase (a b : Real) :
    abs (Real.cos (a + b) - Real.cos a) <=
      norm (Complex.exp ((b : Complex) * Complex.I) - 1) := by
  have hunit : norm (Complex.exp ((a : Complex) * Complex.I)) = 1 := by
    rw [mul_comm]
    exact Complex.norm_exp_I_mul_ofReal a
  have hid : Complex.exp (((a + b : Real) : Complex) * Complex.I) -
        Complex.exp ((a : Complex) * Complex.I) =
      Complex.exp ((a : Complex) * Complex.I) *
        (Complex.exp ((b : Complex) * Complex.I) - 1) := by
    rw [Complex.ofReal_add, add_mul, Complex.exp_add]
    ring
  have hre : Real.cos (a + b) - Real.cos a =
      (Complex.exp (((a + b : Real) : Complex) * Complex.I) -
        Complex.exp ((a : Complex) * Complex.I)).re := by
    rw [Complex.sub_re, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_re]
  calc
    abs (Real.cos (a + b) - Real.cos a) = abs
        ((Complex.exp (((a + b : Real) : Complex) * Complex.I) -
          Complex.exp ((a : Complex) * Complex.I)).re) := congrArg abs hre
    _ <= norm (Complex.exp (((a + b : Real) : Complex) * Complex.I) -
        Complex.exp ((a : Complex) * Complex.I)) := Complex.abs_re_le_norm _
    _ = norm (Complex.exp ((b : Complex) * Complex.I) - 1) := by
      rw [hid, norm_mul, hunit, one_mul]

theorem finiteJointWave_uniformAlmostPeriodic (m : Nat)
    (A frequency phase : Fin m -> Real) :
    IsUniformAlmostPeriodicWave (finiteJointWave m A frequency phase) := by
  intro e he
  let C := finiteJointAmplitude m A
  have hC : 0 <= C := finiteJointAmplitude_nonneg m A
  let d := e / (C + 1)
  have hd : 0 < d := div_pos he (by linarith only [hC])
  let q : Fin m -> Real -> Complex :=
    fun j t => Complex.exp (((frequency j * t : Real) : Complex) * Complex.I)
  have hunit : forall j t, norm (q j t) = 1 := by
    intro j t
    dsimp [q]
    rw [mul_comm]
    exact Complex.norm_exp_I_mul_ofReal _
  have hadd : forall j s t, q j (s + t) = q j s * q j t := by
    intro j s t
    dsimp [q]
    rw [mul_add, Complex.ofReal_add, add_mul, Complex.exp_add]
  choose L hL using finite_unit_character_recurrence m q hunit hadd d hd
  refine Exists.intro L (And.intro hL.1 ?_)
  intro b
  choose t ht using hL.2 b
  refine Exists.intro t (And.intro ht.1 (And.intro ht.2.1 ?_))
  intro v
  have hterm (j : Fin m) :
      abs (A j * Real.cos (frequency j * (v + t) + phase j) -
        A j * Real.cos (frequency j * v + phase j)) <= abs (A j) * d := by
    rw [<- mul_sub, abs_mul]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    rw [show frequency j * (v + t) + phase j =
      (frequency j * v + phase j) + frequency j * t by ring]
    exact (cosine_shift_abs_le_unit_phase _ _).trans (ht.2.2 j).le
  have hsum : abs (finiteJointWave m A frequency phase (v + t) -
      finiteJointWave m A frequency phase v) <= C * d := by
    unfold finiteJointWave
    rw [<- Finset.sum_sub_distrib]
    calc
      _ <= Finset.univ.sum (fun j => abs (A j *
          Real.cos (frequency j * (v + t) + phase j) - A j *
            Real.cos (frequency j * v + phase j))) := Finset.abs_sum_le_sum_abs _ _
      _ <= Finset.univ.sum (fun j => abs (A j) * d) :=
        Finset.sum_le_sum (fun j _ => hterm j)
      _ = C * d := by rw [<- Finset.sum_mul]; rfl
  have hde : d * (C + 1) = e := by
    dsimp [d]
    field_simp
  exact hsum.trans (by nlinarith only [hde, hd])

end PrimeFactorOscillations.PrimeClassDeletion

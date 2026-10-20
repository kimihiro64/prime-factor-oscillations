/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Assembly.DetectorPackets.MobiusCompensatedCovariance

/-!
# PolarizedCoprimeProbe

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

namespace PrimeFactorOscillations.PolarizedCoprimeProbe

def mixedForm (S T : Finset Nat) (K : Nat -> Nat -> Complex)
    (a b : Nat -> Complex) : Complex :=
  S.sum (fun n => T.sum (fun m => K n m * a n * star (b m)))

def diagonalForm (S : Finset Nat) (K : Nat -> Nat -> Complex)
    (a : Nat -> Complex) : Complex :=
  mixedForm S S K a a

theorem mixed_add_left (S T : Finset Nat) (K : Nat -> Nat -> Complex)
    (a b c : Nat -> Complex) :
    mixedForm S T K (fun n => a n + b n) c =
      mixedForm S T K a c + mixedForm S T K b c := by
  simp [mixedForm, add_mul, mul_add, Finset.sum_add_distrib]

theorem mixed_sub_left (S T : Finset Nat) (K : Nat -> Nat -> Complex)
    (a b c : Nat -> Complex) :
    mixedForm S T K (fun n => a n - b n) c =
      mixedForm S T K a c - mixedForm S T K b c := by
  simp [mixedForm, sub_mul, mul_sub, Finset.sum_sub_distrib]

theorem mixed_add_right (S T : Finset Nat) (K : Nat -> Nat -> Complex)
    (a b c : Nat -> Complex) :
    mixedForm S T K a (fun n => b n + c n) =
      mixedForm S T K a b + mixedForm S T K a c := by
  simp [mixedForm, star_add, mul_add, Finset.sum_add_distrib]

theorem mixed_sub_right (S T : Finset Nat) (K : Nat -> Nat -> Complex)
    (a b c : Nat -> Complex) :
    mixedForm S T K a (fun n => b n - c n) =
      mixedForm S T K a b - mixedForm S T K a c := by
  simp [mixedForm, star_sub, mul_sub, Finset.sum_sub_distrib]

theorem mixed_scale_left (S T : Finset Nat) (K : Nat -> Nat -> Complex)
    (a b : Nat -> Complex) (c : Complex) :
    mixedForm S T K (fun n => c * a n) b = c * mixedForm S T K a b := by
  unfold mixedForm
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  ring

theorem mixed_scale_right (S T : Finset Nat) (K : Nat -> Nat -> Complex)
    (a b : Nat -> Complex) (c : Complex) :
    mixedForm S T K a (fun n => c * b n) =
      star c * mixedForm S T K a b := by
  unfold mixedForm
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  simp only [star_mul]
  ring

theorem four_phase_recovery (S : Finset Nat) (K : Nat -> Nat -> Complex)
    (a b : Nat -> Complex) :
    diagonalForm S K (fun n => a n + b n) -
        diagonalForm S K (fun n => a n - b n) +
      Complex.I * (diagonalForm S K (fun n => a n + Complex.I * b n) -
        diagonalForm S K (fun n => a n - Complex.I * b n)) =
      4 * mixedForm S S K a b := by
  have hI : star Complex.I = -Complex.I := by simp
  simp only [diagonalForm, mixed_add_left, mixed_sub_left, mixed_add_right,
    mixed_sub_right, mixed_scale_left, mixed_scale_right, hI]
  ring_nf <;> simp [Complex.I_sq] <;> ring

theorem coprime_mixed_eq (S : Finset Nat) (a b : Nat -> Complex) :
    QuadraticCoprimeMean.coprimeForm S S a (fun n => star (b n)) =
      mixedForm S S (fun n m => if Nat.Coprime n m then 1 else 0) a b := by
  unfold QuadraticCoprimeMean.coprimeForm mixedForm
  apply Finset.sum_congr rfl
  intro n hn
  apply Finset.sum_congr rfl
  intro m hm
  by_cases h : Nat.Coprime n m <;> simp [h]

end PrimeFactorOscillations.PolarizedCoprimeProbe

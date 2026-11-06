/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Tactic.FinCases
import PrimeFactorOscillations.Assembly.CarmichaelMultiplicitySupportBound

/-!
# An exact five-point multiplicity-support extremizer

The center has multiplicity two. Its two reference points and their
reflections have multiplicity one. The closed strip endpoints are retained.
No claim is made that this finite model is a zeta-zero configuration.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations.CarmichaelDyadicSharpness

open DirichletCompensatedProbe CarmichaelWeightedSignal CarmichaelTraceSharpness

def fivePoint (H : Real) (i : Fin 5) : Complex :=
  match i.val with
  | 0 => Complex.mk (1 / 2) H
  | 1 => Complex.mk (1 / 4) (H / 2)
  | 2 => Complex.mk (3 / 4) (H / 2)
  | 3 => Complex.mk (1 / 8) (H / 4)
  | _ => Complex.mk (7 / 8) (H / 4)

def fiveMultiplicity (i : Fin 5) : Nat :=
  if i = 0 then 2 else 1

def fiveMirror (i : Fin 5) : Fin 5 :=
  match i.val with
  | 0 => 0
  | 1 => 2
  | 2 => 1
  | 3 => 4
  | _ => 3

theorem fivePoint_injective (H : Real) : Function.Injective (fivePoint H) := by
  intro i j h
  have he := congrArg Complex.re h
  fin_cases i <;> fin_cases j <;> norm_num [fivePoint] at he
  all_goals rfl

def fiveSpectrum (H : Real) (hH : 0 < H) : ReflectedSpectrum (Fin 5) (7 / 8) where
  point := fivePoint H
  mult := fiveMultiplicity
  point_injective := fivePoint_injective H
  mult_pos := by
    intro i
    unfold fiveMultiplicity
    split_ifs <;> norm_num
  im_pos := by
    intro i
    fin_cases i
    . exact hH
    . exact div_pos hH (by norm_num)
    . exact div_pos hH (by norm_num)
    . exact div_pos hH (by norm_num)
    . exact div_pos hH (by norm_num)
  re_lower := by
    intro i
    fin_cases i <;> norm_num [fivePoint]
  re_upper := by
    intro i
    fin_cases i <;> norm_num [fivePoint]
  mirror := fiveMirror
  mirror_involutive := by
    intro i
    fin_cases i <;> rfl
  point_mirror := by
    intro i
    apply Complex.ext
    . rw [zeroReflection_re]
      fin_cases i <;> norm_num [fivePoint, fiveMirror]
    . rw [zeroReflection_im]
      fin_cases i <;> rfl
  mult_mirror := by
    intro i
    fin_cases i <;> norm_num [fiveMultiplicity, fiveMirror]

theorem fivePoint_power_re (H d : Real) (hd : 0 < d) (i : Fin 5) :
    (powerMap d (fivePoint H i)).re = ((fivePoint H i).re + d - 1) / d :=
  (eq_div_iff hd.ne').mpr (powerMap_real_identity d hd (fivePoint H i))

theorem fivePoint_power_im (H d : Real) (hd : 0 < d) (i : Fin 5) :
    (powerMap d (fivePoint H i)).im = (fivePoint H i).im / d :=
  (eq_div_iff hd.ne').mpr (powerMap_im_identity d hd (fivePoint H i))

theorem fivePoint_two_center (H : Real) :
    powerMap 2 (fivePoint H 0) = fivePoint H 2 := by
  apply Complex.ext
  . rw [fivePoint_power_re H 2 (by norm_num)]
    norm_num [fivePoint]
  . rw [fivePoint_power_im H 2 (by norm_num)]
    norm_num [fivePoint]

theorem fivePoint_four_center (H : Real) :
    powerMap 4 (fivePoint H 0) = fivePoint H 4 := by
  apply Complex.ext
  . rw [fivePoint_power_re H 4 (by norm_num)]
    norm_num [fivePoint]
  . rw [fivePoint_power_im H 4 (by norm_num)]
    norm_num [fivePoint]

theorem fivePoint_two_right (H : Real) :
    powerMap 2 (fivePoint H 2) = fivePoint H 4 := by
  apply Complex.ext
  . rw [fivePoint_power_re H 2 (by norm_num)]
    norm_num [fivePoint]
  . rw [fivePoint_power_im H 2 (by norm_num)]
    norm_num [fivePoint]
    ring

end PrimeFactorOscillations.CarmichaelDyadicSharpness

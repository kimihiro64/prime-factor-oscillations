/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Tactic.FinCases
import PrimeFactorOscillations.Assembly.CarmichaelFifthSupport

/-!
# The full seventeen-point fifth-multiplicity extremizer

Integer real-coordinate and height tables certify all reference ownership.
The center has order five; its left descendants have orders three,two,two.
No assertion identifies this finite model with actual zeta zeros.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000

noncomputable section

namespace PrimeFactorOscillations.CarmichaelDyadicSharpness

open DirichletCompensatedProbe CarmichaelWeightedSignal CarmichaelTraceSharpness

def seventeenRealCode (i : Fin 17) : Nat :=
  match i.val with
  | 0 => 32 | 1 => 16 | 2 => 48 | 3 => 8 | 4 => 56 | 5 => 24
  | 6 => 40 | 7 => 12 | 8 => 52 | 9 => 28 | 10 => 36 | 11 => 14
  | 12 => 50 | 13 => 20 | 14 => 44 | 15 => 10 | _ => 54

def seventeenHeightDenominator (i : Fin 17) : Nat :=
  match i.val with
  | 0 => 1 | 1 => 2 | 2 => 2 | 3 => 4 | 4 => 4 | 5 => 4 | 6 => 4
  | 7 => 8 | 8 => 8 | 9 => 8 | 10 => 8 | 11 => 16 | 12 => 16
  | 13 => 8 | 14 => 8 | 15 => 16 | _ => 16

def seventeenMultiplicity (i : Fin 17) : Nat :=
  match i.val with
  | 0 => 5 | 1 => 3 | 2 => 3 | 3 => 2 | 4 => 2 | 5 => 2 | 6 => 2
  | _ => 1

def seventeenMirror (i : Fin 17) : Fin 17 :=
  match i.val with
  | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5
  | 7 => 8 | 8 => 7 | 9 => 10 | 10 => 9 | 11 => 12 | 12 => 11
  | 13 => 14 | 14 => 13 | 15 => 16 | _ => 15

def seventeenTwoTarget (i : Fin 17) : Option (Fin 17) :=
  match i.val with
  | 0 => some 2 | 1 => some 6 | 2 => some 4 | 3 => some 10
  | 5 => some 14 | 6 => some 8 | 10 => some 12 | 14 => some 16
  | _ => none

def seventeenFourTarget (i : Fin 17) : Option (Fin 17) :=
  match i.val with
  | 0 => some 4 | 1 => some 8 | 3 => some 12 | 5 => some 16
  | _ => none

theorem seventeenHeightDenominator_pos (i : Fin 17) :
    0 < seventeenHeightDenominator i := by
  fin_cases i <;> decide

theorem seventeenTwoTarget_iff (i j : Fin 17) :
    seventeenTwoTarget i = some j <->
      2 * seventeenRealCode j = seventeenRealCode i + 64 := by
  fin_cases i <;> fin_cases j <;> decide

theorem seventeenFourTarget_iff (i j : Fin 17) :
    seventeenFourTarget i = some j <->
      4 * seventeenRealCode j = seventeenRealCode i + 192 := by
  fin_cases i <;> fin_cases j <;> decide

theorem seventeenTwoTarget_height (i j : Fin 17) (h : seventeenTwoTarget i = some j) :
    seventeenHeightDenominator j = 2 * seventeenHeightDenominator i := by
  fin_cases i <;> fin_cases j <;> norm_num [seventeenTwoTarget] at h
  all_goals decide

theorem seventeenFourTarget_height (i j : Fin 17) (h : seventeenFourTarget i = some j) :
    seventeenHeightDenominator j = 4 * seventeenHeightDenominator i := by
  fin_cases i <;> fin_cases j <;> norm_num [seventeenFourTarget] at h
  all_goals decide

def seventeenPoint (H : Real) (i : Fin 17) : Complex :=
  Complex.mk ((seventeenRealCode i : Real) / 64)
    (H / (seventeenHeightDenominator i : Real))

theorem seventeenPoint_injective (H : Real) : Function.Injective (seventeenPoint H) := by
  intro i j h
  have he := congrArg Complex.re h
  fin_cases i <;> fin_cases j <;> norm_num [seventeenPoint, seventeenRealCode] at he
  all_goals rfl

def seventeenSpectrum (H : Real) (hH : 0 < H) : ReflectedSpectrum (Fin 17) (7 / 8) where
  point := seventeenPoint H
  mult := seventeenMultiplicity
  point_injective := seventeenPoint_injective H
  mult_pos := by
    intro i
    fin_cases i <;> decide
  im_pos := by
    intro i
    apply div_pos hH
    exact_mod_cast seventeenHeightDenominator_pos i
  re_lower := by
    intro i
    fin_cases i <;> norm_num [seventeenPoint, seventeenRealCode]
  re_upper := by
    intro i
    fin_cases i <;> norm_num [seventeenPoint, seventeenRealCode]
  mirror := seventeenMirror
  mirror_involutive := by
    intro i
    fin_cases i <;> rfl
  point_mirror := by
    intro i
    apply Complex.ext
    . rw [zeroReflection_re]
      fin_cases i <;> norm_num [seventeenPoint, seventeenRealCode, seventeenMirror]
    . rw [zeroReflection_im]
      fin_cases i <;> rfl
  mult_mirror := by
    intro i
    fin_cases i <;> rfl

theorem seventeenPoint_power_re (H d : Real) (hd : 0 < d) (i : Fin 17) :
    (powerMap d (seventeenPoint H i)).re =
      ((seventeenPoint H i).re + d - 1) / d :=
  (eq_div_iff hd.ne').mpr (powerMap_real_identity d hd (seventeenPoint H i))

theorem seventeenPoint_power_im (H d : Real) (hd : 0 < d) (i : Fin 17) :
    (powerMap d (seventeenPoint H i)).im = (seventeenPoint H i).im / d :=
  (eq_div_iff hd.ne').mpr (powerMap_im_identity d hd (seventeenPoint H i))

end PrimeFactorOscillations.CarmichaelDyadicSharpness

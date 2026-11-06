/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Tactic.FinCases
import PrimeFactorOscillations.Assembly.CarmichaelTwoTailBound

/-!
# Two exact spatial multiplicity-tail extremizers

The nine-point and thirteen-point models certify the two additional facets.
All coordinates and every reference target are finite integer tables.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000

noncomputable section

namespace PrimeFactorOscillations.CarmichaelDyadicSharpness

open DirichletCompensatedProbe CarmichaelWeightedSignal CarmichaelTraceSharpness

def tailNineRealCode (i : Fin 9) : Nat :=
  match i.val with
  | 0 => 32
  | 1 => 16
  | 2 => 48
  | 3 => 8
  | 4 => 56
  | 5 => 28
  | 6 => 36
  | 7 => 14
  | _ => 50

def tailNineHeightDenominator (i : Fin 9) : Nat :=
  match i.val with
  | 0 => 1
  | 1 => 2
  | 2 => 2
  | 3 => 4
  | 4 => 4
  | 5 => 8
  | 6 => 8
  | 7 => 16
  | _ => 16

def tailNineMultiplicity (i : Fin 9) : Nat :=
  match i.val with
  | 0 => 5
  | 1 => 3
  | 2 => 3
  | 3 => 2
  | 4 => 2
  | 5 => 1
  | 6 => 1
  | 7 => 1
  | _ => 1

def tailNineMirror (i : Fin 9) : Fin 9 :=
  match i.val with
  | 0 => 0
  | 1 => 2
  | 2 => 1
  | 3 => 4
  | 4 => 3
  | 5 => 6
  | 6 => 5
  | 7 => 8
  | _ => 7

def tailNineTwoTarget (i : Fin 9) : Option (Fin 9) :=
  match i.val with
  | 0 => some 2
  | 1 => none
  | 2 => some 4
  | 3 => some 6
  | 4 => none
  | 5 => none
  | 6 => some 8
  | 7 => none
  | _ => none

def tailNineFourTarget (i : Fin 9) : Option (Fin 9) :=
  match i.val with
  | 0 => some 4
  | 1 => none
  | 2 => none
  | 3 => some 8
  | 4 => none
  | 5 => none
  | 6 => none
  | 7 => none
  | _ => none

theorem tailNineHeightDenominator_pos (i : Fin 9) :
    0 < tailNineHeightDenominator i := by
  fin_cases i <;> decide

theorem tailNineTwoTarget_iff (i j : Fin 9) :
    tailNineTwoTarget i = some j <->
      2 * tailNineRealCode j = tailNineRealCode i + 64 := by
  fin_cases i <;> fin_cases j <;> decide

theorem tailNineFourTarget_iff (i j : Fin 9) :
    tailNineFourTarget i = some j <->
      4 * tailNineRealCode j = tailNineRealCode i + 192 := by
  fin_cases i <;> fin_cases j <;> decide

theorem tailNineTwoTarget_height (i j : Fin 9) (h : tailNineTwoTarget i = some j) :
    tailNineHeightDenominator j = 2 * tailNineHeightDenominator i := by
  fin_cases i <;> fin_cases j <;> norm_num [tailNineTwoTarget] at h
  all_goals decide

theorem tailNineFourTarget_height (i j : Fin 9) (h : tailNineFourTarget i = some j) :
    tailNineHeightDenominator j = 4 * tailNineHeightDenominator i := by
  fin_cases i <;> fin_cases j <;> norm_num [tailNineFourTarget] at h
  all_goals decide

def tailNinePoint (H : Real) (i : Fin 9) : Complex :=
  Complex.mk ((tailNineRealCode i : Real) / 64)
    (H / (tailNineHeightDenominator i : Real))

theorem tailNinePoint_injective (H : Real) : Function.Injective (tailNinePoint H) := by
  intro i j h
  have he := congrArg Complex.re h
  fin_cases i <;> fin_cases j <;> norm_num [tailNinePoint, tailNineRealCode] at he
  all_goals rfl

def tailNineSpectrum (H : Real) (hH : 0 < H) : ReflectedSpectrum (Fin 9) (7 / 8) where
  point := tailNinePoint H
  mult := tailNineMultiplicity
  point_injective := tailNinePoint_injective H
  mult_pos := by
    intro i
    fin_cases i <;> decide
  im_pos := by
    intro i
    apply div_pos hH
    exact_mod_cast tailNineHeightDenominator_pos i
  re_lower := by
    intro i
    fin_cases i <;> norm_num [tailNinePoint, tailNineRealCode]
  re_upper := by
    intro i
    fin_cases i <;> norm_num [tailNinePoint, tailNineRealCode]
  mirror := tailNineMirror
  mirror_involutive := by
    intro i
    fin_cases i <;> rfl
  point_mirror := by
    intro i
    apply Complex.ext
    . rw [zeroReflection_re]
      fin_cases i <;> norm_num [tailNinePoint, tailNineRealCode, tailNineMirror]
    . rw [zeroReflection_im]
      fin_cases i <;> rfl
  mult_mirror := by
    intro i
    fin_cases i <;> rfl

theorem tailNinePoint_power_re (H d : Real) (hd : 0 < d) (i : Fin 9) :
    (powerMap d (tailNinePoint H i)).re =
      ((tailNinePoint H i).re + d - 1) / d :=
  (eq_div_iff hd.ne').mpr (powerMap_real_identity d hd (tailNinePoint H i))

theorem tailNinePoint_power_im (H d : Real) (hd : 0 < d) (i : Fin 9) :
    (powerMap d (tailNinePoint H i)).im = (tailNinePoint H i).im / d :=
  (eq_div_iff hd.ne').mpr (powerMap_im_identity d hd (tailNinePoint H i))

def tailThirteenRealCode (i : Fin 13) : Nat :=
  match i.val with
  | 0 => 32
  | 1 => 16
  | 2 => 48
  | 3 => 8
  | 4 => 56
  | 5 => 24
  | 6 => 40
  | 7 => 12
  | 8 => 52
  | 9 => 20
  | 10 => 44
  | 11 => 10
  | _ => 54

def tailThirteenHeightDenominator (i : Fin 13) : Nat :=
  match i.val with
  | 0 => 1
  | 1 => 2
  | 2 => 2
  | 3 => 4
  | 4 => 4
  | 5 => 4
  | 6 => 4
  | 7 => 8
  | 8 => 8
  | 9 => 8
  | 10 => 8
  | 11 => 16
  | _ => 16

def tailThirteenMultiplicity (i : Fin 13) : Nat :=
  match i.val with
  | 0 => 2
  | 1 => 3
  | 2 => 3
  | 3 => 1
  | 4 => 1
  | 5 => 2
  | 6 => 2
  | 7 => 1
  | 8 => 1
  | 9 => 1
  | 10 => 1
  | 11 => 1
  | _ => 1

def tailThirteenMirror (i : Fin 13) : Fin 13 :=
  match i.val with
  | 0 => 0
  | 1 => 2
  | 2 => 1
  | 3 => 4
  | 4 => 3
  | 5 => 6
  | 6 => 5
  | 7 => 8
  | 8 => 7
  | 9 => 10
  | 10 => 9
  | 11 => 12
  | _ => 11

def tailThirteenTwoTarget (i : Fin 13) : Option (Fin 13) :=
  match i.val with
  | 0 => some 2
  | 1 => some 6
  | 2 => some 4
  | 3 => none
  | 4 => none
  | 5 => some 10
  | 6 => some 8
  | 7 => none
  | 8 => none
  | 9 => none
  | 10 => some 12
  | 11 => none
  | _ => none

def tailThirteenFourTarget (i : Fin 13) : Option (Fin 13) :=
  match i.val with
  | 0 => some 4
  | 1 => some 8
  | 2 => none
  | 3 => none
  | 4 => none
  | 5 => some 12
  | 6 => none
  | 7 => none
  | 8 => none
  | 9 => none
  | 10 => none
  | 11 => none
  | _ => none

theorem tailThirteenHeightDenominator_pos (i : Fin 13) :
    0 < tailThirteenHeightDenominator i := by
  fin_cases i <;> decide

theorem tailThirteenTwoTarget_iff (i j : Fin 13) :
    tailThirteenTwoTarget i = some j <->
      2 * tailThirteenRealCode j = tailThirteenRealCode i + 64 := by
  fin_cases i <;> fin_cases j <;> decide

theorem tailThirteenFourTarget_iff (i j : Fin 13) :
    tailThirteenFourTarget i = some j <->
      4 * tailThirteenRealCode j = tailThirteenRealCode i + 192 := by
  fin_cases i <;> fin_cases j <;> decide

theorem tailThirteenTwoTarget_height (i j : Fin 13) (h : tailThirteenTwoTarget i = some j) :
    tailThirteenHeightDenominator j = 2 * tailThirteenHeightDenominator i := by
  fin_cases i <;> fin_cases j <;> norm_num [tailThirteenTwoTarget] at h
  all_goals decide

theorem tailThirteenFourTarget_height (i j : Fin 13) (h : tailThirteenFourTarget i = some j) :
    tailThirteenHeightDenominator j = 4 * tailThirteenHeightDenominator i := by
  fin_cases i <;> fin_cases j <;> norm_num [tailThirteenFourTarget] at h
  all_goals decide

def tailThirteenPoint (H : Real) (i : Fin 13) : Complex :=
  Complex.mk ((tailThirteenRealCode i : Real) / 64)
    (H / (tailThirteenHeightDenominator i : Real))

theorem tailThirteenPoint_injective (H : Real) : Function.Injective (tailThirteenPoint H) := by
  intro i j h
  have he := congrArg Complex.re h
  fin_cases i <;> fin_cases j <;> norm_num [tailThirteenPoint, tailThirteenRealCode] at he
  all_goals rfl

def tailThirteenSpectrum (H : Real) (hH : 0 < H) : ReflectedSpectrum (Fin 13) (7 / 8) where
  point := tailThirteenPoint H
  mult := tailThirteenMultiplicity
  point_injective := tailThirteenPoint_injective H
  mult_pos := by
    intro i
    fin_cases i <;> decide
  im_pos := by
    intro i
    apply div_pos hH
    exact_mod_cast tailThirteenHeightDenominator_pos i
  re_lower := by
    intro i
    fin_cases i <;> norm_num [tailThirteenPoint, tailThirteenRealCode]
  re_upper := by
    intro i
    fin_cases i <;> norm_num [tailThirteenPoint, tailThirteenRealCode]
  mirror := tailThirteenMirror
  mirror_involutive := by
    intro i
    fin_cases i <;> rfl
  point_mirror := by
    intro i
    apply Complex.ext
    . rw [zeroReflection_re]
      fin_cases i <;> norm_num [tailThirteenPoint, tailThirteenRealCode, tailThirteenMirror]
    . rw [zeroReflection_im]
      fin_cases i <;> rfl
  mult_mirror := by
    intro i
    fin_cases i <;> rfl

theorem tailThirteenPoint_power_re (H d : Real) (hd : 0 < d) (i : Fin 13) :
    (powerMap d (tailThirteenPoint H i)).re =
      ((tailThirteenPoint H i).re + d - 1) / d :=
  (eq_div_iff hd.ne').mpr (powerMap_real_identity d hd (tailThirteenPoint H i))

theorem tailThirteenPoint_power_im (H d : Real) (hd : 0 < d) (i : Fin 13) :
    (powerMap d (tailThirteenPoint H i)).im = (tailThirteenPoint H i).im / d :=
  (eq_div_iff hd.ne').mpr (powerMap_im_identity d hd (tailThirteenPoint H i))

end PrimeFactorOscillations.CarmichaelDyadicSharpness

/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Tactic.FinCases
import PrimeFactorOscillations.Assembly.CarmichaelNinthSupport

/-!
# The twenty-nine-point ninth-tail extremizer

Every real coordinate, height and affine reference is certified over Fin 29.
The central order is nine; the seven common-weak orders are nine, five,
three, three, two, two, two.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000

noncomputable section

namespace PrimeFactorOscillations.CarmichaelDyadicSharpness

open DirichletCompensatedProbe CarmichaelWeightedSignal CarmichaelTraceSharpness

def ninthRealCode (i : Fin 29) : Nat :=
  match i.val with
  | 0 => 64 | 1 => 32 | 2 => 96 | 3 => 16
  | 4 => 112 | 5 => 48 | 6 => 80 | 7 => 24
  | 8 => 104 | 9 => 56 | 10 => 72 | 11 => 28
  | 12 => 100 | 13 => 40 | 14 => 88 | 15 => 20
  | 16 => 108 | 17 => 52 | 18 => 76 | 19 => 26
  | 20 => 102 | 21 => 36 | 22 => 92 | 23 => 18
  | 24 => 110 | 25 => 44 | 26 => 84 | 27 => 22
  | _ => 106

def ninthHeightDenominator (i : Fin 29) : Nat :=
  match i.val with
  | 0 => 1 | 1 => 2 | 2 => 2 | 3 => 4
  | 4 => 4 | 5 => 4 | 6 => 4 | 7 => 8
  | 8 => 8 | 9 => 8 | 10 => 8 | 11 => 16
  | 12 => 16 | 13 => 8 | 14 => 8 | 15 => 16
  | 16 => 16 | 17 => 16 | 18 => 16 | 19 => 32
  | 20 => 32 | 21 => 16 | 22 => 16 | 23 => 32
  | 24 => 32 | 25 => 16 | 26 => 16 | 27 => 32
  | _ => 32

def ninthMultiplicity (i : Fin 29) : Nat :=
  match i.val with
  | 0 => 9 | 1 => 5 | 2 => 5 | 3 => 3
  | 4 => 3 | 5 => 3 | 6 => 3 | 7 => 2
  | 8 => 2 | 9 => 2 | 10 => 2 | 11 => 1
  | 12 => 1 | 13 => 2 | 14 => 2 | 15 => 1
  | 16 => 1 | 17 => 1 | 18 => 1 | 19 => 1
  | 20 => 1 | 21 => 1 | 22 => 1 | 23 => 1
  | 24 => 1 | 25 => 1 | 26 => 1 | 27 => 1
  | _ => 1

def ninthMirror (i : Fin 29) : Fin 29 :=
  match i.val with
  | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4
  | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 8
  | 8 => 7 | 9 => 10 | 10 => 9 | 11 => 12
  | 12 => 11 | 13 => 14 | 14 => 13 | 15 => 16
  | 16 => 15 | 17 => 18 | 18 => 17 | 19 => 20
  | 20 => 19 | 21 => 22 | 22 => 21 | 23 => 24
  | 24 => 23 | 25 => 26 | 26 => 25 | 27 => 28
  | _ => 27

def ninthTwoTarget (i : Fin 29) : Option (Fin 29) :=
  match i.val with
  | 0 => some 2 | 1 => some 6 | 2 => some 4
  | 3 => some 10 | 5 => some 14 | 6 => some 8
  | 7 => some 18 | 9 => some 22 | 10 => some 12
  | 13 => some 26 | 14 => some 16 | 18 => some 20
  | 22 => some 24 | 26 => some 28 | _ => none

def ninthFourTarget (i : Fin 29) : Option (Fin 29) :=
  match i.val with
  | 0 => some 4 | 1 => some 8 | 3 => some 12
  | 5 => some 16 | 7 => some 20 | 9 => some 24
  | 13 => some 28 | _ => none


theorem ninthHeightDenominator_pos (i : Fin 29) :
    0 < ninthHeightDenominator i := by
  fin_cases i <;> decide

theorem ninthTwoTarget_iff (i j : Fin 29) :
    ninthTwoTarget i = some j <->
      2 * ninthRealCode j = ninthRealCode i + 128 := by
  fin_cases i <;> fin_cases j <;> decide

theorem ninthFourTarget_iff (i j : Fin 29) :
    ninthFourTarget i = some j <->
      4 * ninthRealCode j = ninthRealCode i + 384 := by
  fin_cases i <;> fin_cases j <;> decide

theorem ninthTwoTarget_height (i j : Fin 29) (h : ninthTwoTarget i = some j) :
    ninthHeightDenominator j = 2 * ninthHeightDenominator i := by
  fin_cases i <;> fin_cases j <;> norm_num [ninthTwoTarget] at h
  all_goals decide

theorem ninthFourTarget_height (i j : Fin 29) (h : ninthFourTarget i = some j) :
    ninthHeightDenominator j = 4 * ninthHeightDenominator i := by
  fin_cases i <;> fin_cases j <;> norm_num [ninthFourTarget] at h
  all_goals decide

def ninthPoint (H : Real) (i : Fin 29) : Complex :=
  Complex.mk ((ninthRealCode i : Real) / 128)
    (H / (ninthHeightDenominator i : Real))

theorem ninthPoint_injective (H : Real) : Function.Injective (ninthPoint H) := by
  intro i j h
  have he := congrArg Complex.re h
  fin_cases i <;> fin_cases j <;> norm_num [ninthPoint, ninthRealCode] at he
  all_goals rfl

def ninthSpectrum (H : Real) (hH : 0 < H) : ReflectedSpectrum (Fin 29) (7 / 8) where
  point := ninthPoint H
  mult := ninthMultiplicity
  point_injective := ninthPoint_injective H
  mult_pos := by
    intro i
    fin_cases i <;> decide
  im_pos := by
    intro i
    apply div_pos hH
    exact_mod_cast ninthHeightDenominator_pos i
  re_lower := by
    intro i
    fin_cases i <;> norm_num [ninthPoint, ninthRealCode]
  re_upper := by
    intro i
    fin_cases i <;> norm_num [ninthPoint, ninthRealCode]
  mirror := ninthMirror
  mirror_involutive := by
    intro i
    fin_cases i <;> rfl
  point_mirror := by
    intro i
    apply Complex.ext
    . rw [zeroReflection_re]
      fin_cases i <;> norm_num [ninthPoint, ninthRealCode, ninthMirror]
    . rw [zeroReflection_im]
      fin_cases i <;> rfl
  mult_mirror := by
    intro i
    fin_cases i <;> rfl

theorem ninthPoint_power_re (H d : Real) (hd : 0 < d) (i : Fin 29) :
    (powerMap d (ninthPoint H i)).re =
      ((ninthPoint H i).re + d - 1) / d :=
  (eq_div_iff hd.ne').mpr (powerMap_real_identity d hd (ninthPoint H i))

theorem ninthPoint_power_im (H d : Real) (hd : 0 < d) (i : Fin 29) :
    (powerMap d (ninthPoint H i)).im = (ninthPoint H i).im / d :=
  (eq_div_iff hd.ne').mpr (powerMap_im_identity d hd (ninthPoint H i))

end PrimeFactorOscillations.CarmichaelDyadicSharpness


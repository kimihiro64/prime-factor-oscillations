/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Assembly.DetectorPackets.IntegerQuadraticCorrelationPoisson

/-!
# IntegerQuadraticStandardCRT

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

/-! Exact CRT product and conjugation laws for the raw standard Gauss sum. -/


noncomputable section
namespace PrimeFactorOscillations.IntegerQuadraticStandardCRT

open IntegerQuadraticCharacter IntegerQuadraticGauss IntegerQuadraticCRT
open IntegerQuadraticSquarefree IntegerQuadraticInitial

variable {m n : Nat} [NeZero m] [NeZero n]

theorem std_scale (m n : Nat) [NeZero m] [NeZero n] (u : Int) :
    ZMod.stdAddChar (((n : Int) * u : Int) : ZMod (m * n)) =
      ZMod.stdAddChar (u : ZMod m) := by
  have hm0 : Not ((m : Complex) = 0) := by exact_mod_cast NeZero.ne m
  have hn0 : Not ((n : Complex) = 0) := by exact_mod_cast NeZero.ne n
  rw [ZMod.stdAddChar_coe, ZMod.stdAddChar_coe]
  congr 1
  push_cast
  field_simp

theorem left_std_shift (h : Nat.Coprime m n) :
    (leftChar h ZMod.stdAddChar).mulShift (n : ZMod m) =
      (ZMod.stdAddChar : AddChar (ZMod m) Complex) := by
  apply AddChar.ext
  intro x
  choose u hu using ZMod.natCast_zmod_surjective x
  rw [<- hu]
  let e := ZMod.chineseRemainder h
  change ZMod.stdAddChar (e.symm ((n : ZMod m) * (u : ZMod m), 0)) =
    ZMod.stdAddChar (u : ZMod m)
  have heq : e.symm ((n : ZMod m) * (u : ZMod m), 0) =
      ((n * u : Nat) : ZMod (m * n)) := by
    apply e.injective
    rw [e.apply_symm_apply, map_natCast e]
    ext <;> simp
  rw [heq]
  simpa only [Int.cast_mul, Int.cast_natCast, Nat.cast_mul] using std_scale m n (u : Int)

theorem right_std_shift (h : Nat.Coprime m n) :
    (rightChar h ZMod.stdAddChar).mulShift (m : ZMod n) =
      (ZMod.stdAddChar : AddChar (ZMod n) Complex) := by
  apply AddChar.ext
  intro x
  choose u hu using ZMod.natCast_zmod_surjective x
  rw [<- hu]
  let e := ZMod.chineseRemainder h
  change ZMod.stdAddChar (e.symm (0, (m : ZMod n) * (u : ZMod n))) =
    ZMod.stdAddChar (u : ZMod n)
  have heq : e.symm (0, (m : ZMod n) * (u : ZMod n)) =
      ((m * u : Nat) : ZMod (m * n)) := by
    apply e.injective
    rw [e.apply_symm_apply, map_natCast e]
    ext <;> simp
  rw [heq]
  have hm0 : Not ((m : Complex) = 0) := by exact_mod_cast NeZero.ne m
  have hn0 : Not ((n : Complex) = 0) := by exact_mod_cast NeZero.ne n
  calc
    _ = ZMod.stdAddChar (((m : Int) * (u : Int) : Int) : ZMod (m * n)) := by
      simp only [Int.cast_mul, Int.cast_natCast, Nat.cast_mul]
    _ = ZMod.stdAddChar ((u : Int) : ZMod n) := by
      rw [ZMod.stdAddChar_coe, ZMod.stdAddChar_coe]
      congr 1
      push_cast
      field_simp
    _ = ZMod.stdAddChar (u : ZMod n) := by rw [Int.cast_natCast]

theorem left_gauss_std (hm : Good m) (h : Nat.Coprime m n) :
    gaussSum (character m hm.1) (leftChar h ZMod.stdAddChar) =
      character m hm.1 (n : ZMod m) * gaussSum (character m hm.1) ZMod.stdAddChar := by
  have hs := squarefree_fourier_factor m hm.1 hm.2.1 hm.2.2
    (leftChar h ZMod.stdAddChar) (n : ZMod m)
  rw [left_std_shift h] at hs
  have hu := character_unit_square m hm.1 n h.symm
  calc
    _ = character m hm.1 (n : ZMod m) ^ 2 *
        gaussSum (character m hm.1) (leftChar h ZMod.stdAddChar) := by
      rw [hu, one_mul]
    _ = _ := by rw [hs]; ring

theorem right_gauss_std (hn : Good n) (h : Nat.Coprime m n) :
    gaussSum (character n hn.1) (rightChar h ZMod.stdAddChar) =
      character n hn.1 (m : ZMod n) * gaussSum (character n hn.1) ZMod.stdAddChar := by
  have hs := squarefree_fourier_factor n hn.1 hn.2.1 hn.2.2
    (rightChar h ZMod.stdAddChar) (m : ZMod n)
  rw [right_std_shift h] at hs
  have hu := character_unit_square n hn.1 m h
  calc
    _ = character n hn.1 (m : ZMod n) ^ 2 *
        gaussSum (character n hn.1) (rightChar h ZMod.stdAddChar) := by
      rw [hu, one_mul]
    _ = _ := by rw [hs]; ring

theorem gauss_std_product (hm : Good m) (hn : Good n) (h : Nat.Coprime m n) :
    gaussSum (character (m * n) (by nlinarith [hm.1, hn.1])) ZMod.stdAddChar =
      character m hm.1 (n : ZMod m) * character n hn.1 (m : ZMod n) *
        gaussSum (character m hm.1) ZMod.stdAddChar *
          gaussSum (character n hn.1) ZMod.stdAddChar := by
  rw [gauss_crt hm.1 hn.1 h, left_gauss_std hm h, right_gauss_std hn h]
  ring

theorem star_gauss_std (hm : Good m) :
    star (gaussSum (character m hm.1) ZMod.stdAddChar) =
      character m hm.1 (-1 : ZMod m) *
        gaussSum (character m hm.1) ZMod.stdAddChar := by
  rw [star_gaussSum_eq, (character_quadratic m hm.1).inv]
  have hi : Inv.inv (ZMod.stdAddChar : AddChar (ZMod m) Complex) =
      (ZMod.stdAddChar : AddChar (ZMod m) Complex).mulShift (-1 : ZMod m) := by
    apply AddChar.ext
    intro x
    simp [AddChar.mulShift_apply]
  rw [hi, squarefree_fourier_factor m hm.1 hm.2.1 hm.2.2]

end PrimeFactorOscillations.IntegerQuadraticStandardCRT


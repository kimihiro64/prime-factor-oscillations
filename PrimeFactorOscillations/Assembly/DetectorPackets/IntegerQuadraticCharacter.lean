/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import Mathlib.NumberTheory.DirichletCharacter.Basic
import PrimeFactorOscillations.Assembly.DetectorPackets.IntegerQuadraticSieve

/-!
# IntegerQuadraticCharacter

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
# The actual Jacobi kernel as a Dirichlet character

This constructs the character used in the integer quadratic sieve from the
Jacobi symbol and proves its evaluation formula, including its zero mask.
Primitivity for odd squarefree moduli is a separate arithmetic theorem.
-/


noncomputable section
namespace PrimeFactorOscillations.IntegerQuadraticCharacter

open QuadraticCarrierPacket IntegerQuadraticSieve

theorem kernel_mod (u n : Nat) : kernel (u % n) n = kernel u n := by
  unfold kernel
  congr 1
  simpa only [Int.natCast_emod] using (jacobiSym.mod_left (u : Int) n).symm

def character (n : Nat) (hn : 1 < n) : DirichletCharacter Complex n := by
  letI : NeZero n := NeZero.mk (by omega)
  letI : Fact (1 < n) := Fact.mk hn
  exact {
    toFun := fun x => kernel x.val n
    map_one' := by simp [kernel, ZMod.val_one]
    map_mul' := by
      intro x y
      rw [ZMod.val_mul, kernel_mod, kernel_mul_left]
    map_nonunit' := by
      intro x hx
      have hcop : Not (Nat.Coprime x.val n) := by
        intro h
        apply hx
        have hunit := (ZMod.isUnit_iff_coprime x.val n).mpr h
        simpa only [ZMod.natCast_zmod_val] using hunit
      have hzero : jacobiSym (x.val : Int) n = 0 := by
        apply jacobiSym.eq_zero_iff.mpr
        refine And.intro (by omega) ?_
        simpa only [Int.gcd_natCast_natCast] using hcop
      simp only [kernel, hzero, Int.cast_zero]
  }

theorem character_apply (n : Nat) (hn : 1 < n) (x : ZMod n) :
    character n hn x = kernel x.val n := rfl

theorem character_natCast (n : Nat) (hn : 1 < n) (u : Nat) :
    character n hn (u : ZMod n) = kernel u n := by
  rw [character_apply, ZMod.val_natCast, kernel_mod]

theorem character_real (n : Nat) (hn : 1 < n) (x : ZMod n) :
    star (character n hn x) = character n hn x := by
  simp [character_apply, kernel]

theorem character_unit_square (n : Nat) (hn : 1 < n)
    (u : Nat) (hu : Nat.Coprime u n) :
    character n hn (u : ZMod n) ^ 2 = 1 := by
  rw [character_natCast, kernel_square_value u n (by omega)]
  have h : (u : Int).gcd n = 1 := by
    simpa only [Int.gcd_natCast_natCast] using hu
  simp only [h, ite_true]

theorem prime_character (p : Nat) [hp : Fact (Nat.Prime p)] :
    character p hp.out.one_lt =
      (quadraticChar (ZMod p)).ringHomComp (Int.castRingHom Complex) := by
  apply MulChar.ext'
  intro x
  rw [character_apply]
  unfold kernel
  rw [jacobiSym.legendreSym.to_jacobiSym p (x.val : Int) |>.symm]
  simp [legendreSym]

theorem prime_character_ne_one (p : Nat) (hp : Nat.Prime p)
    (hp2 : Not (p = 2)) : Not (character p hp.one_lt = 1) := by
  letI : Fact (Nat.Prime p) := Fact.mk hp
  rw [prime_character p]
  apply (MulChar.ringHomComp_ne_one_iff
    (show Function.Injective (Int.castRingHom Complex) from Int.cast_injective)).mpr
  apply quadraticChar_ne_one
  simpa only [ringChar.eq (ZMod p) p] using hp2

theorem prime_character_primitive (p : Nat) (hp : Nat.Prime p)
    (hp2 : Not (p = 2)) : (character p hp.one_lt).IsPrimitive := by
  letI : NeZero p := NeZero.mk hp.ne_zero
  change (character p hp.one_lt).conductor = p
  rcases (Nat.dvd_prime hp).mp (character p hp.one_lt).conductor_dvd_level
    with h | h
  . exact False.elim (prime_character_ne_one p hp hp2
      (DirichletCharacter.eq_one_iff_conductor_eq_one.mpr h))
  . exact h

end PrimeFactorOscillations.IntegerQuadraticCharacter

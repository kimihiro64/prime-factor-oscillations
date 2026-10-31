/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.FiniteFieldIntegerNativeRigidity

/-!
# Negative numerator characters retain their parity phase

The witness 4*A-1 proves nonprincipality even when A is a square.
This is the negative unit row needed for adjacent consecutive pairs.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace PrimeFactorOscillations.IntegerQuadraticCharacter

theorem negative_numerator_character_ne_one (A : Nat) (hA : 0 < A)
    (hD : Not (-(A : Int) = 0)) :
    Not (numeratorCharacter (-(A : Int)) hD = 1) := by
  let N : Nat := 4 * A - 1
  have hN : 3 <= N := by dsimp [N]; omega
  have hOdd : Odd N := by
    apply Nat.odd_iff.mpr
    dsimp [N]
    omega
  have hcast : (N : ZMod 4) = 3 := by
    dsimp [N]
    rw [Nat.cast_sub (by omega : 1 <= 4 * A), Nat.cast_mul]
    change (4 : ZMod 4) * (A : ZMod 4) - 1 = 3
    rw [show (4 : ZMod 4) = 0 from by decide, zero_mul]
    decide
  have hNcast : (N : Int) = 4 * (A : Int) - 1 := by
    dsimp [N]
    omega
  have hrem : (4 * (A : Int)) % (N : Int) = 1 := by
    have he : 4 * (A : Int) = (N : Int) + 1 := by omega
    rw [he, Int.add_emod, Int.emod_self, zero_add, Int.emod_emod]
    exact Int.emod_eq_of_lt (by omega) (by omega)
  have hprod : jacobiSym (4 * (A : Int)) N = 1 := by
    rw [jacobiSym.mod_left, hrem]
    simp
  have hpos : jacobiSym (A : Int) N = 1 := by
    have ht := jacobiSym.mul_left (4 : Int) (A : Int) N
    rw [jacobiSym.at_four hOdd, one_mul] at ht
    rw [<- ht]
    exact hprod
  have hneg : jacobiSym (-(A : Int)) N = -1 := by
    rw [jacobiSym.neg (A : Int) hOdd, hpos, mul_one, hcast]
    decide
  apply character_ne_one_of_neg_one (numeratorCharacter (-(A : Int)) hD)
    (N : ZMod (4 * (-(A : Int)).natAbs))
  rw [numerator_character_odd (-(A : Int)) hD N hOdd]
  exact_mod_cast hneg

end PrimeFactorOscillations.IntegerQuadraticCharacter

/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.DetectorPackets.IntegerQuadraticCharacter

/-!
# Parity of negative numerator characters

For a positive numerator magnitude a, the residue 4*a-1 is a direct
negative witness, whose sign comes from the odd negative-unit factor.
This proves nonprincipality without a prime-factor or squarefree hypothesis.
These classical character facts support the polynomial-height packet bound.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace PrimeFactorOscillations.IntegerQuadraticCharacter

theorem numerator_kernel_negative_residue (a : Nat) (ha : 0 < a) :
    numeratorKernel (-(a : Int)) (4 * a - 1) = -1 := by
  let u : Nat := 4 * a - 1
  have hu1 : 1 < u := by dsimp [u]; omega
  have hu4 : u % 4 = 3 := by dsimp [u]; omega
  have huo : Odd u := by
    apply Nat.odd_iff.mpr
    omega
  have huA : u + 1 = 4 * a := by dsimp [u]; omega
  have huAI : ((4 * a : Nat) : Int) = (u : Int) + 1 := by exact_mod_cast huA.symm
  have huIR : (1 : Int) < (u : Int) := by exact_mod_cast hu1
  have hmod : ((4 * a : Nat) : Int) % (u : Int) = 1 := by
    rw [huAI, Int.add_emod]
    simp only [Int.emod_self, zero_add,
      Int.emod_eq_of_lt (by norm_num : (0 : Int) <= 1) huIR]
  have hfour : jacobiSym (((4 * a : Nat) : Int)) u = 1 := by
    rw [jacobiSym.mod_left, hmod, jacobiSym.one_left]
  have hpositive : jacobiSym (a : Int) u = 1 := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat, jacobiSym.mul_left,
      jacobiSym.at_four huo, one_mul] using hfour
  have hnegative : jacobiSym (-1) u = -1 := by
    have ht := jacobiSym.mod_right (-1 : Int) huo
    simpa only [Int.natAbs_neg, Int.natAbs_one, Nat.mul_one, hu4,
      (show jacobiSym (-1) 3 = -1 by
        rw [jacobiSym.at_neg_one (by decide : Odd (3 : Nat))]
        rfl)] using ht
  have hj : jacobiSym (-(a : Int)) u = -1 := by
    rw [show -(a : Int) = (-1) * (a : Int) by ring,
      jacobiSym.mul_left, hnegative, hpositive]
    norm_num
  change numeratorKernel (-(a : Int)) u = -1
  simp only [numeratorKernel, ite_eq_left huo, hj, Int.cast_neg, Int.cast_one]

theorem numerator_character_negative_nonprincipal (a : Nat) (ha : 0 < a)
    (hD : Not (-(a : Int) = 0)) :
    Not (numeratorCharacter (-(a : Int)) hD = 1) := by
  apply character_ne_one_of_neg_one (numeratorCharacter (-(a : Int)) hD)
    ((4 * a - 1 : Nat) : ZMod (4 * (-(a : Int)).natAbs))
  rw [numerator_character_natCast, numerator_kernel_negative_residue a ha]

end PrimeFactorOscillations.IntegerQuadraticCharacter

/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.CarmichaelPrimeConductor
import PrimeFactorOscillations.Helpers.QRHCharacterChebyshev

/-!
# Inflation-independent QRH bounds for native tame modes

Prime-power level inflation introduces no missing Euler factor when the
primitive conductor is the same residue prime. Equality at every natural
input gives exact equality of the Chebyshev sums before any estimate.
The installed seven-eighths bound then depends on p and x, never on a.
This estimates individual nonprincipal modes, not the signed principal wave.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations.CarmichaelTameChebyshev

open BombieriVinogradov.SiegelWalfisz
open CarmichaelPrimePacket CarmichaelCorrelationSpectrum CarmichaelPrimeConductor

theorem character_eq_primitive_on_nat (p a : Nat) [NeZero p]
    (chi : DirichletCharacter Complex (p ^ (a + 1)))
    (hConductor : chi.conductor = p) (n : Nat) :
    chi (n : ZMod (p ^ (a + 1))) =
      chi.primitiveCharacter (n : ZMod chi.conductor) := by
  by_cases hCop : Nat.Coprime n p
  . have hLevel := hCop.pow_right (a + 1)
    have h := DirichletCharacter.primitiveCharacter_apply_of_isCoprime chi
      (a := (n : Int)) (Nat.isCoprime_iff_coprime.mpr hLevel)
    simpa only [Int.cast_natCast] using h.symm
  . have hLevel : Not (Nat.Coprime n (p ^ (a + 1))) := by
      intro h
      exact hCop (Nat.Coprime.of_dvd_right
        (PrimePowerCharacterConductor.prime_dvd_level p a) h)
    have hPrimitive : Not (Nat.Coprime n chi.conductor) := by
      rw [hConductor]
      exact hCop
    have hZero := (DirichletCharacter.apply_eq_zero_iff chi (n : Int)).mpr
      (Nat.isCoprime_iff_coprime.not.mpr hLevel)
    have hPrimitiveZero :=
      (DirichletCharacter.apply_eq_zero_iff chi.primitiveCharacter (n : Int)).mpr
        (Nat.isCoprime_iff_coprime.not.mpr hPrimitive)
    simpa only [Int.cast_natCast] using hZero.trans hPrimitiveZero.symm

theorem characterChebyshevSum_eq_primitive (p a : Nat) [NeZero p]
    (chi : DirichletCharacter Complex (p ^ (a + 1)))
    (hConductor : chi.conductor = p) (x : Nat) :
    characterChebyshevSum x chi =
      characterChebyshevSum x chi.primitiveCharacter := by
  simp only [characterChebyshevSum, BombieriVinogradov.VaughanMeanValue.psiCharacterSum]
  simp_rw [character_eq_primitive_on_nat p a chi hConductor]

theorem exists_tame_survivor_chebyshev_bound :
    exists A : Real, And (0 < A)
      (forall {p : Nat} [NeZero p], Nat.Prime p ->
        forall (a : Nat) (l : Nat.Primes), Nat.Coprime (l : Nat) p ->
          Dvd.dvd (l : Nat) (Monoid.exponent (Units (ZMod (p ^ (a + 1))))) ->
          forall chi : DirichletCharacter Complex (p ^ (a + 1)),
            Not (coefficient (weight (p ^ (a + 1)) l) chi = 0) ->
            Not (chi = 1) -> forall {x : Nat}, 2 <= x ->
              norm (characterChebyshevSum x chi) <=
                A * (x : Real) ^ (7 / 8 : Real) *
                  (1 + Real.log p + Real.log ((x : Real) + 2)) ^ 2) := by
  choose A hA hBound using QRH.exists_primitive_characterChebyshevSum_le_seven_eighths
  refine Exists.intro A (And.intro hA ?_)
  intro p inst hp a l hCop hDiv chi hNonzero hChi x hx
  have hConductor := tame_nonprincipal_survivor_conductor
    p a hp l hCop hDiv chi hNonzero hChi
  let : NeZero chi.conductor := NeZero.mk chi.conductor_ne_zero
  have hPrimitiveNe :=
    BombieriVinogradov.DirichletCharacter.primitiveCharacter_ne_one_of_ne_one chi hChi
  have hThree :=
    BombieriVinogradov.DirichletCharacter.three_le_level_of_ne_one
      chi.primitiveCharacter hPrimitiveNe
  have hPrimitiveBound := hBound hThree chi.primitiveCharacter hPrimitiveNe
    chi.primitiveCharacter_isPrimitive hx
  calc
    norm (characterChebyshevSum x chi) =
        norm (characterChebyshevSum x chi.primitiveCharacter) :=
      congrArg norm (characterChebyshevSum_eq_primitive p a chi hConductor x)
    _ <= A * (x : Real) ^ (7 / 8 : Real) *
        (1 + Real.log chi.conductor + Real.log ((x : Real) + 2)) ^ 2 :=
      hPrimitiveBound
    _ = _ := by rw [hConductor]

end PrimeFactorOscillations.CarmichaelTameChebyshev

/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.CarmichaelTameChebyshev
import PrimeFactorOscillations.Assembly.CarmichaelWildConductor

/-!
# Exact prime-power transfer for native character waves

If an imprimitive character and its primitive ancestor have prime-power
moduli with the same residue prime, their values agree even on nonunits.
The Chebyshev sums are therefore exactly equal, with no Euler correction.
The installed primitive QRH bound depends on the true conductor exponent
b + 1, independently of the arbitrary presentation inflation a.
The native odd-wild specialization has true conductor p^2.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations.CarmichaelPrimePowerChebyshev

open BombieriVinogradov.SiegelWalfisz
open CarmichaelPrimePacket CarmichaelCorrelationSpectrum

local instance primeLabelNeZero (l : Nat.Primes) : NeZero (l : Nat) :=
  NeZero.mk l.property.ne_zero

theorem character_eq_primitive_on_nat (p a b : Nat) [NeZero p]
    (chi : DirichletCharacter Complex (p ^ (a + b + 1)))
    (hConductor : chi.conductor = p ^ (b + 1)) (n : Nat) :
    chi (n : ZMod (p ^ (a + b + 1))) =
      chi.primitiveCharacter (n : ZMod chi.conductor) := by
  by_cases hCop : Nat.Coprime n p
  . have hLevel := hCop.pow_right (a + b + 1)
    have h := DirichletCharacter.primitiveCharacter_apply_of_isCoprime chi
      (a := (n : Int)) (Nat.isCoprime_iff_coprime.mpr hLevel)
    simpa only [Int.cast_natCast] using h.symm
  . have hLevel : Not (Nat.Coprime n (p ^ (a + b + 1))) := by
      intro h
      exact hCop (Nat.Coprime.of_dvd_right
        (PrimePowerCharacterConductor.prime_dvd_level p (a + b)) h)
    have hPrimitive : Not (Nat.Coprime n chi.conductor) := by
      rw [hConductor]
      intro h
      exact hCop (Nat.Coprime.of_dvd_right
        (PrimePowerCharacterConductor.prime_dvd_level p b) h)
    have hZero := (DirichletCharacter.apply_eq_zero_iff chi (n : Int)).mpr
      (Nat.isCoprime_iff_coprime.not.mpr hLevel)
    have hPrimitiveZero :=
      (DirichletCharacter.apply_eq_zero_iff chi.primitiveCharacter (n : Int)).mpr
        (Nat.isCoprime_iff_coprime.not.mpr hPrimitive)
    simpa only [Int.cast_natCast] using hZero.trans hPrimitiveZero.symm

theorem characterChebyshevSum_eq_primitive (p a b : Nat) [NeZero p]
    (chi : DirichletCharacter Complex (p ^ (a + b + 1)))
    (hConductor : chi.conductor = p ^ (b + 1)) (x : Nat) :
    characterChebyshevSum x chi =
      characterChebyshevSum x chi.primitiveCharacter := by
  simp only [characterChebyshevSum, BombieriVinogradov.VaughanMeanValue.psiCharacterSum]
  simp_rw [character_eq_primitive_on_nat p a b chi hConductor]

theorem exists_primePower_chebyshev_bound :
    exists A : Real, And (0 < A)
      (forall (p a b : Nat) [NeZero p],
        forall chi : DirichletCharacter Complex (p ^ (a + b + 1)),
          chi.conductor = p ^ (b + 1) -> Not (chi = 1) ->
            forall {x : Nat}, 2 <= x ->
              norm (characterChebyshevSum x chi) <=
                A * (x : Real) ^ (7 / 8 : Real) *
                  (1 + ((b : Real) + 1) * Real.log p +
                    Real.log ((x : Real) + 2)) ^ 2) := by
  choose A hA hBound using QRH.exists_primitive_characterChebyshevSum_le_seven_eighths
  refine Exists.intro A (And.intro hA ?_)
  intro p a b inst chi hConductor hChi x hx
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
      congrArg norm (characterChebyshevSum_eq_primitive p a b chi hConductor x)
    _ <= A * (x : Real) ^ (7 / 8 : Real) *
        (1 + Real.log chi.conductor + Real.log ((x : Real) + 2)) ^ 2 :=
      hPrimitiveBound
    _ = _ := by
      rw [hConductor, Nat.cast_pow, Real.log_pow, Nat.cast_add, Nat.cast_one]

theorem exists_wild_survivor_chebyshev_bound :
    exists A : Real, And (0 < A)
      (forall (l : Nat.Primes) (a : Nat), Not ((l : Nat) = 2) ->
        forall chi : DirichletCharacter Complex ((l : Nat) ^ (a + 2)),
          Not (coefficient (weight ((l : Nat) ^ (a + 2)) l) chi = 0) ->
          Not (chi = 1) -> forall {x : Nat}, 2 <= x ->
            norm (characterChebyshevSum x chi) <=
              A * (x : Real) ^ (7 / 8 : Real) *
                (1 + 2 * Real.log (l : Nat) + Real.log ((x : Real) + 2)) ^ 2) := by
  choose A hA hBound using exists_primePower_chebyshev_bound
  refine Exists.intro A (And.intro hA ?_)
  intro l a hTwo chi hNonzero hChi x hx
  let : NeZero (l : Nat) := NeZero.mk l.property.ne_zero
  have hConductor := CarmichaelWildConductor.wild_nonprincipal_survivor_conductor
    l a hTwo chi hNonzero hChi
  simpa only [Nat.cast_one, one_add_one_eq_two] using
    hBound (l : Nat) a 1 chi hConductor hChi hx

end PrimeFactorOscillations.CarmichaelPrimePowerChebyshev

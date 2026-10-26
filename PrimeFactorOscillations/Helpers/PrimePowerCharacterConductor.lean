/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.NumberTheory.DirichletCharacter.Basic
import PrimeFactorOscillations.Helpers.PrimePowerConductorReduction

/-!
# Tame characters at inflated prime-power levels

A unit character annihilated by an exponent coprime to the residue prime
factors through that prime. The proof uses the actual reduction kernel,
whose cardinality is already proved in the return-spectrum library.
No absolute estimate or cyclicity hypothesis is used.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations.PrimePowerCharacterConductor

theorem prime_dvd_level (p a : Nat) : Dvd.dvd p (p ^ (a + 1)) := by
  simp

theorem tame_factorsThrough (p a m : Nat) [NeZero p]
    (hp : Nat.Prime p) (hCop : Nat.Coprime m p)
    (chi : DirichletCharacter Complex (p ^ (a + 1)))
    (hPower : forall u : Units (ZMod (p ^ (a + 1))),
      (chi (u : ZMod (p ^ (a + 1)))) ^ m = 1) :
    chi.FactorsThrough p := by
  let hd := prime_dvd_level p a
  let f := ZMod.unitsMap hd
  have hCard : Nat.card f.ker = p ^ a := by
    let P : Nat -> Prop := fun d =>
      forall h : Dvd.dvd d (p ^ (a + 1)), Nat.card (ZMod.unitsMap h).ker = p ^ a
    have hP : P (p ^ (0 + 1)) := by
      intro h
      exact PrimePowerReturnSpectrum.conductor_kernel_card p a 0 hp
    have hEq : p ^ (0 + 1) = p := by simp
    have hPrime : P p := Eq.mp (congrArg P hEq) hP
    exact hPrime hd
  apply (DirichletCharacter.factorsThrough_iff_ker_unitsMap hd).mpr
  intro u hu
  let v : f.ker := Subtype.mk u hu
  have hv : v ^ (p ^ a) = 1 := by
    rw [<- hCard]
    exact pow_card_eq_one'
  have huPower : u ^ (p ^ a) = 1 := by
    exact congrArg (fun z : f.ker => z.val) hv
  have hLocal : (chi.toUnitHom u) ^ (p ^ a) = 1 := by
    rw [<- map_pow, huPower, map_one]
  have hLabel : (chi.toUnitHom u) ^ m = 1 := by
    apply Units.ext
    change (chi (u : ZMod (p ^ (a + 1)))) ^ m = 1
    exact hPower u
  have hOrder : Dvd.dvd (orderOf (chi.toUnitHom u)) 1 := by
    have hBoth := Nat.dvd_gcd
      (orderOf_dvd_iff_pow_eq_one.mpr hLabel)
      (orderOf_dvd_iff_pow_eq_one.mpr hLocal)
    rwa [(hCop.pow_right a).gcd_eq_one] at hBoth
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp hOrder)

theorem tame_conductor_dvd (p a m : Nat) [NeZero p]
    (hp : Nat.Prime p) (hCop : Nat.Coprime m p)
    (chi : DirichletCharacter Complex (p ^ (a + 1)))
    (hPower : forall u : Units (ZMod (p ^ (a + 1))),
      (chi (u : ZMod (p ^ (a + 1)))) ^ m = 1) :
    Dvd.dvd chi.conductor p :=
  DirichletCharacter.conductor_dvd_of_mem_conductorSet chi
    (tame_factorsThrough p a m hp hCop chi hPower)

theorem tame_nonprincipal_conductor (p a m : Nat) [NeZero p]
    (hp : Nat.Prime p) (hCop : Nat.Coprime m p)
    (chi : DirichletCharacter Complex (p ^ (a + 1)))
    (hPower : forall u : Units (ZMod (p ^ (a + 1))),
      (chi (u : ZMod (p ^ (a + 1)))) ^ m = 1)
    (hChi : Not (chi = 1)) :
    chi.conductor = p := by
  have hDiv := tame_conductor_dvd p a m hp hCop chi hPower
  rcases (Nat.dvd_prime hp).mp hDiv with hOne | hPrime
  . exact (hChi (DirichletCharacter.eq_one_iff_conductor_eq_one.mpr hOne)).elim
  . exact hPrime

theorem tame_values_eq_of_reduction_eq (p a m : Nat) [NeZero p]
    (hp : Nat.Prime p) (hCop : Nat.Coprime m p)
    (chi : DirichletCharacter Complex (p ^ (a + 1)))
    (hPower : forall u : Units (ZMod (p ^ (a + 1))),
      (chi (u : ZMod (p ^ (a + 1)))) ^ m = 1)
    (u v : Units (ZMod (p ^ (a + 1))))
    (hReduce : ZMod.unitsMap (prime_dvd_level p a) u =
      ZMod.unitsMap (prime_dvd_level p a) v) :
    chi (u : ZMod (p ^ (a + 1))) = chi (v : ZMod (p ^ (a + 1))) := by
  choose hd psi hChi using tame_factorsThrough p a m hp hCop chi hPower
  have hUnits : chi.toUnitHom u = chi.toUnitHom v := by
    rw [hChi, DirichletCharacter.changeLevel_toUnitHom]
    exact congrArg psi.toUnitHom hReduce
  have hValues := congrArg (fun z : Units Complex => (z : Complex)) hUnits
  simpa only [MulChar.coe_toUnitHom] using hValues

end PrimeFactorOscillations.PrimePowerCharacterConductor

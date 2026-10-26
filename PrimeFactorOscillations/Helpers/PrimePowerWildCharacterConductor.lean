/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.Tactic.Ring
import PrimeFactorOscillations.Helpers.PrimePowerCharacterConductor

/-!
# Exact wild conductors at odd prime-power levels

Characters killed by the residue prime descend to its square. For a
nonprincipal character that square is the exact conductor. Cyclicity is
used only in the upper descent; the obstruction to descent to the prime
is proved for every residue prime. No analytic estimate is used.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations.PrimePowerWildCharacterConductor

theorem primeSquare_dvd_level (p a : Nat) :
    Dvd.dvd (p ^ 2) (p ^ (a + 2)) :=
  PrimePowerReturnSpectrum.conductor_dvd p a 1

theorem prime_dvd_exponent (p a : Nat) [NeZero p] (hp : Nat.Prime p) :
    Dvd.dvd p (Monoid.exponent (Units (ZMod (p ^ (a + 2))))) := by
  let G := Units (ZMod (p ^ (a + 2)))
  have hGroup : Nat.card G = p ^ (a + 1) * (p - 1) := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]
    exact Nat.totient_prime_pow_succ hp (a + 1)
  have hPrime : Dvd.dvd p (Fintype.card G) := by
    rw [<- Nat.card_eq_fintype_card, hGroup]
    refine Dvd.intro (p ^ a * (p - 1)) ?_
    rw [Nat.pow_succ]
    ring
  let : Fact (Nat.Prime p) := Fact.mk hp
  choose u hu using exists_prime_orderOf_dvd_card (G := G) p hPrime
  have hDiv := orderOf_dvd_iff_pow_eq_one.mpr (Monoid.pow_exponent_eq_one u)
  rwa [hu] at hDiv

theorem odd_wild_factorsThrough (p a : Nat) [NeZero p]
    (hp : Nat.Prime p) (hpTwo : Not (p = 2))
    (chi : DirichletCharacter Complex (p ^ (a + 2)))
    (hPower : forall u : Units (ZMod (p ^ (a + 2))),
      (chi (u : ZMod (p ^ (a + 2)))) ^ p = 1) :
    chi.FactorsThrough (p ^ 2) := by
  let G := Units (ZMod (p ^ (a + 2)))
  let : IsCyclic G := ZMod.isCyclic_units_of_prime_pow p hp hpTwo (a + 2)
  let hd := primeSquare_dvd_level p a
  let f := ZMod.unitsMap hd
  let H : Subgroup G := (powMonoidHom p).range
  have hGroup : Nat.card G = p ^ (a + 1) * (p - 1) := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]
    exact Nat.totient_prime_pow_succ hp (a + 1)
  have hPrime : Dvd.dvd p (Nat.card G) := by
    refine Dvd.intro (p ^ a * (p - 1)) ?_
    rw [hGroup, Nat.pow_succ]
    ring
  have hRange : Nat.card H = p ^ a * (p - 1) := by
    rw [IsCyclic.card_powMonoidHom_range, Nat.gcd_eq_right hPrime, hGroup]
    calc
      _ = p * (p ^ a * (p - 1)) / p := by
        congr 1
        rw [Nat.pow_succ]
        ring
      _ = _ := Nat.mul_div_cancel_left _ hp.pos
  have hKernel : Nat.card f.ker = p ^ a :=
    PrimePowerReturnSpectrum.conductor_kernel_card p a 1 hp
  have hLe : f.ker <= H := by
    apply IsCyclic.subgroup_le_iff_card_dvd.mpr
    rw [hKernel, hRange]
    exact dvd_mul_right (p ^ a) (p - 1)
  apply (DirichletCharacter.factorsThrough_iff_ker_unitsMap hd).mpr
  intro u hu
  choose v hv using (MonoidHom.mem_range.mp (hLe hu))
  change chi.toUnitHom u = 1
  rw [<- hv]
  change chi.toUnitHom (v ^ p) = 1
  rw [map_pow]
  apply Units.ext
  change (chi (v : ZMod (p ^ (a + 2)))) ^ p = 1
  exact hPower v

theorem odd_wild_conductor_dvd (p a : Nat) [NeZero p]
    (hp : Nat.Prime p) (hpTwo : Not (p = 2))
    (chi : DirichletCharacter Complex (p ^ (a + 2)))
    (hPower : forall u : Units (ZMod (p ^ (a + 2))),
      (chi (u : ZMod (p ^ (a + 2)))) ^ p = 1) :
    Dvd.dvd chi.conductor (p ^ 2) :=
  DirichletCharacter.conductor_dvd_of_mem_conductorSet chi
    (odd_wild_factorsThrough p a hp hpTwo chi hPower)

theorem nonprincipal_not_factorsThrough_prime (p a : Nat) [NeZero p]
    (hp : Nat.Prime p)
    (chi : DirichletCharacter Complex (p ^ (a + 2)))
    (hPower : forall u : Units (ZMod (p ^ (a + 2))),
      (chi (u : ZMod (p ^ (a + 2)))) ^ p = 1)
    (hChi : Not (chi = 1)) :
    Not (chi.FactorsThrough p) := by
  intro hFactor
  choose hd psi hEquality using hFactor
  apply hChi
  apply MulChar.eq_one_iff.mpr
  intro u
  let v := ZMod.unitsMap hd u
  have hv : v ^ (p - 1) = 1 := by
    have h := pow_card_eq_one' (x := v)
    simpa only [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient,
      Nat.totient_prime hp] using h
  have hPhi : (chi.toUnitHom u) ^ (p - 1) = 1 := by
    rw [hEquality, DirichletCharacter.changeLevel_toUnitHom]
    change (psi.toUnitHom v) ^ (p - 1) = 1
    rw [<- map_pow, hv, map_one]
  have hLabel : (chi.toUnitHom u) ^ p = 1 := by
    apply Units.ext
    change (chi (u : ZMod (p ^ (a + 2)))) ^ p = 1
    exact hPower u
  have hCop : Nat.Coprime p (p - 1) :=
    (Nat.coprime_self_sub_right hp.one_lt.le).mpr (by simp)
  have hOrder : Dvd.dvd (orderOf (chi.toUnitHom u)) 1 := by
    have hBoth := Nat.dvd_gcd
      (orderOf_dvd_iff_pow_eq_one.mpr hLabel)
      (orderOf_dvd_iff_pow_eq_one.mpr hPhi)
    rwa [hCop.gcd_eq_one] at hBoth
  have hOne := orderOf_eq_one_iff.mp (Nat.dvd_one.mp hOrder)
  have hValues := congrArg (fun z : Units Complex => (z : Complex)) hOne
  simpa only [MulChar.coe_toUnitHom, Units.val_one] using hValues

theorem odd_wild_nonprincipal_conductor (p a : Nat) [NeZero p]
    (hp : Nat.Prime p) (hpTwo : Not (p = 2))
    (chi : DirichletCharacter Complex (p ^ (a + 2)))
    (hPower : forall u : Units (ZMod (p ^ (a + 2))),
      (chi (u : ZMod (p ^ (a + 2)))) ^ p = 1)
    (hChi : Not (chi = 1)) :
    chi.conductor = p ^ 2 := by
  have hDiv := odd_wild_conductor_dvd p a hp hpTwo chi hPower
  choose k hk hEquality using (Nat.dvd_prime_pow hp).mp hDiv
  by_cases hTwo : k = 2
  . simpa only [hTwo] using hEquality
  . by_cases hZero : k = 0
    . have hOne : chi.conductor = 1 := by
        rw [hEquality, hZero, Nat.pow_zero]
      exact (hChi (DirichletCharacter.eq_one_iff_conductor_eq_one.mpr hOne)).elim
    . have hOne : k = 1 := by omega
      have hConductor : Dvd.dvd chi.conductor p := by
        rw [hEquality, hOne, Nat.pow_one]
      have hFactor : chi.FactorsThrough p :=
        (DirichletCharacter.mem_conductorSet_iff_conductor_dvd chi
          (PrimePowerCharacterConductor.prime_dvd_level p (a + 1))).mpr hConductor
      exact (nonprincipal_not_factorsThrough_prime p a hp chi hPower hChi hFactor).elim

end PrimeFactorOscillations.PrimePowerWildCharacterConductor

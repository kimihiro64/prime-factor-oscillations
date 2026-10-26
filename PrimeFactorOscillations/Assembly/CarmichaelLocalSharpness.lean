/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.CarmichaelConductorAssembly

/-!
# A sharp surviving mode at every native prime-power level

The maintained tame, odd-wild, and two-power classifications are consumed
on their actual domains. Every admissible native prime-power kernel has
a nonprincipal surviving character attaining its entire least spectral
conductor. The small levels two, four and eight are treated explicitly.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations.CarmichaelLocalSharpness

open CarmichaelPrimePacket CarmichaelCorrelation CarmichaelCorrelationSpectrum
open CarmichaelPrimePacketSpectrum CarmichaelSpectralConductor
open CarmichaelTwoPowerConductor CarmichaelConductorAssembly

local instance primeNeZero (p : Nat.Primes) : NeZero (p : Nat) :=
  NeZero.mk p.property.ne_zero

theorem exists_nonprincipal_survivor (q : Nat) [NeZero q] (l : Nat.Primes)
    (hDiv : Dvd.dvd (l : Nat) (Monoid.exponent (Units (ZMod q)))) :
    exists chi : DirichletCharacter Complex q,
      Not (chi = 1) /\ Not (coefficient (weight q l) chi = 0) := by
  choose chi hChi hPower hCoefficient using exists_nonprincipal_prime_character q l hDiv
  have hD : (1 : Real) < (index q l : Real) := by
    exact_mod_cast (show 1 < index q l from lt_of_lt_of_le (by decide) (index_ge_two q l hDiv))
  have hDen : Not ((index q l : Real) - 1 = 0) := sub_ne_zero.mpr (ne_of_gt hD)
  refine Exists.intro chi (And.intro hChi ?_)
  rw [hCoefficient]
  exact div_ne_zero one_ne_zero (pow_ne_zero _ hDen)

theorem spectralConductor_ne_one (q : Nat) [NeZero q] (l : Nat.Primes)
    (hDiv : Dvd.dvd (l : Nat) (Monoid.exponent (Units (ZMod q)))) :
    Not (spectralConductor q l = 1) := by
  choose chi hChi hNonzero using exists_nonprincipal_survivor q l hDiv
  have h := (spectralConductor_dvd_iff q l (spectralConductor q l)).mp
    (dvd_refl _) chi hNonzero
  intro hOne
  rw [hOne] at h
  exact hChi (DirichletCharacter.eq_one_iff_conductor_eq_one.mpr (Nat.dvd_one.mp h))

theorem sharp_mode_of_common_conductor (q : Nat) [NeZero q] (l : Nat.Primes)
    (hDiv : Dvd.dvd (l : Nat) (Monoid.exponent (Units (ZMod q))))
    (f : Nat)
    (hAll : forall chi : DirichletCharacter Complex q,
      Not (coefficient (weight q l) chi = 0) -> Not (chi = 1) -> chi.conductor = f) :
    exists chi : DirichletCharacter Complex q,
      Not (chi = 1) /\ Not (coefficient (weight q l) chi = 0) /\
        chi.conductor = spectralConductor q l := by
  choose chi hChi hNonzero using exists_nonprincipal_survivor q l hDiv
  have hUpper : Dvd.dvd (spectralConductor q l) f := by
    apply (spectralConductor_dvd_iff q l f).mpr
    intro psi hPsi
    by_cases hPrincipal : psi = 1
    . rw [hPrincipal, DirichletCharacter.conductor_one]
      exact one_dvd _
    . rw [hAll psi hPsi hPrincipal]
  have hLower : Dvd.dvd f (spectralConductor q l) := by
    have h := (spectralConductor_dvd_iff q l (spectralConductor q l)).mp
      (dvd_refl _) chi hNonzero
    rwa [hAll chi hNonzero hChi] at h
  have hM : spectralConductor q l = f := Nat.dvd_antisymm hUpper hLower
  exact Exists.intro chi (And.intro hChi
    (And.intro hNonzero ((hAll chi hNonzero hChi).trans hM.symm)))

theorem two_power_has_sharp_mode (a : Nat)
    (hDiv : Dvd.dvd 2 (Monoid.exponent (Units (ZMod (2 ^ (a + 1)))))) :
    exists chi : DirichletCharacter Complex (2 ^ (a + 1)),
      Not (chi = 1) /\ Not (coefficient (weight (2 ^ (a + 1)) labelTwo) chi = 0) /\
        chi.conductor = spectralConductor (2 ^ (a + 1)) labelTwo := by
  cases a with
  | zero => exact (level_two_inadmissible hDiv).elim
  | succ a =>
    cases a with
    | zero =>
      exact sharp_mode_of_common_conductor 4 labelTwo hDiv 4
        (fun chi _ hChi => level_four_nonprincipal_conductor chi hChi)
    | succ a =>
      cases a with
      | zero =>
        choose chi hChi hCond hCoefficient using exists_level_eight_conductor_eight_survivor
        have hNonzero : Not (coefficient (weight 8 labelTwo) chi = 0) := by
          rw [hCoefficient]
          norm_num
        have hLower : Dvd.dvd 8 (spectralConductor 8 labelTwo) := by
          have h := (spectralConductor_dvd_iff 8 labelTwo
            (spectralConductor 8 labelTwo)).mp (dvd_refl _) chi hNonzero
          rwa [hCond] at h
        have hM : spectralConductor 8 labelTwo = 8 :=
          Nat.dvd_antisymm (spectralConductor_dvd_level 8 labelTwo) hLower
        exact Exists.intro chi (And.intro hChi
          (And.intro hNonzero (hCond.trans hM.symm)))
      | succ a =>
        exact sharp_mode_of_common_conductor (2 ^ (a + 4)) labelTwo hDiv 8
          (large_nonprincipal_survivor_conductor a)

theorem prime_power_has_sharp_mode (p l : Nat.Primes) (a : Nat)
    (hDiv : Dvd.dvd (l : Nat)
      (Monoid.exponent (Units (ZMod ((p : Nat) ^ (a + 1)))))) :
    exists chi : DirichletCharacter Complex ((p : Nat) ^ (a + 1)),
      Not (chi = 1) /\ Not (coefficient (weight ((p : Nat) ^ (a + 1)) l) chi = 0) /\
        chi.conductor = spectralConductor ((p : Nat) ^ (a + 1)) l := by
  by_cases hSame : l = p
  . subst l
    by_cases hTwo : (p : Nat) = 2
    . have hP : p = labelTwo := Subtype.ext hTwo
      subst p
      exact two_power_has_sharp_mode a hDiv
    . cases a with
      | zero =>
        let P : Nat -> Prop := fun d =>
          Dvd.dvd p.val (Monoid.exponent (Units (ZMod d)))
        have hMod : p.val ^ (0 + 1) = p.val := pow_one p.val
        have hDivPrime : P p.val := Eq.mp (congrArg P hMod) hDiv
        have hBound : Dvd.dvd p.val (p.val - 1) :=
          Eq.mp (congrArg (fun E : Nat => Dvd.dvd p.val E)
            (PrimeOrderReturnIndex.prime_unit_exponent p)) hDivPrime
        have hLe := Nat.le_of_dvd (Nat.sub_pos_of_lt p.property.one_lt) hBound
        exact ((not_le_of_gt (Nat.sub_lt p.property.pos (by decide : 0 < 1))) hLe).elim
      | succ a =>
        exact sharp_mode_of_common_conductor ((p : Nat) ^ (a + 2)) p hDiv
          ((p : Nat) ^ 2) (CarmichaelWildConductor.wild_nonprincipal_survivor_conductor p a hTwo)
  . have hCop : Nat.Coprime (l : Nat) (p : Nat) := by
      apply (l.property.coprime_iff_not_dvd).mpr
      intro hDivPrime
      rcases (Nat.dvd_prime p.property).mp hDivPrime with hOne | hEqual
      . exact l.property.ne_one hOne
      . exact hSame (Subtype.ext hEqual)
    exact sharp_mode_of_common_conductor ((p : Nat) ^ (a + 1)) l hDiv (p : Nat)
      (fun chi hNonzero hChi =>
        CarmichaelPrimeConductor.tame_nonprincipal_survivor_conductor (p : Nat) a
          p.property l hCop hDiv chi hNonzero hChi)

end PrimeFactorOscillations.CarmichaelLocalSharpness

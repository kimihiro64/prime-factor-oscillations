/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.CarmichaelPrimePacketSpectrum
import PrimeFactorOscillations.Helpers.PrimePowerCharacterConductor

/-!
# Exact tame conductor compression of the native return kernel

At a prime-power level, a return label coprime to the residue prime
retains only the principal character and characters of conductor exactly
that prime. The complete original kernel, with every complex phase, is
constant on reduction fibers. A nonprincipal mode survives, so the prime
conductor cost is real. This gives no independent arithmetic upper bound.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations.CarmichaelPrimeConductor

open CarmichaelPrimePacket CarmichaelCorrelation CarmichaelCorrelationSpectrum
open CarmichaelPrimePacketSpectrum PrimePowerCharacterConductor

theorem tame_survivor_factorsThrough (p a : Nat) [NeZero p]
    (hp : Nat.Prime p) (l : Nat.Primes) (hCop : Nat.Coprime (l : Nat) p)
    (hDiv : Dvd.dvd (l : Nat) (Monoid.exponent (Units (ZMod (p ^ (a + 1))))))
    (chi : DirichletCharacter Complex (p ^ (a + 1)))
    (hNonzero : Not (coefficient (weight (p ^ (a + 1)) l) chi = 0)) :
    chi.FactorsThrough p :=
  tame_factorsThrough p a (l : Nat) hp hCop chi
    (nonzero_coefficient_prime_power (p ^ (a + 1)) l hDiv chi hNonzero)

theorem tame_survivor_conductor_dvd (p a : Nat) [NeZero p]
    (hp : Nat.Prime p) (l : Nat.Primes) (hCop : Nat.Coprime (l : Nat) p)
    (hDiv : Dvd.dvd (l : Nat) (Monoid.exponent (Units (ZMod (p ^ (a + 1))))))
    (chi : DirichletCharacter Complex (p ^ (a + 1)))
    (hNonzero : Not (coefficient (weight (p ^ (a + 1)) l) chi = 0)) :
    Dvd.dvd chi.conductor p :=
  tame_conductor_dvd p a (l : Nat) hp hCop chi
    (nonzero_coefficient_prime_power (p ^ (a + 1)) l hDiv chi hNonzero)

theorem tame_nonprincipal_survivor_conductor (p a : Nat) [NeZero p]
    (hp : Nat.Prime p) (l : Nat.Primes) (hCop : Nat.Coprime (l : Nat) p)
    (hDiv : Dvd.dvd (l : Nat) (Monoid.exponent (Units (ZMod (p ^ (a + 1))))))
    (chi : DirichletCharacter Complex (p ^ (a + 1)))
    (hNonzero : Not (coefficient (weight (p ^ (a + 1)) l) chi = 0))
    (hChi : Not (chi = 1)) :
    chi.conductor = p :=
  tame_nonprincipal_conductor p a (l : Nat) hp hCop chi
    (nonzero_coefficient_prime_power (p ^ (a + 1)) l hDiv chi hNonzero) hChi

theorem tame_kernel_eq_of_reduction_eq (p a : Nat) [NeZero p]
    (hp : Nat.Prime p) (l : Nat.Primes) (hCop : Nat.Coprime (l : Nat) p)
    (hDiv : Dvd.dvd (l : Nat) (Monoid.exponent (Units (ZMod (p ^ (a + 1))))))
    (u v : Units (ZMod (p ^ (a + 1))))
    (hReduce : ZMod.unitsMap (prime_dvd_level p a) u =
      ZMod.unitsMap (prime_dvd_level p a) v) :
    kernel (weight (p ^ (a + 1)) l) u =
      kernel (weight (p ^ (a + 1)) l) v := by
  classical
  apply Complex.ofReal_injective
  rw [kernel_expansion, kernel_expansion]
  apply Finset.sum_congr rfl
  intro chi _
  by_cases hZero : coefficient (weight (p ^ (a + 1)) l) chi = 0
  . simp only [hZero, Complex.ofReal_zero, zero_mul]
  . apply congrArg (fun z : Complex =>
      (coefficient (weight (p ^ (a + 1)) l) chi : Complex) * z)
    change chi (Units.val (Inv.inv u)) = chi (Units.val (Inv.inv v))
    apply tame_values_eq_of_reduction_eq p a (l : Nat) hp hCop chi
      (nonzero_coefficient_prime_power (p ^ (a + 1)) l hDiv chi hZero)
    simpa only [map_inv] using
      congrArg (fun z : Units (ZMod p) => Inv.inv z) hReduce

theorem tame_kernel_descends_to_prime (p a : Nat) [NeZero p]
    (hp : Nat.Prime p) (l : Nat.Primes) (hCop : Nat.Coprime (l : Nat) p)
    (hDiv : Dvd.dvd (l : Nat) (Monoid.exponent (Units (ZMod (p ^ (a + 1)))))) :
    exists k : Units (ZMod p) -> Real,
      forall u : Units (ZMod (p ^ (a + 1))),
        kernel (weight (p ^ (a + 1)) l) u =
          k (ZMod.unitsMap (prime_dvd_level p a) u) := by
  let lift : Units (ZMod p) -> Units (ZMod (p ^ (a + 1))) :=
    fun v => Classical.choose (ZMod.unitsMap_surjective (prime_dvd_level p a) v)
  have hLift (v : Units (ZMod p)) :
      ZMod.unitsMap (prime_dvd_level p a) (lift v) = v :=
    Classical.choose_spec (ZMod.unitsMap_surjective (prime_dvd_level p a) v)
  refine Exists.intro (fun v => kernel (weight (p ^ (a + 1)) l) (lift v)) ?_
  intro u
  exact tame_kernel_eq_of_reduction_eq p a hp l hCop hDiv u
    (lift (ZMod.unitsMap (prime_dvd_level p a) u))
    (hLift (ZMod.unitsMap (prime_dvd_level p a) u)).symm

theorem exists_tame_prime_conductor_survivor (p a : Nat) [NeZero p]
    (hp : Nat.Prime p) (l : Nat.Primes) (hCop : Nat.Coprime (l : Nat) p)
    (hDiv : Dvd.dvd (l : Nat) (Monoid.exponent (Units (ZMod (p ^ (a + 1)))))) :
    exists chi : DirichletCharacter Complex (p ^ (a + 1)),
      Not (chi = 1) /\ chi.conductor = p /\
        coefficient (weight (p ^ (a + 1)) l) chi =
          1 / ((index (p ^ (a + 1)) l : Real) - 1) ^ 2 := by
  choose chi hChi hPower hCoefficient using
    exists_nonprincipal_prime_character (p ^ (a + 1)) l hDiv
  exact Exists.intro chi (And.intro hChi
    (And.intro (tame_nonprincipal_conductor p a (l : Nat) hp hCop chi hPower hChi)
      hCoefficient))

end PrimeFactorOscillations.CarmichaelPrimeConductor

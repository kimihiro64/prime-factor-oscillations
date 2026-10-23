/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.GroupTheory.Perm.Cycle.Type
import PrimeFactorOscillations.Helpers.PrimePowerReturnTrace

/-!
# The primitive-frequency classification, including two

Cauchy's theorem handles the noncyclic two-power unit groups. The actual
power kernel cannot have cardinal divisible by a prime absent from its
annihilating exponent. The full centered primitive signal is classified
without excluding any prime or any natural power exponent.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations.PrimePowerReturnSpectrum

open scoped BigOperators
open RationalFourierOrbit

theorem kernel_prime_divisor_forces_power (n : Nat) [NeZero n]
    (k p : Nat) (hp : Nat.Prime p)
    (hd : Dvd.dvd p (Fintype.card (powerKernel n k))) : Dvd.dvd p k := by
  classical
  letI : Fact (Nat.Prime p) := Fact.mk hp
  choose u hu using (exists_prime_orderOf_dvd_card (G := powerKernel n k) p hd)
  have hpow : u ^ k = 1 := by
    apply Subtype.ext
    change u.val ^ k = 1
    exact u.property
  have horder : Dvd.dvd (orderOf u) k := orderOf_dvd_iff_pow_eq_one.mpr hpow
  rwa [hu] at horder

theorem primitive_return_nonzero_all_primes (p a k h : Nat) [NeZero p]
    (hp : Nat.Prime p) (hpk : Not (Dvd.dvd p k))
    (hh : Nat.Coprime h (p ^ (a + 2))) :
    Not (returnTransform (p ^ (a + 2)) k h = 0) := by
  classical
  intro hz
  have hroot := (standard_character_root (p ^ (a + 2))).pow_of_coprime h hh
  have hsum : Finset.univ.sum (fun u : powerKernel (p ^ (a + 2)) k =>
      (ZMod.stdAddChar (1 : ZMod (p ^ (a + 2))) ^ h) ^
        (u.val : ZMod (p ^ (a + 2))).val) = 0 := by
    simpa only [returnTransform, standard_character_nat_mul, pow_mul] using hz
  have hd := prime_dvd_card_of_root_sum_zero p (a + 1) hp _ hroot
    (fun u : powerKernel (p ^ (a + 2)) k =>
      (u.val : ZMod (p ^ (a + 2))).val) hsum
  exact hpk (kernel_prime_divisor_forces_power (p ^ (a + 2)) k p hp hd)

theorem primitive_centered_nonzero_all_primes (p a k h : Nat) [NeZero p]
    (hp : Nat.Prime p) (hpk : Not (Dvd.dvd p k))
    (hh : Nat.Coprime h (p ^ (a + 2))) :
    Not (centeredTransform (p ^ (a + 2)) k h = 0) := by
  rw [centeredTransform, primitive_unit_mask p a h hp hh, mul_zero, sub_zero]
  apply mul_ne_zero
  { have hcard : 0 < Fintype.card (Units (ZMod (p ^ (a + 2)))) := Fintype.card_pos
    exact_mod_cast hcard.ne' }
  { exact primitive_return_nonzero_all_primes p a k h hp hpk hh }

/-- Exact classification for every prime, every proper prime-power
conductor, every natural exponent, and every primitive frequency. -/
theorem primitive_centered_zero_iff_all_primes (p a k h : Nat) [NeZero p]
    (hp : Nat.Prime p) (hh : Nat.Coprime h (p ^ (a + 2))) :
    centeredTransform (p ^ (a + 2)) k h = 0 <-> Dvd.dvd p k := by
  constructor
  { intro hz
    by_contra hpk
    exact primitive_centered_nonzero_all_primes p a k h hp hpk hh hz }
  { intro hpk
    rw [centeredTransform, primitive_return_zero p a k h hp hpk hh,
      primitive_unit_mask p a h hp hh, mul_zero, mul_zero, sub_self] }

end PrimeFactorOscillations.PrimePowerReturnSpectrum

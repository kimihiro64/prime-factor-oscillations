/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Data.Nat.GCD.Basic
import PrimeFactorOscillations.Helpers.PrimePowerConductorShell

/-!
# Actual root images at the prime conductor

The original exponent is preserved when the entire principal part is
removed. This is the local input for the signed radical consumer;
intermediate conductor images are still treated as actual subgroups.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations.PrimePowerReturnSpectrum

theorem root_kernel_mass_factors (p s k : Nat) [NeZero p]
    (hp : Nat.Prime p) (hp2 : Not (p = 2)) :
    And (Nat.card (powerKernel (p ^ (s + 1)) k) =
        Nat.gcd k (p ^ s) * Nat.gcd k (p - 1))
      (And (Nat.gcd (Nat.card (powerKernel (p ^ (s + 1)) k)) (p ^ s) =
          Nat.gcd k (p ^ s))
        (Nat.gcd (Nat.card (powerKernel (p ^ (s + 1)) k)) (p - 1) =
          Nat.gcd k (p - 1))) := by
  letI : IsCyclic (Units (ZMod (p ^ (s + 1)))) :=
    ZMod.isCyclic_units_of_prime_pow p hp hp2 (s + 1)
  have hr : Nat.card (powerKernel (p ^ (s + 1)) k) =
      Nat.gcd (p ^ s * (p - 1)) k := by
    rw [Nat.card_eq_fintype_card, power_kernel_card,
      Nat.totient_prime_pow_succ hp s]
  have hR : Nat.gcd (Nat.card (powerKernel (p ^ (s + 1)) k)) (p ^ s) =
      Nat.gcd k (p ^ s) := by
    rw [hr, Nat.gcd_assoc]
    exact Nat.gcd_eq_right (dvd_trans (Nat.gcd_dvd_right k (p ^ s))
      (dvd_mul_right (p ^ s) (p - 1)))
  have hD : Nat.gcd (Nat.card (powerKernel (p ^ (s + 1)) k)) (p - 1) =
      Nat.gcd k (p - 1) := by
    rw [hr, Nat.gcd_assoc]
    exact Nat.gcd_eq_right (dvd_trans (Nat.gcd_dvd_right k (p - 1))
      (dvd_mul_left (p - 1) (p ^ s)))
  have hcop : Nat.Coprime p (p - 1) :=
    (Nat.coprime_self_sub_right hp.one_lt.le).mpr (by simp)
  have hdiv : Dvd.dvd (Nat.card (powerKernel (p ^ (s + 1)) k))
      (p ^ s * (p - 1)) := by
    rw [hr]
    exact Nat.gcd_dvd_left _ _
  have hfactor :=
    (Nat.gcd_mul_gcd_eq_iff_dvd_mul_of_coprime (hcop.pow_left s)).mpr hdiv
  rw [hR, hD] at hfactor
  exact And.intro hfactor.symm (And.intro hR hD)

theorem prime_power_tame_image_card (p s k : Nat) [NeZero p]
    (hp : Nat.Prime p) (hp2 : Not (p = 2)) :
    Nat.card ((powerKernel (p ^ (s + 1)) k).map (conductorMap p s 0)) =
      Nat.gcd (p - 1) k := by
  have hm := root_kernel_mass_factors p s k hp hp2
  have hpos : 0 < Nat.gcd k (p ^ s) := by
    apply Nat.pos_of_ne_zero
    intro hz
    have hd := Nat.gcd_dvd_right k (p ^ s)
    rw [hz, zero_dvd_iff] at hd
    exact (pow_ne_zero s hp.ne_zero) hd
  calc
    _ = Nat.card (powerKernel (p ^ (s + 1)) k) /
        Nat.gcd (Nat.card (powerKernel (p ^ (s + 1)) k)) (p ^ s) :=
      conductor_image_card p s 0 hp hp2 _
    _ = (Nat.gcd k (p ^ s) * Nat.gcd k (p - 1)) / Nat.gcd k (p ^ s) := by
      rw [hm.right.left, hm.left]
    _ = Nat.gcd k (p - 1) := Nat.mul_div_cancel_left _ hpos
    _ = Nat.gcd (p - 1) k := Nat.gcd_comm _ _

/-- Every root at the prime conductor lifts to an actual root of the
same power at the full odd prime-power conductor. -/
theorem prime_power_tame_image (p s k : Nat) [NeZero p]
    (hp : Nat.Prime p) (hp2 : Not (p = 2)) :
    (powerKernel (p ^ (s + 1)) k).map (conductorMap p s 0) =
      powerKernel (p ^ (0 + 1)) k := by
  letI : IsCyclic (Units (ZMod (p ^ (0 + 1)))) :=
    ZMod.isCyclic_units_of_prime_pow p hp hp2 (0 + 1)
  apply IsCyclic.subgroup_eq_iff_card_eq.mpr
  rw [prime_power_tame_image_card p s k hp hp2,
    Nat.card_eq_fintype_card, power_kernel_card,
    Nat.totient_prime_pow_succ hp 0, pow_zero, one_mul]

end PrimeFactorOscillations.PrimePowerReturnSpectrum

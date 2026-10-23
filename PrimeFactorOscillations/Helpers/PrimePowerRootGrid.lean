/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.CompensatedConductorReduction

/-!
# Every frequency on the actual primary root grid survives

The cyclotomic weight obstruction uses the primitive conductor root and
puts the frequency into the integer exponents. Thus a prime-to-p image
mass has a nonzero trace at every frequency, without a coprimality
restriction on that frequency. This supplies the root-product branch of
the full signed odd-modulus consumer.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations.PrimePowerReturnSpectrum

open scoped BigOperators
open RationalFourierOrbit

theorem subgroup_trace_nonzero_of_prime_not_dvd_card (p a h : Nat) [NeZero p]
    (hp : Nat.Prime p) (H : Subgroup (Units (ZMod (p ^ (a + 1)))))
    (hd : Not (Dvd.dvd p (Nat.card H))) :
    Not (subgroupTrace (p ^ (a + 1)) H h = 0) := by
  classical
  letI : Fintype H := Fintype.ofFinite H
  intro hz
  have hsum : Finset.univ.sum (fun u : H =>
      ZMod.stdAddChar (1 : ZMod (p ^ (a + 1))) ^
        (h * (u.val : ZMod (p ^ (a + 1))).val)) = 0 := by
    simpa only [subgroupTrace, standard_character_nat_mul] using hz
  have hmass := prime_dvd_card_of_root_sum_zero p a hp _
    (standard_character_root (p ^ (a + 1)))
    (fun u : H => h * (u.val : ZMod (p ^ (a + 1))).val) hsum
  exact hd (by simpa only [Nat.card_eq_fintype_card] using hmass)

theorem root_trace_nonzero_on_primary_grid (p t b k h : Nat) [NeZero p]
    (hp : Nat.Prime p) (hp2 : Not (p = 2))
    (ht : Nat.gcd k (p ^ (t + b)) = p ^ t) :
    Not (returnTransform (p ^ (t + b + 1)) k (p ^ t * h) = 0) := by
  let H := powerKernel (p ^ (t + b + 1)) k
  let J := H.map (conductorMap p t b)
  let d := Nat.gcd k (p - 1)
  have hr : Nat.card H = p ^ t * d := by
    change Nat.card (powerKernel (p ^ (t + b + 1)) k) = _
    rw [(root_kernel_mass_factors p (t + b) k hp hp2).left, ht]
  have hgcd : Nat.gcd (Nat.card H) (p ^ t) = p ^ t := by
    rw [hr]
    exact Nat.gcd_eq_right (dvd_mul_right (p ^ t) d)
  have hJ : Nat.card J = d := by
    change Nat.card (H.map (conductorMap p t b)) = d
    rw [conductor_image_card p t b hp hp2 H, hgcd, hr]
    exact Nat.mul_div_cancel_left d (pow_pos hp.pos t)
  have hnot : Not (Dvd.dvd p (Nat.card J)) := by
    rw [hJ]
    intro hpd
    have hdiv := dvd_trans hpd (Nat.gcd_dvd_right k (p - 1))
    have hpos : 0 < p - 1 := by have htwo := hp.two_le; omega
    have hle := Nat.le_of_dvd hpos hdiv
    omega
  change Not (subgroupTrace (p ^ (t + b + 1)) H (p ^ t * h) = 0)
  rw [subgroup_conductor_reduction p t b h hp hp2 H, hgcd]
  apply mul_ne_zero
  { exact_mod_cast (pow_ne_zero t hp.ne_zero) }
  { exact subgroup_trace_nonzero_of_prime_not_dvd_card p b h hp J hnot }

/-- The entire primary grid survives, including zero frequency. -/
theorem root_trace_nonzero_of_primary_clock_dvd (p s k h : Nat) [NeZero p]
    (hp : Nat.Prime p) (hp2 : Not (p = 2))
    (hdiv : Dvd.dvd (Nat.gcd k (p ^ s)) h) :
    Not (returnTransform (p ^ (s + 1)) k h = 0) := by
  choose t ht using (Nat.dvd_prime_pow hp).mp (Nat.gcd_dvd_right k (p ^ s))
  choose b hb using Nat.exists_eq_add_of_le ht.left
  subst s
  rw [ht.right] at hdiv
  choose v hv using hdiv
  rw [hv]
  exact root_trace_nonzero_on_primary_grid p t b k v hp hp2 ht.right

end PrimeFactorOscillations.PrimePowerReturnSpectrum

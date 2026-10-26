/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.CarmichaelCorrelationFloor
import PrimeFactorOscillations.Assembly.CarmichaelPacketSpectrum

/-!
# Exact native kernels for one prime return label

The scalar depends on the index of the actual shortened-period image, not
on a replacement cube subgroup. Every same-base overlap is retained.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations.CarmichaelPrimePacket

open CarmichaelCorrelation CarmichaelCorrelationLocal CarmichaelCorrelationFloor
open CarmichaelCorrelationSpectrum PrimeOrderReturnLaw

def weight (q : Nat) [NeZero q] (l : Nat.Primes) : Units (ZMod q) -> Real :=
  vacancyWeight (Monoid.exponent (Units (ZMod q))) {l}

def index (q : Nat) [NeZero q] (l : Nat.Primes) : Nat :=
  returnIndex (G := Units (ZMod q)) (Monoid.exponent (Units (ZMod q))) (l : Nat)

local instance characterDecidableEq (q : Nat) : DecidableEq (DirichletCharacter Complex q) :=
  Classical.typeDecidableEq _

private theorem singleton_divisors (q : Nat) [NeZero q] (l : Nat.Primes)
    (hDiv : Dvd.dvd (l : Nat) (Monoid.exponent (Units (ZMod q)))) :
    forall p : ({l} : Finset Nat.Primes),
      Dvd.dvd (p.val : Nat) (Monoid.exponent (Units (ZMod q))) := by
  intro p
  have hp : p.val = l := Finset.mem_singleton.mp p.property
  simpa only [hp] using hDiv

theorem index_ge_two (q : Nat) [NeZero q] (l : Nat.Primes)
    (hDiv : Dvd.dvd (l : Nat) (Monoid.exponent (Units (ZMod q)))) :
    2 <= index q l := by
  exact l.property.two_le.trans
    (divisor_le_returnIndex (G := Units (ZMod q)) (l : Nat) hDiv)

theorem vacancy_iff_not_return (q : Nat) [NeZero q] (l : Nat.Primes)
    (u : Units (ZMod q)) :
    OddReturnCharacterSupport.vacancy (Monoid.exponent (Units (ZMod q))) {l} u <->
      Not (u ^ (Monoid.exponent (Units (ZMod q)) / (l : Nat)) = 1) := by
  constructor
  . intro h
    exact h (Subtype.mk l (Finset.mem_singleton_self l))
  . intro h p
    have hp : p.val = l := Finset.mem_singleton.mp p.property
    simpa only [hp] using h

theorem projection_eq_one_iff_return (q : Nat) [NeZero q] (l : Nat.Primes)
    (u : Units (ZMod q)) :
    packetProjection (Monoid.exponent (Units (ZMod q))) {l} u = 1 <->
      u ^ (Monoid.exponent (Units (ZMod q)) / (l : Nat)) = 1 := by
  constructor
  . intro h
    have hp := congrFun h (Subtype.mk l (Finset.mem_singleton_self l))
    exact congrArg Subtype.val hp
  . intro h
    funext p
    apply Subtype.ext
    have hp : p.val = l := Finset.mem_singleton.mp p.property
    change u ^ (Monoid.exponent (Units (ZMod q)) / (p.val : Nat)) = 1
    simpa only [hp] using h

theorem weightSum_pos (q : Nat) [NeZero q] (l : Nat.Primes)
    (hDiv : Dvd.dvd (l : Nat) (Monoid.exponent (Units (ZMod q)))) :
    0 < weightSum (weight q l) :=
  canonical_vacancy_weightSum_pos {l} (singleton_divisors q l hDiv)

theorem weight_mean (q : Nat) [NeZero q] (l : Nat.Primes)
    (hDiv : Dvd.dvd (l : Nat) (Monoid.exponent (Units (ZMod q)))) :
    weightMean (weight q l) = 1 - 1 / (index q l : Real) := by
  classical
  let S : Finset Nat.Primes := {l}
  let L := Monoid.exponent (Units (ZMod q))
  have h := OddReturnCharacterSupport.vacancy_mean_eq_product L S
    (singleton_divisors q l hDiv) (fun g => Monoid.pow_exponent_eq_one g)
  have hTerm : (fun p : S => 1 - 1 / (returnIndex (G := Units (ZMod q)) L (p.val : Nat) : Real)) =
      (fun _ : S => 1 - 1 / (index q l : Real)) := by
    funext p
    have hp : p.val = l := Finset.mem_singleton.mp p.property
    rw [hp]
    rfl
  rw [hTerm, Finset.prod_const] at h
  change (Finset.univ.sum (fun g : Units (ZMod q) =>
    if OddReturnCharacterSupport.vacancy L S g then (1 : Real) else 0) /
      (Fintype.card (Units (ZMod q)) : Real)) = _
  simpa only [Finset.card_univ, Fintype.card_coe, S,
    Finset.card_singleton, pow_one] using h

theorem kernel_eq_localFactor (q : Nat) [NeZero q] (l : Nat.Primes)
    (hDiv : Dvd.dvd (l : Nat) (Monoid.exponent (Units (ZMod q))))
    (u : Units (ZMod q)) :
    kernel (weight q l) u = localFactor (index q l)
      (returnBit (Monoid.exponent (Units (ZMod q))) (l : Nat) u) := by
  classical
  let S : Finset Nat.Primes := {l}
  let L := Monoid.exponent (Units (ZMod q))
  have h := canonical_kernel_eq_product (G := Units (ZMod q)) S
    (singleton_divisors q l hDiv) u
  have hTerm : (fun p : S => localFactor (returnIndex (G := Units (ZMod q)) L (p.val : Nat))
      (returnBit L (p.val : Nat) u)) =
      (fun _ : S => localFactor (index q l) (returnBit L (l : Nat) u)) := by
    funext p
    have hp : p.val = l := Finset.mem_singleton.mp p.property
    rw [hp]
    rfl
  rw [hTerm, Finset.prod_const] at h
  simpa only [weight, Finset.card_univ, Fintype.card_coe, S,
    Finset.card_singleton, pow_one] using h

theorem kernel_closed (q : Nat) [NeZero q] (l : Nat.Primes)
    (hDiv : Dvd.dvd (l : Nat) (Monoid.exponent (Units (ZMod q))))
    (u : Units (ZMod q)) :
    kernel (weight q l) u =
      1 + ((if returnBit (Monoid.exponent (Units (ZMod q))) (l : Nat) u
        then (index q l : Real) else 0) - 1) / ((index q l : Real) - 1) ^ 2 := by
  rw [kernel_eq_localFactor q l hDiv u,
    localFactor_closed _ (index_ge_two q l hDiv)]

theorem kernel_of_return (q : Nat) [NeZero q] (l : Nat.Primes)
    (hDiv : Dvd.dvd (l : Nat) (Monoid.exponent (Units (ZMod q))))
    (u : Units (ZMod q))
    (hReturn : u ^ (Monoid.exponent (Units (ZMod q)) / (l : Nat)) = 1) :
    kernel (weight q l) u = (index q l : Real) / ((index q l : Real) - 1) := by
  have hBit : returnBit (Monoid.exponent (Units (ZMod q))) (l : Nat) u = true := by
    simp [returnBit, hReturn]
  have hd : (1 : Real) < index q l := by exact_mod_cast (by have h := index_ge_two q l hDiv; omega)
  have h1 : Not ((index q l : Real) - 1 = 0) := sub_ne_zero.mpr (ne_of_gt hd)
  rw [kernel_closed q l hDiv u, hBit]
  change 1 + ((index q l : Real) - 1) / ((index q l : Real) - 1) ^ 2 =
    (index q l : Real) / ((index q l : Real) - 1)
  field_simp [h1]
  ring

theorem kernel_of_not_return (q : Nat) [NeZero q] (l : Nat.Primes)
    (hDiv : Dvd.dvd (l : Nat) (Monoid.exponent (Units (ZMod q))))
    (u : Units (ZMod q))
    (hReturn : Not (u ^ (Monoid.exponent (Units (ZMod q)) / (l : Nat)) = 1)) :
    kernel (weight q l) u = 1 - 1 / ((index q l : Real) - 1) ^ 2 := by
  have hBit : returnBit (Monoid.exponent (Units (ZMod q))) (l : Nat) u = false := by
    simp [returnBit, hReturn]
  rw [kernel_closed q l hDiv u, hBit]
  change 1 + (0 - 1) / ((index q l : Real) - 1) ^ 2 =
    1 - 1 / ((index q l : Real) - 1) ^ 2
  ring

theorem kernel_bounds_of_index_ge_three (q : Nat) [NeZero q] (l : Nat.Primes)
    (hDiv : Dvd.dvd (l : Nat) (Monoid.exponent (Units (ZMod q))))
    (hThree : 3 <= index q l) (u : Units (ZMod q)) :
    And ((3 / 4 : Real) <= kernel (weight q l) u)
      (kernel (weight q l) u <= 3 / 2) := by
  have hLow := localFactor_prime_floor (Subtype.mk 3 (by decide)) (by decide)
    (index q l) hThree (returnBit (Monoid.exponent (Units (ZMod q))) (l : Nat) u)
  norm_num [telescopeFactor] at hLow
  have hUpper := (kernel_bounds (weight q l)
    (fun g => vacancyWeight_bounds (Monoid.exponent (Units (ZMod q))) {l} g)
    (weightSum_pos q l hDiv) u).2
  rw [weight_mean q l hDiv] at hUpper
  have hd : (3 : Real) <= index q l := by exact_mod_cast hThree
  have hInv := one_div_le_one_div_of_le (by norm_num : (0 : Real) < 3) hd
  have hMean : (2 / 3 : Real) <= 1 - 1 / (index q l : Real) := by linarith
  have hLast := one_div_le_one_div_of_le (by norm_num : (0 : Real) < 2 / 3) hMean
  norm_num at hLast
  refine And.intro ?_ (hUpper.trans (by simpa only [one_div] using hLast))
  rw [kernel_eq_localFactor q l hDiv u]
  exact hLow

theorem nonprincipal_coefficient_mass (q : Nat) [NeZero q] (l : Nat.Primes)
    (hDiv : Dvd.dvd (l : Nat) (Monoid.exponent (Units (ZMod q)))) :
    (Finset.univ.erase (1 : DirichletCharacter Complex q)).sum (coefficient (weight q l)) =
      1 / ((index q l : Real) - 1) := by
  have h := nonprincipal_coefficient_sum (weight q l) (weightSum_pos q l hDiv)
    (fun g => vacancyWeight_idempotent (Monoid.exponent (Units (ZMod q))) {l} g)
  rw [weight_mean q l hDiv] at h
  have hd : (1 : Real) < index q l := by exact_mod_cast (by have h := index_ge_two q l hDiv; omega)
  have h0 : Not ((index q l : Real) = 0) := ne_of_gt (zero_lt_one.trans hd)
  have h1 : Not ((index q l : Real) - 1 = 0) := sub_ne_zero.mpr (ne_of_gt hd)
  rw [h]
  field_simp [h0, h1]
  ring

end PrimeFactorOscillations.CarmichaelPrimePacket

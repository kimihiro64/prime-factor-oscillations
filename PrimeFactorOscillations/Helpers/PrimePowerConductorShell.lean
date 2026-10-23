/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.PrimePowerConductorReduction

/-!
# Exact nonprimitive subgroup trace shells

All subgroup images and fiber multiplicities from conductor reduction
are retained. The prime-conductor boundary is included separately in the
primitive input, so the nonprimitive consumer covers b=0 as well.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations.PrimePowerReturnSpectrum

open scoped BigOperators
open RationalFourierOrbit

theorem prime_subgroup_mass_not_dvd (p : Nat) [NeZero p] (hp : Nat.Prime p)
    (H : Subgroup (Units (ZMod p))) : Not (Dvd.dvd p (Nat.card H)) := by
  have hunit : Nat.card (Units (ZMod p)) = p - 1 := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]
    simpa only [Nat.zero_add, pow_one, pow_zero, one_mul] using
      (Nat.totient_prime_pow_succ hp 0)
  intro hd
  have hdiv := dvd_trans hd H.card_subgroup_dvd_card
  rw [hunit] at hdiv
  have hpos : 0 < p - 1 := by have htwo := hp.two_le; omega
  have hle := Nat.le_of_dvd hpos hdiv
  omega

theorem prime_subgroup_nonzero (p h : Nat) [NeZero p] (hp : Nat.Prime p)
    (H : Subgroup (Units (ZMod p))) (hh : Nat.Coprime h p) :
    Not (subgroupTrace p H h = 0) := by
  classical
  letI : Fintype H := Fintype.ofFinite H
  intro hz
  have hroot := (standard_character_root p).pow_of_coprime h hh
  have hroot' : IsPrimitiveRoot
      (ZMod.stdAddChar (1 : ZMod p) ^ h) (p ^ (0 + 1)) := by
    simpa only [Nat.zero_add, pow_one] using hroot
  have hsum : Finset.univ.sum (fun u : H =>
      (ZMod.stdAddChar (1 : ZMod p) ^ h) ^ (u.val : ZMod p).val) = 0 := by
    simpa only [subgroupTrace, standard_character_nat_mul, pow_mul] using hz
  have hd := prime_dvd_card_of_root_sum_zero p 0 hp _ hroot'
    (fun u : H => (u.val : ZMod p).val) hsum
  apply prime_subgroup_mass_not_dvd p hp H
  simpa only [Nat.card_eq_fintype_card] using hd

theorem primitive_subgroup_zero_iff_all_conductors (p b h : Nat) [NeZero p]
    (hp : Nat.Prime p) (hp2 : Not (p = 2))
    (H : Subgroup (Units (ZMod (p ^ (b + 1)))))
    (hh : Nat.Coprime h (p ^ (b + 1))) :
    subgroupTrace (p ^ (b + 1)) H h = 0 <-> Dvd.dvd p (Nat.card H) := by
  revert H hh
  cases b with
  | zero =>
    intro H hh
    have hbase (n : Nat) [NeZero n] (hn : n = p)
        (J : Subgroup (Units (ZMod n))) (ht : Nat.Coprime h n) :
        subgroupTrace n J h = 0 <-> Dvd.dvd p (Nat.card J) := by
      subst n
      exact iff_of_false (prime_subgroup_nonzero p h hp J ht)
        (prime_subgroup_mass_not_dvd p hp J)
    exact hbase (p ^ (0 + 1)) (by simp only [Nat.zero_add, pow_one]) H hh
  | succ b =>
    intro H hh
    exact primitive_subgroup_zero_iff p b h hp hp2 H hh

/-- Every nonprimitive conductor row, with its genuine image mass. -/
theorem subgroup_nonprimitive_zero_iff (p a b h : Nat) [NeZero p]
    (hp : Nat.Prime p) (hp2 : Not (p = 2))
    (H : Subgroup (Units (ZMod (p ^ (a + b + 1)))))
    (hh : Nat.Coprime h (p ^ (b + 1))) :
    subgroupTrace (p ^ (a + b + 1)) H (p ^ a * h) = 0 <->
      Dvd.dvd p (Nat.card H / Nat.gcd (Nat.card H) (p ^ a)) := by
  have hmass : Not (Nat.gcd (Nat.card H) (p ^ a) = 0) := by
    intro hz
    have hd := Nat.gcd_dvd_right (Nat.card H) (p ^ a)
    rw [hz, zero_dvd_iff] at hd
    exact (pow_ne_zero a hp.ne_zero) hd
  have hc : Not ((Nat.gcd (Nat.card H) (p ^ a) : Complex) = 0) := by
    exact_mod_cast hmass
  rw [subgroup_conductor_reduction p a b h hp hp2 H]
  simp only [mul_eq_zero, hc, false_or]
  rw [primitive_subgroup_zero_iff_all_conductors p b h hp hp2 _ hh,
    conductor_image_card p a b hp hp2 H]

theorem subgroup_trace_at_multiple (n h : Nat) [NeZero n]
    (H : Subgroup (Units (ZMod n))) :
    subgroupTrace n H (n * h) = (Nat.card H : Complex) := by
  classical
  letI : Fintype H := Fintype.ofFinite H
  simp only [subgroupTrace, Nat.cast_mul, CharP.cast_eq_zero, zero_mul,
    AddChar.map_zero_eq_one, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, mul_one, Nat.card_eq_fintype_card]

/-- The complete conductor-reduction theorem used by the paper. -/
theorem conductor_trace_and_zero_shell (p a b h : Nat) [NeZero p]
    (hp : Nat.Prime p) (hp2 : Not (p = 2))
    (H : Subgroup (Units (ZMod (p ^ (a + b + 1)))))
    (hh : Nat.Coprime h (p ^ (b + 1))) :
    And (Nat.card (conductorMap p a b).ker = p ^ a)
      (And (Nat.card (H.map (conductorMap p a b)) =
          Nat.card H / Nat.gcd (Nat.card H) (p ^ a))
        (And (subgroupTrace (p ^ (a + b + 1)) H (p ^ a * h) =
            (Nat.gcd (Nat.card H) (p ^ a) : Complex) *
              subgroupTrace (p ^ (b + 1)) (H.map (conductorMap p a b)) h)
          (And (subgroupTrace (p ^ (a + b + 1)) H (p ^ a * h) = 0 <->
              Dvd.dvd p (Nat.card H / Nat.gcd (Nat.card H) (p ^ a)))
            (forall t : Nat, subgroupTrace (p ^ (a + b + 1)) H
              (p ^ (a + b + 1) * t) = (Nat.card H : Complex))))) := by
  exact And.intro (conductor_kernel_card p a b hp)
    (And.intro (conductor_image_card p a b hp hp2 H)
      (And.intro (subgroup_conductor_reduction p a b h hp hp2 H)
        (And.intro (subgroup_nonprimitive_zero_iff p a b h hp hp2 H hh)
          (fun t => subgroup_trace_at_multiple (p ^ (a + b + 1)) t H))))

end PrimeFactorOscillations.PrimePowerReturnSpectrum

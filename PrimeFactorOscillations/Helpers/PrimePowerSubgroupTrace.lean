/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.PrimePowerReturnTrace

/-!
# Complete primitive traces of multiplicative subgroups

The full odd-modulus inverse theorem needs images of power kernels under
conductor reduction. Such images are subgroups, but need not be kernels
of one common renamed power. This module retains their actual membership.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations.PrimePowerReturnSpectrum

open scoped BigOperators
open RationalFourierOrbit

def subgroupTrace (n : Nat) [NeZero n] (H : Subgroup (Units (ZMod n)))
    (h : Nat) : Complex :=
  letI : Fintype H := Fintype.ofFinite H
  Finset.univ.sum (fun u : H =>
    ZMod.stdAddChar ((h : ZMod n) * (u.val : ZMod n)))

theorem prime_kernel_card (p a : Nat) [NeZero p] (hp : Nat.Prime p)
    (hp2 : Not (p = 2)) :
    Nat.card (powerKernel (p ^ (a + 2)) p) = p := by
  letI : IsCyclic (Units (ZMod (p ^ (a + 2)))) :=
    ZMod.isCyclic_units_of_prime_pow p hp hp2 (a + 2)
  rw [Nat.card_eq_fintype_card, power_kernel_card,
    Nat.totient_prime_pow_succ hp (a + 1)]
  apply Nat.gcd_eq_right
  refine Dvd.intro (p ^ a * (p - 1)) ?_
  rw [pow_succ]
  ring

theorem prime_kernel_le_of_card_dvd (p a : Nat) [NeZero p]
    (hp : Nat.Prime p) (hp2 : Not (p = 2))
    (H : Subgroup (Units (ZMod (p ^ (a + 2)))))
    (hd : Dvd.dvd p (Nat.card H)) :
    powerKernel (p ^ (a + 2)) p <= H := by
  letI : IsCyclic (Units (ZMod (p ^ (a + 2)))) :=
    ZMod.isCyclic_units_of_prime_pow p hp hp2 (a + 2)
  apply IsCyclic.subgroup_le_iff_card_dvd.mpr
  rwa [prime_kernel_card p a hp hp2]

theorem primitive_subgroup_nonzero (p a h : Nat) [NeZero p]
    (hp : Nat.Prime p) (H : Subgroup (Units (ZMod (p ^ (a + 1)))))
    (hd : Not (Dvd.dvd p (Nat.card H)))
    (hh : Nat.Coprime h (p ^ (a + 1))) :
    Not (subgroupTrace (p ^ (a + 1)) H h = 0) := by
  classical
  letI : Fintype H := Fintype.ofFinite H
  intro hz
  have hroot := (standard_character_root (p ^ (a + 1))).pow_of_coprime h hh
  have hsum : Finset.univ.sum (fun u : H =>
      (ZMod.stdAddChar (1 : ZMod (p ^ (a + 1))) ^ h) ^
        (u.val : ZMod (p ^ (a + 1))).val) = 0 := by
    simpa only [subgroupTrace, standard_character_nat_mul, pow_mul] using hz
  have hmass := prime_dvd_card_of_root_sum_zero p a hp _ hroot
    (fun u : H => (u.val : ZMod (p ^ (a + 1))).val) hsum
  exact hd (by simpa only [Nat.card_eq_fintype_card] using hmass)

theorem primitive_subgroup_zero (p a h : Nat) [NeZero p]
    (hp : Nat.Prime p) (hp2 : Not (p = 2))
    (H : Subgroup (Units (ZMod (p ^ (a + 2)))))
    (hd : Dvd.dvd p (Nat.card H))
    (hh : Nat.Coprime h (p ^ (a + 2))) :
    subgroupTrace (p ^ (a + 2)) H h = 0 := by
  classical
  letI : Fintype H := Fintype.ofFinite H
  have hle := prime_kernel_le_of_card_dvd p a hp hp2 H hd
  let ell (j : Fin p) : H := Subtype.mk
    (lastLayerReturn p a p (dvd_refl p) j).val
    (hle (lastLayerReturn p a p (dvd_refl p) j).property)
  have hval (j : Fin p) : (ell j).val =
      (lastLayerReturn p a p (dvd_refl p) j).val := rfl
  have hperm (j : Fin p) : Finset.univ.sum
      (fun u : H => ZMod.stdAddChar ((h : ZMod (p ^ (a + 2))) *
        ((u * ell j).val : ZMod (p ^ (a + 2))))) =
      subgroupTrace (p ^ (a + 2)) H h :=
    _root_.Equiv.sum_comp (Equiv.mulRight (ell j))
      (fun u : H => ZMod.stdAddChar ((h : ZMod (p ^ (a + 2))) *
        (u.val : ZMod (p ^ (a + 2)))))
  have hsum : Finset.univ.sum
      (fun _ : Fin p => subgroupTrace (p ^ (a + 2)) H h) = 0 := by
    calc
      _ = Finset.univ.sum (fun j : Fin p => Finset.univ.sum
          (fun u : H => ZMod.stdAddChar ((h : ZMod (p ^ (a + 2))) *
            ((u * ell j).val : ZMod (p ^ (a + 2)))))) := by
        apply Finset.sum_congr rfl
        intro j _
        exact (hperm j).symm
      _ = Finset.univ.sum (fun u : H => Finset.univ.sum
          (fun j : Fin p => ZMod.stdAddChar ((h : ZMod (p ^ (a + 2))) *
            ((u * ell j).val : ZMod (p ^ (a + 2)))))) := Finset.sum_comm
      _ = 0 := by
        apply Finset.sum_eq_zero
        intro u _
        simpa only [Subgroup.coe_mul, Units.val_mul, hval,
          last_layer_return_value] using (last_layer_phase_sum p a h hp hh u.val)
  have hm : (p : Complex) * subgroupTrace (p ^ (a + 2)) H h = 0 := by
    simpa [nsmul_eq_mul] using hsum
  exact (mul_eq_zero.mp hm).resolve_left (by exact_mod_cast hp.ne_zero)

/-- Exact zero criterion for every subgroup at an odd proper prime power. -/
theorem primitive_subgroup_zero_iff (p a h : Nat) [NeZero p]
    (hp : Nat.Prime p) (hp2 : Not (p = 2))
    (H : Subgroup (Units (ZMod (p ^ (a + 2)))))
    (hh : Nat.Coprime h (p ^ (a + 2))) :
    subgroupTrace (p ^ (a + 2)) H h = 0 <-> Dvd.dvd p (Nat.card H) := by
  constructor
  { intro hz
    by_contra hd
    exact primitive_subgroup_nonzero p (a + 1) h hp H hd hh hz }
  { intro hd
    exact primitive_subgroup_zero p a h hp hp2 H hd hh }

end PrimeFactorOscillations.PrimePowerReturnSpectrum

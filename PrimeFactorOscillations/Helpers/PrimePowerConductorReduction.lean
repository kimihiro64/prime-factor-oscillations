/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.CyclicConductorReduction

/-!
# Actual prime-power conductor reduction

The map is the genuine reduction of modular units. Its image is retained
as a subgroup, with exact kernel mass and all complex Fourier phases.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations.PrimePowerReturnSpectrum

open scoped BigOperators
open CyclicConductorReduction

theorem standard_character_nat_cast (N : Nat) [NeZero N] (j : Nat) :
    ZMod.stdAddChar (j : ZMod N) =
      Complex.exp (2 * (Real.pi : Complex) * Complex.I * j / N) := by
  simpa only [Int.cast_natCast] using (ZMod.stdAddChar_coe (N := N) (j : Int))

theorem standard_character_reduce (N n m : Nat) [NeZero N] [NeZero n]
    [NeZero m] (hd : Dvd.dvd n N) (hnm : N = m * n) (x : ZMod N) :
    ZMod.stdAddChar ((m : ZMod N) * x) =
      ZMod.stdAddChar (ZMod.castHom hd (ZMod n) x) := by
  have hroot : ZMod.stdAddChar (m : ZMod N) =
      ZMod.stdAddChar (1 : ZMod n) := by
    have hone : ZMod.stdAddChar (1 : ZMod n) =
        Complex.exp (2 * (Real.pi : Complex) * Complex.I / n) := by
      simpa only [Nat.cast_one, mul_one] using (standard_character_nat_cast n 1)
    rw [standard_character_nat_cast N m, hone, hnm, Nat.cast_mul]
    apply congrArg Complex.exp
    rw [mul_comm (m : Complex) (n : Complex)]
    exact mul_div_mul_right _ _ (by exact_mod_cast (NeZero.ne m))
  have hcast : ZMod.castHom hd (ZMod n) x = (x.val : ZMod n) := by
    simpa only [map_natCast] using
      congrArg (ZMod.castHom hd (ZMod n)) (ZMod.natCast_zmod_val x).symm
  calc
    _ = ZMod.stdAddChar (m : ZMod N) ^ x.val := by
      have hc := AddChar.map_nsmul_eq_pow (ZMod.stdAddChar (N := N)) x.val (m : ZMod N)
      simpa only [nsmul_eq_mul, ZMod.natCast_zmod_val, mul_comm] using hc
    _ = ZMod.stdAddChar (1 : ZMod n) ^ x.val := by rw [hroot]
    _ = _ := by
      rw [hcast]
      simpa only [nsmul_eq_mul, mul_one] using
        (AddChar.map_nsmul_eq_pow (ZMod.stdAddChar (N := n)) x.val (1 : ZMod n)).symm

theorem conductor_dvd (p a b : Nat) :
    Dvd.dvd (p ^ (b + 1)) (p ^ (a + b + 1)) := by
  refine Dvd.intro (p ^ a) ?_
  rw [<- pow_add]
  congr 1
  omega

theorem conductor_product (p a b : Nat) :
    p ^ (a + b + 1) = p ^ a * p ^ (b + 1) := by
  rw [<- pow_add]
  congr 1

def conductorMap (p a b : Nat) :
    MonoidHom (Units (ZMod (p ^ (a + b + 1)))) (Units (ZMod (p ^ (b + 1)))) :=
  ZMod.unitsMap (conductor_dvd p a b)

theorem conductor_kernel_card (p a b : Nat) [NeZero p] (hp : Nat.Prime p) :
    Nat.card (conductorMap p a b).ker = p ^ a := by
  let f := conductorMap p a b
  have hf : Function.Surjective f := ZMod.unitsMap_surjective (conductor_dvd p a b)
  have hmul : Nat.card f.ker * Nat.card (Units (ZMod (p ^ (b + 1)))) =
      Nat.card (Units (ZMod (p ^ (a + b + 1)))) := by
    calc
      _ = Nat.card f.ker * Nat.card f.range := by
        rw [f.range_eq_top.mpr hf, Subgroup.card_top]
      _ = Nat.card f.ker * f.ker.index := by rw [Subgroup.index_ker]
      _ = _ := f.ker.card_mul_index
  have hpos : 0 < Nat.card (Units (ZMod (p ^ (b + 1)))) := Nat.card_pos
  apply Nat.eq_of_mul_eq_mul_right hpos
  change Nat.card f.ker * Nat.card (Units (ZMod (p ^ (b + 1)))) = _
  rw [hmul]
  simp only [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]
  rw [Nat.totient_prime_pow_succ hp (a + b), Nat.totient_prime_pow_succ hp b, pow_add]
  ring

theorem conductor_image_card (p a b : Nat) [NeZero p] (hp : Nat.Prime p)
    (hp2 : Not (p = 2)) (H : Subgroup (Units (ZMod (p ^ (a + b + 1))))) :
    Nat.card (H.map (conductorMap p a b)) =
      Nat.card H / Nat.gcd (Nat.card H) (p ^ a) := by
  letI : IsCyclic (Units (ZMod (p ^ (a + b + 1)))) :=
    ZMod.isCyclic_units_of_prime_pow p hp hp2 (a + b + 1)
  rw [cyclic_image_card, conductor_kernel_card p a b hp]

theorem subgroup_conductor_reduction (p a b h : Nat) [NeZero p]
    (hp : Nat.Prime p) (hp2 : Not (p = 2))
    (H : Subgroup (Units (ZMod (p ^ (a + b + 1))))) :
    subgroupTrace (p ^ (a + b + 1)) H (p ^ a * h) =
      (Nat.gcd (Nat.card H) (p ^ a) : Complex) *
        subgroupTrace (p ^ (b + 1)) (H.map (conductorMap p a b)) h := by
  classical
  letI : IsCyclic (Units (ZMod (p ^ (a + b + 1)))) :=
    ZMod.isCyclic_units_of_prime_pow p hp hp2 (a + b + 1)
  letI : Fintype H := Fintype.ofFinite H
  letI : Fintype (H.map (conductorMap p a b)) := Fintype.ofFinite _
  have hs := cyclic_subgroup_sum_pushforward H (conductorMap p a b)
    (fun v : Units (ZMod (p ^ (b + 1))) =>
      ZMod.stdAddChar ((h : ZMod (p ^ (b + 1))) * (v : ZMod (p ^ (b + 1)))))
  rw [conductor_kernel_card p a b hp] at hs
  change Finset.univ.sum (fun u : H => ZMod.stdAddChar
      (((p ^ a * h : Nat) : ZMod (p ^ (a + b + 1))) *
        (u.val : ZMod (p ^ (a + b + 1))))) = _
  dsimp only [subgroupTrace]
  rw [<- hs]
  apply Finset.sum_congr rfl
  intro u _
  change ZMod.stdAddChar (((p ^ a * h : Nat) : ZMod (p ^ (a + b + 1))) *
      (u.val : ZMod (p ^ (a + b + 1)))) =
    ZMod.stdAddChar ((h : ZMod (p ^ (b + 1))) *
      ZMod.castHom (conductor_dvd p a b) (ZMod (p ^ (b + 1)))
        (u.val : ZMod (p ^ (a + b + 1))))
  have hc := standard_character_reduce (p ^ (a + b + 1)) (p ^ (b + 1)) (p ^ a)
    (conductor_dvd p a b) (conductor_product p a b)
    ((h : ZMod (p ^ (a + b + 1))) * (u.val : ZMod (p ^ (a + b + 1))))
  simpa only [Nat.cast_mul, mul_assoc, map_mul, map_natCast] using hc

end PrimeFactorOscillations.PrimePowerReturnSpectrum

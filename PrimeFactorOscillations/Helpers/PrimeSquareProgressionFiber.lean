/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.PrimePowerConductorReduction

/-!
# Actual additive progressions in a prime-square unit fiber

The p positions n + j*p*t enumerate the complete unit fiber modulo p squared
when n and t are coprime to p. No primality of the positions is assumed.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations.PrimeSquareProgressionFiber

open PrimePowerReturnSpectrum

local instance primeLabelNeZero (l : Nat.Primes) : NeZero (l : Nat) :=
  NeZero.mk l.property.ne_zero

theorem position_coprime (l : Nat.Primes) (n t j : Nat)
    (hn : Nat.Coprime n (l : Nat)) :
    Nat.Coprime (n + j * (l : Nat) * t) (l : Nat) := by
  apply Nat.Coprime.symm
  apply (l.property.coprime_iff_not_dvd).mpr
  intro hDiv
  have hInc : Dvd.dvd (l : Nat) (j * (l : Nat) * t) :=
    Exists.intro (j * t) (by ring)
  have hN : Dvd.dvd (l : Nat) n := (Nat.dvd_add_iff_left hInc).mpr hDiv
  exact ((l.property.coprime_iff_not_dvd).mp hn.symm) hN

def positionUnit (l : Nat.Primes) (n t j : Nat)
    (hn : Nat.Coprime n (l : Nat)) : Units (ZMod ((l : Nat) ^ 2)) :=
  ZMod.unitOfCoprime (n + j * (l : Nat) * t) ((position_coprime l n t j hn).pow_right 2)

def baseUnit (l : Nat.Primes) (n : Nat) (hn : Nat.Coprime n (l : Nat)) :
    Units (ZMod ((l : Nat) ^ 2)) :=
  ZMod.unitOfCoprime n (hn.pow_right 2)

theorem position_reduction (l : Nat.Primes) (n t j : Nat)
    (hn : Nat.Coprime n (l : Nat)) :
    conductorMap (l : Nat) 1 0 (positionUnit l n t j hn) =
      conductorMap (l : Nat) 1 0 (baseUnit l n hn) := by
  have hPzero : ((l : Nat) : ZMod ((l : Nat) ^ 1)) = 0 := by
    have h := ZMod.natCast_self ((l : Nat) ^ 1)
    simpa only [pow_one] using h
  apply Units.ext
  change ZMod.castHom (conductor_dvd (l : Nat) 1 0) _
      ((n + j * (l : Nat) * t : Nat) : ZMod ((l : Nat) ^ 2)) =
    ZMod.castHom (conductor_dvd (l : Nat) 1 0) _ (n : ZMod ((l : Nat) ^ 2))
  rw [map_natCast, map_natCast, Nat.cast_add, Nat.cast_mul, Nat.cast_mul, hPzero]
  ring

def point (l : Nat.Primes) (n t : Nat) (hn : Nat.Coprime n (l : Nat))
    (i : Fin (l : Nat)) : (conductorMap (l : Nat) 1 0).ker :=
  Subtype.mk (positionUnit l n t i.val hn * Inv.inv (baseUnit l n hn)) (by
    change conductorMap (l : Nat) 1 0
      (positionUnit l n t i.val hn * Inv.inv (baseUnit l n hn)) = 1
    rw [map_mul, map_inv, position_reduction, mul_inv_cancel])

local instance fiberFintype (l : Nat.Primes) :
    Fintype (conductorMap (l : Nat) 1 0).ker := Fintype.ofFinite _

theorem point_injective (l : Nat.Primes) (n t : Nat)
    (hn : Nat.Coprime n (l : Nat)) (ht : Nat.Coprime t (l : Nat)) :
    Function.Injective (point l n t hn) := by
  intro i j hij
  have hPoint := congrArg Subtype.val hij
  change positionUnit l n t i.val hn * Inv.inv (baseUnit l n hn) =
    positionUnit l n t j.val hn * Inv.inv (baseUnit l n hn) at hPoint
  have hUnit := mul_right_cancel hPoint
  have hCast := congrArg Units.val hUnit
  change ((n + i.val * (l : Nat) * t : Nat) : ZMod ((l : Nat) ^ 2)) =
    ((n + j.val * (l : Nat) * t : Nat) : ZMod ((l : Nat) ^ 2)) at hCast
  simp only [Nat.cast_add, Nat.cast_mul] at hCast
  have hProd := add_left_cancel hCast
  let ut : Units (ZMod ((l : Nat) ^ 2)) := ZMod.unitOfCoprime t (ht.pow_right 2)
  have hInv : (t : ZMod ((l : Nat) ^ 2)) * Units.val (Inv.inv ut) = 1 := by
    exact congrArg Units.val (mul_inv_cancel ut)
  have hz := congrArg
    (fun z : ZMod ((l : Nat) ^ 2) => z * Units.val (Inv.inv ut)) hProd
  simp only [mul_assoc, hInv, mul_one] at hz
  have hzNat : ((i.val * (l : Nat) : Nat) : ZMod ((l : Nat) ^ 2)) =
      ((j.val * (l : Nat) : Nat) : ZMod ((l : Nat) ^ 2)) := by
    simpa only [Nat.cast_mul] using hz
  have hi : i.val * (l : Nat) < (l : Nat) ^ 2 := by
    calc
      i.val * (l : Nat) < (l : Nat) * (l : Nat) :=
        Nat.mul_lt_mul_of_pos_right i.isLt l.property.pos
      _ = (l : Nat) ^ 2 := (pow_two (l : Nat)).symm
  have hj : j.val * (l : Nat) < (l : Nat) ^ 2 := by
    calc
      j.val * (l : Nat) < (l : Nat) * (l : Nat) :=
        Nat.mul_lt_mul_of_pos_right j.isLt l.property.pos
      _ = (l : Nat) ^ 2 := (pow_two (l : Nat)).symm
  have hValues := congrArg ZMod.val hzNat
  rw [ZMod.val_natCast_of_lt hi, ZMod.val_natCast_of_lt hj] at hValues
  exact Fin.ext (Nat.eq_of_mul_eq_mul_right l.property.pos hValues)

theorem point_bijective (l : Nat.Primes) (n t : Nat)
    (hn : Nat.Coprime n (l : Nat)) (ht : Nat.Coprime t (l : Nat)) :
    Function.Bijective (point l n t hn) := by
  apply (Fintype.bijective_iff_injective_and_card (point l n t hn)).mpr
  refine And.intro (point_injective l n t hn ht) ?_
  rw [Fintype.card_fin, <- Nat.card_eq_fintype_card]
  have hc := conductor_kernel_card (l : Nat) 1 0 l.property
  simpa only [pow_one] using hc.symm

theorem progression_sum_eq_coset (l : Nat.Primes) (n t : Nat)
    (hn : Nat.Coprime n (l : Nat)) (ht : Nat.Coprime t (l : Nat))
    (f : Units (ZMod ((l : Nat) ^ 2)) -> Real)
    (v : Units (ZMod ((l : Nat) ^ 2))) :
    Finset.univ.sum (fun i : Fin (l : Nat) => f (v * positionUnit l n t i.val hn)) =
      Finset.univ.sum (fun h : (conductorMap (l : Nat) 1 0).ker =>
        f ((v * baseUnit l n hn) * h.val)) := by
  classical
  let e := Equiv.ofBijective (point l n t hn) (point_bijective l n t hn ht)
  have h := Equiv.sum_comp e
    (fun h : (conductorMap (l : Nat) 1 0).ker => f ((v * baseUnit l n hn) * h.val))
  calc
    _ = Finset.univ.sum (fun i : Fin (l : Nat) =>
        f ((v * baseUnit l n hn) * (e i).val)) := by
      apply Finset.sum_congr rfl
      intro i hi
      change f (v * positionUnit l n t i.val hn) =
        f ((v * baseUnit l n hn) *
          (positionUnit l n t i.val hn * Inv.inv (baseUnit l n hn)))
      congr 1
      simp only [mul_assoc, mul_comm (baseUnit l n hn), inv_mul_cancel, mul_one]
    _ = _ := h

end PrimeFactorOscillations.PrimeSquareProgressionFiber

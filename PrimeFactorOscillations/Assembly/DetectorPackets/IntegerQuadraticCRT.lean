/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Assembly.DetectorPackets.IntegerQuadraticGauss

/-!
# IntegerQuadraticCRT

Maintained extraction of completed detector/packet proof components.
All original theorem hypotheses and retained proof bodies are preserved.
This module alone asserts no improved zero-free boundary.
-/

set_option autoImplicit false
set_option Elab.async false

/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

/-!
# CRT assembly of integer Jacobi Fourier transforms

The additive factors are restrictions through the actual CRT idempotents.
All identities retain the raw Gauss factors and zero-frequency masks.
-/


noncomputable section
open scoped BigOperators
namespace PrimeFactorOscillations.IntegerQuadraticCRT

open QuadraticCarrierPacket IntegerQuadraticSieve IntegerQuadraticCharacter

variable {m n : Nat} [NeZero m] [NeZero n]

def leftChar (h : Nat.Coprime m n) (psi : AddChar (ZMod (m * n)) Complex) :
    AddChar (ZMod m) Complex where
  toFun x := psi ((ZMod.chineseRemainder h).symm (x, 0))
  map_zero_eq_one' := by
    change psi ((ZMod.chineseRemainder h).symm 0) = 1
    simp
  map_add_eq_mul' x y := by
    have heq : (x + y, (0 : ZMod n)) = (x, 0) + (y, 0) := by
      ext <;> simp
    rw [heq, map_add, AddChar.map_add_eq_mul]

def rightChar (h : Nat.Coprime m n) (psi : AddChar (ZMod (m * n)) Complex) :
    AddChar (ZMod n) Complex where
  toFun x := psi ((ZMod.chineseRemainder h).symm (0, x))
  map_zero_eq_one' := by
    change psi ((ZMod.chineseRemainder h).symm 0) = 1
    simp
  map_add_eq_mul' x y := by
    have heq : ((0 : ZMod m), x + y) = (0, x) + (0, y) := by
      ext <;> simp
    rw [heq, map_add, AddChar.map_add_eq_mul]

theorem character_crt (hm : 1 < m) (hn : 1 < n) (h : Nat.Coprime m n)
    (x : ZMod (m * n)) :
    character (m * n) (by nlinarith) x =
      character m hm (ZMod.chineseRemainder h x).1 *
        character n hn (ZMod.chineseRemainder h x).2 := by
  choose u hu using ZMod.natCast_zmod_surjective x
  rw [<- hu]
  rw [map_natCast (ZMod.chineseRemainder h) u]
  change character (m * n) _ (u : ZMod (m * n)) =
    character m hm (u : ZMod m) * character n hn (u : ZMod n)
  rw [character_natCast, character_natCast, character_natCast]
  exact kernel_mul_right u m n (NeZero.ne m) (NeZero.ne n)

theorem additive_crt (h : Nat.Coprime m n)
    (psi : AddChar (ZMod (m * n)) Complex) (x : ZMod (m * n)) :
    psi x = leftChar h psi (ZMod.chineseRemainder h x).1 *
      rightChar h psi (ZMod.chineseRemainder h x).2 := by
  let e := ZMod.chineseRemainder h
  have hx : e.symm ((e x).1, 0) + e.symm (0, (e x).2) = x := by
    apply e.injective
    simp
  calc
    psi x = psi (e.symm ((e x).1, 0) + e.symm (0, (e x).2)) :=
      congrArg psi hx.symm
    _ = _ := psi.map_add_eq_mul _ _

theorem gauss_crt (hm : 1 < m) (hn : 1 < n) (h : Nat.Coprime m n)
    (psi : AddChar (ZMod (m * n)) Complex) :
    gaussSum (character (m * n) (by nlinarith)) psi =
      gaussSum (character m hm) (leftChar h psi) *
        gaussSum (character n hn) (rightChar h psi) := by
  let e := ZMod.chineseRemainder h
  unfold gaussSum
  calc
    _ = Finset.univ.sum (fun y : Prod (ZMod m) (ZMod n) =>
      character (m * n) (by nlinarith) (e.symm y) * psi (e.symm y)) :=
      (e.symm.toEquiv.sum_comp _).symm
    _ = Finset.univ.sum (fun y : Prod (ZMod m) (ZMod n) =>
      (character m hm y.1 * leftChar h psi y.1) *
        (character n hn y.2 * rightChar h psi y.2)) := by
      apply Finset.sum_congr rfl
      intro y hy
      rw [character_crt hm hn h, additive_crt h psi]
      simp only [e, RingEquiv.apply_symm_apply]
      ring
    _ = _ := by
      rw [Fintype.sum_prod_type, Finset.sum_mul_sum]

theorem leftChar_primitive (h : Nat.Coprime m n)
    (psi : AddChar (ZMod (m * n)) Complex) (hpsi : psi.IsPrimitive) :
    (leftChar h psi).IsPrimitive := by
  intro a ha hbad
  let e := ZMod.chineseRemainder h
  have ha0 : Not (e.symm (a, 0) = 0) := by
    intro hz
    have hz' := congrArg e hz
    have he : (a, (0 : ZMod n)) = 0 := by simpa using hz'
    exact ha (congrArg Prod.fst he)
  apply hpsi ha0
  ext x
  have hprod : e.symm (a, 0) * x = e.symm (a * (e x).1, 0) := by
    apply e.injective
    ext <;> simp
  change psi (e.symm (a, 0) * x) = 1
  rw [hprod]
  have hf := congrArg (fun f : AddChar (ZMod m) Complex => f (e x).1) hbad
  exact hf

theorem rightChar_primitive (h : Nat.Coprime m n)
    (psi : AddChar (ZMod (m * n)) Complex) (hpsi : psi.IsPrimitive) :
    (rightChar h psi).IsPrimitive := by
  intro a ha hbad
  let e := ZMod.chineseRemainder h
  have ha0 : Not (e.symm (0, a) = 0) := by
    intro hz
    have hz' := congrArg e hz
    have he : ((0 : ZMod m), a) = 0 := by simpa using hz'
    exact ha (congrArg Prod.snd he)
  apply hpsi ha0
  ext x
  have hprod : e.symm (0, a) * x = e.symm (0, a * (e x).2) := by
    apply e.injective
    ext <;> simp
  change psi (e.symm (0, a) * x) = 1
  rw [hprod]
  have hf := congrArg (fun f : AddChar (ZMod n) Complex => f (e x).2) hbad
  exact hf

theorem leftChar_shift (h : Nat.Coprime m n)
    (psi : AddChar (ZMod (m * n)) Complex) (k : ZMod (m * n)) :
    leftChar h (psi.mulShift k) =
      (leftChar h psi).mulShift (ZMod.chineseRemainder h k).1 := by
  ext x
  let e := ZMod.chineseRemainder h
  have heq : k * e.symm (x, 0) = e.symm ((e k).1 * x, 0) := by
    apply e.injective
    ext <;> simp
  change psi (k * e.symm (x, 0)) = psi (e.symm ((e k).1 * x, 0))
  rw [heq]

theorem rightChar_shift (h : Nat.Coprime m n)
    (psi : AddChar (ZMod (m * n)) Complex) (k : ZMod (m * n)) :
    rightChar h (psi.mulShift k) =
      (rightChar h psi).mulShift (ZMod.chineseRemainder h k).2 := by
  ext x
  let e := ZMod.chineseRemainder h
  have heq : k * e.symm (0, x) = e.symm (0, (e k).2 * x) := by
    apply e.injective
    ext <;> simp
  change psi (k * e.symm (0, x)) = psi (e.symm (0, (e k).2 * x))
  rw [heq]

theorem fourier_factor_mul (hm : 1 < m) (hn : 1 < n)
    (h : Nat.Coprime m n)
    (hM : forall (psi : AddChar (ZMod m) Complex) (k : ZMod m),
      gaussSum (character m hm) (psi.mulShift k) =
        character m hm k * gaussSum (character m hm) psi)
    (hN : forall (psi : AddChar (ZMod n) Complex) (k : ZMod n),
      gaussSum (character n hn) (psi.mulShift k) =
        character n hn k * gaussSum (character n hn) psi)
    (psi : AddChar (ZMod (m * n)) Complex) (k : ZMod (m * n)) :
    gaussSum (character (m * n) (by nlinarith)) (psi.mulShift k) =
      character (m * n) (by nlinarith) k *
        gaussSum (character (m * n) (by nlinarith)) psi := by
  rw [gauss_crt hm hn h, leftChar_shift, rightChar_shift,
    hM, hN, character_crt hm hn h, gauss_crt hm hn h]
  ring

theorem gauss_norm_sq_mul (hm : 1 < m) (hn : 1 < n)
    (h : Nat.Coprime m n)
    (hM : forall psi : AddChar (ZMod m) Complex, psi.IsPrimitive ->
      norm (gaussSum (character m hm) psi) ^ 2 = (m : Real))
    (hN : forall psi : AddChar (ZMod n) Complex, psi.IsPrimitive ->
      norm (gaussSum (character n hn) psi) ^ 2 = (n : Real))
    (psi : AddChar (ZMod (m * n)) Complex) (hpsi : psi.IsPrimitive) :
    norm (gaussSum (character (m * n) (by nlinarith)) psi) ^ 2 =
      ((m * n : Nat) : Real) := by
  rw [gauss_crt hm hn h, norm_mul, mul_pow,
    hM _ (leftChar_primitive h psi hpsi), hN _ (rightChar_primitive h psi hpsi)]
  exact (Nat.cast_mul m n).symm

end PrimeFactorOscillations.IntegerQuadraticCRT

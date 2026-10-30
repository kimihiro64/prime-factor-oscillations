/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import Mathlib.NumberTheory.DirichletCharacter.Basic
import PrimeFactorOscillations.Assembly.DetectorPackets.IntegerQuadraticSieve

/-!
# IntegerQuadraticCharacter

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
# The actual Jacobi kernel as a Dirichlet character

This constructs the character used in the integer quadratic sieve from the
Jacobi symbol and proves its evaluation formula, including its zero mask.
Primitivity for odd squarefree moduli is a separate arithmetic theorem.
The numerator-Jacobi character modulo 4*abs(D) is also constructed with
its complete parity and nonunit masks. For D = h*P or D = -(h*P), a CRT nonsquare
witness proves nonprincipality whenever P is an odd prime larger than h.
-/


noncomputable section
namespace PrimeFactorOscillations.IntegerQuadraticCharacter

open QuadraticCarrierPacket IntegerQuadraticSieve

theorem kernel_mod (u n : Nat) : kernel (u % n) n = kernel u n := by
  unfold kernel
  congr 1
  simpa only [Int.natCast_emod] using (jacobiSym.mod_left (u : Int) n).symm

def character (n : Nat) (hn : 1 < n) : DirichletCharacter Complex n := by
  letI : NeZero n := NeZero.mk (by omega)
  letI : Fact (1 < n) := Fact.mk hn
  exact {
    toFun := fun x => kernel x.val n
    map_one' := by simp [kernel, ZMod.val_one]
    map_mul' := by
      intro x y
      rw [ZMod.val_mul, kernel_mod, kernel_mul_left]
    map_nonunit' := by
      intro x hx
      have hcop : Not (Nat.Coprime x.val n) := by
        intro h
        apply hx
        have hunit := (ZMod.isUnit_iff_coprime x.val n).mpr h
        simpa only [ZMod.natCast_zmod_val] using hunit
      have hzero : jacobiSym (x.val : Int) n = 0 := by
        apply jacobiSym.eq_zero_iff.mpr
        refine And.intro (by omega) ?_
        simpa only [Int.gcd_natCast_natCast] using hcop
      simp only [kernel, hzero, Int.cast_zero]
  }

theorem character_apply (n : Nat) (hn : 1 < n) (x : ZMod n) :
    character n hn x = kernel x.val n := rfl

theorem character_natCast (n : Nat) (hn : 1 < n) (u : Nat) :
    character n hn (u : ZMod n) = kernel u n := by
  rw [character_apply, ZMod.val_natCast, kernel_mod]

theorem character_real (n : Nat) (hn : 1 < n) (x : ZMod n) :
    star (character n hn x) = character n hn x := by
  simp [character_apply, kernel]

theorem character_unit_square (n : Nat) (hn : 1 < n)
    (u : Nat) (hu : Nat.Coprime u n) :
    character n hn (u : ZMod n) ^ 2 = 1 := by
  rw [character_natCast, kernel_square_value u n (by omega)]
  have h : (u : Int).gcd n = 1 := by
    simpa only [Int.gcd_natCast_natCast] using hu
  simp only [h, ite_true]

theorem prime_character (p : Nat) [hp : Fact (Nat.Prime p)] :
    character p hp.out.one_lt =
      (quadraticChar (ZMod p)).ringHomComp (Int.castRingHom Complex) := by
  apply MulChar.ext'
  intro x
  rw [character_apply]
  unfold kernel
  rw [jacobiSym.legendreSym.to_jacobiSym p (x.val : Int) |>.symm]
  simp [legendreSym]

theorem prime_character_ne_one (p : Nat) (hp : Nat.Prime p)
    (hp2 : Not (p = 2)) : Not (character p hp.one_lt = 1) := by
  letI : Fact (Nat.Prime p) := Fact.mk hp
  rw [prime_character p]
  apply (MulChar.ringHomComp_ne_one_iff
    (show Function.Injective (Int.castRingHom Complex) from Int.cast_injective)).mpr
  apply quadraticChar_ne_one
  simpa only [ringChar.eq (ZMod p) p] using hp2

theorem prime_character_primitive (p : Nat) (hp : Nat.Prime p)
    (hp2 : Not (p = 2)) : (character p hp.one_lt).IsPrimitive := by
  letI : NeZero p := NeZero.mk hp.ne_zero
  change (character p hp.one_lt).conductor = p
  rcases (Nat.dvd_prime hp).mp (character p hp.one_lt).conductor_dvd_level
    with h | h
  . exact False.elim (prime_character_ne_one p hp hp2
      (DirichletCharacter.eq_one_iff_conductor_eq_one.mpr h))
  . exact h

def numeratorKernel (D : Int) (n : Nat) : Complex :=
  if Odd n then (jacobiSym D n : Complex) else 0

theorem numerator_kernel_mod (D : Int) (n : Nat) :
    numeratorKernel D (n % (4 * D.natAbs)) = numeratorKernel D n := by
  have htwo : Dvd.dvd (2 : Nat) (4 * D.natAbs) := dvd_mul_of_dvd_left (by decide : Dvd.dvd (2 : Nat) 4) _
  have hparity : Odd (n % (4 * D.natAbs)) <-> Odd n := by
    simp only [Nat.odd_iff, Nat.mod_mod_of_dvd n htwo]
  by_cases hn : Odd n
  . have hm := hparity.mpr hn
    simp only [numeratorKernel, ite_eq_left hn, ite_eq_left hm]
    exact congrArg (fun z : Int => (z : Complex)) (jacobiSym.mod_right D hn).symm
  . have hm : Not (Odd (n % (4 * D.natAbs))) := fun h => hn (hparity.mp h)
    simp only [numeratorKernel, ite_eq_right hn, ite_eq_right hm]

theorem numerator_kernel_mul (D : Int) (u v : Nat) :
    numeratorKernel D (u * v) = numeratorKernel D u * numeratorKernel D v := by
  by_cases hu : Odd u
  . by_cases hv : Odd v
    . have hm : Odd (u * v) := Nat.odd_mul.mpr (And.intro hu hv)
      have hu0 : Not (u = 0) := by have ht := Nat.odd_iff.mp hu; omega
      have hv0 : Not (v = 0) := by have ht := Nat.odd_iff.mp hv; omega
      simp only [numeratorKernel, ite_eq_left hu, ite_eq_left hv, ite_eq_left hm,
        jacobiSym.mul_right' D hu0 hv0, Int.cast_mul]
    . have hm : Not (Odd (u * v)) := fun h => hv (Nat.odd_mul.mp h).2
      simp only [numeratorKernel, ite_eq_right hm, ite_eq_right hv, mul_zero]
  . have hm : Not (Odd (u * v)) := fun h => hu (Nat.odd_mul.mp h).1
    simp only [numeratorKernel, ite_eq_right hm, ite_eq_right hu, zero_mul]

theorem numerator_kernel_zero_of_not_coprime (D : Int) (n : Nat)
    (hcop : Not (Nat.Coprime n (4 * D.natAbs))) : numeratorKernel D n = 0 := by
  by_cases hn : Odd n
  . have hn0 : Not (n = 0) := by have ht := Nat.odd_iff.mp hn; omega
    have hn4 : Nat.Coprime n 4 := by
      have ht := Nat.coprime_two_right.mpr hn
      simpa only [show (2 : Nat) ^ 2 = 4 by norm_num] using
        (Nat.coprime_pow_right_iff (by decide : 0 < (2 : Nat)) n 2).mpr ht
    have hg : Not (D.gcd (n : Int) = 1) := by
      intro hg
      have ht : Nat.Coprime D.natAbs n := by
        simpa only [Int.gcd_def, Int.natAbs_natCast] using hg
      exact hcop (Nat.coprime_mul_iff_right.mpr (And.intro hn4 ht.symm))
    have hz : jacobiSym D n = 0 := jacobiSym.eq_zero_iff.mpr (And.intro hn0 hg)
    simp only [numeratorKernel, ite_eq_left hn, hz, Int.cast_zero]
  . simp only [numeratorKernel, ite_eq_right hn]

def numeratorCharacter (D : Int) (hD : Not (D = 0)) :
    DirichletCharacter Complex (4 * D.natAbs) := by
  have hd : 0 < D.natAbs := Int.natAbs_pos.mpr hD
  letI : NeZero (4 * D.natAbs) := NeZero.mk (by omega)
  letI : Fact (1 < 4 * D.natAbs) := Fact.mk (by omega)
  exact {
    toFun := fun x => numeratorKernel D x.val
    map_one' := by simp [ZMod.val_one, numeratorKernel, jacobiSym.one_right]
    map_mul' := by
      intro x y
      rw [ZMod.val_mul, numerator_kernel_mod, numerator_kernel_mul]
    map_nonunit' := by
      intro x hx
      apply numerator_kernel_zero_of_not_coprime
      intro hcop
      apply hx
      have ht := (ZMod.isUnit_iff_coprime x.val (4 * D.natAbs)).mpr hcop
      simpa only [ZMod.natCast_zmod_val] using ht
  }

theorem numerator_character_natCast (D : Int) (hD : Not (D = 0)) (n : Nat) :
    numeratorCharacter D hD (n : ZMod (4 * D.natAbs)) = numeratorKernel D n := by
  change numeratorKernel D ((n : ZMod (4 * D.natAbs)).val) = _
  rw [ZMod.val_natCast, numerator_kernel_mod]

theorem numerator_character_odd (D : Int) (hD : Not (D = 0))
    (n : Nat) (hn : Odd n) :
    numeratorCharacter D hD (n : ZMod (4 * D.natAbs)) = (jacobiSym D n : Complex) := by
  rw [numerator_character_natCast]
  simp only [numeratorKernel, ite_eq_left hn]


theorem numerator_kernel_prime (D : Int)
    (p : Nat) [hp : Fact (Nat.Prime p)] (hp2 : Not (p = 2)) :
    numeratorKernel D p = ((quadraticChar (ZMod p)) (D : ZMod p) : Complex) := by
  simp only [numeratorKernel, ite_eq_left (hp.out.odd_of_ne_two hp2)]
  rw [<- jacobiSym.legendreSym.to_jacobiSym p D]
  simp only [legendreSym]

theorem numerator_character_prime (D : Int) (hD : Not (D = 0))
    (p : Nat) [Fact (Nat.Prime p)] (hp2 : Not (p = 2)) :
    numeratorCharacter D hD (p : ZMod (4 * D.natAbs)) =
      ((quadraticChar (ZMod p)) (D : ZMod p) : Complex) := by
  rw [numerator_character_natCast, numerator_kernel_prime D p hp2]

theorem exists_prime_factor_numerator_witness (h P : Nat)
    (hh : 0 < h) (hP : Nat.Prime P) (hP2 : 2 < P) (hhP : h < P) :
    exists u : Nat, And
      (numeratorKernel ((h : Int) * (P : Int)) u = -1)
      (numeratorKernel (-((h : Int) * (P : Int))) u = -1) := by
  have : Fact (Nat.Prime P) := Fact.mk hP
  have : NeZero P := NeZero.mk hP.ne_zero
  have hPo : Odd P := hP.odd_of_ne_two (by omega)
  have hchar : Not (ringChar (ZMod P) = 2) := by
    simpa only [ringChar.eq (ZMod P) P] using (show Not (P = 2) by omega)
  let a : ZMod P := Classical.choose (quadraticChar_exists_neg_one hchar)
  have ha : (quadraticChar (ZMod P)) a = -1 :=
    Classical.choose_spec (quadraticChar_exists_neg_one hchar)
  have hP4 : Nat.Coprime P 4 := by
    have ht := Nat.coprime_two_right.mpr hPo
    simpa only [show (2 : Nat) ^ 2 = 4 by norm_num] using
      (Nat.coprime_pow_right_iff (by decide : 0 < (2 : Nat)) P 2).mpr ht
  have hPh : Nat.Coprime P h := Nat.coprime_of_lt_prime (ne_of_gt hh) hhP hP
  have hco : Nat.Coprime (4 * h) P :=
    Nat.coprime_mul_iff_left.mpr (And.intro hP4.symm hPh.symm)
  let w := Nat.chineseRemainder hco 1 a.val
  let u : Nat := w.val
  have huMod : u % (4 * h) = 1 := by
    have ht := w.property.1
    change u % (4 * h) = 1 % (4 * h) at ht
    simpa only [Nat.mod_eq_of_lt (show 1 < 4 * h by omega)] using ht
  have hu4 : u % 4 = 1 := by
    calc
      _ = (u % (4 * h)) % 4 :=
        (Nat.mod_mod_of_dvd u (dvd_mul_right 4 h)).symm
      _ = 1 := by rw [huMod]
  have hu : Odd u := by
    apply Nat.odd_iff.mpr
    calc
      _ = (u % 4) % 2 := (Nat.mod_mod_of_dvd u (by decide : Dvd.dvd (2 : Nat) 4)).symm
      _ = 1 := by rw [hu4]
  have huCast : (u : ZMod P) = a := by
    have ht : (u : ZMod P) = (a.val : ZMod P) :=
      (ZMod.natCast_eq_natCast_iff u a.val P).mpr w.property.2
    exact ht.trans (ZMod.natCast_zmod_val a)
  have hhJacobi : jacobiSym (h : Int) u = 1 := by
    have ht := jacobiSym.mod_right' h hu
    rw [huMod, jacobiSym.one_right] at ht
    exact ht
  have hpJacobi : jacobiSym (P : Int) u = -1 := by
    rw [jacobiSym.quadratic_reciprocity_one_mod_four' hPo hu4,
      <- jacobiSym.legendreSym.to_jacobiSym P (u : Int)]
    simpa only [legendreSym, Int.cast_natCast, huCast] using ha
  have hneg : jacobiSym (-1) u = 1 := by
    have ht := jacobiSym.mod_right (-1 : Int) hu
    simpa only [Int.natAbs_neg, Int.natAbs_one, Nat.mul_one, hu4,
      jacobiSym.one_right] using ht
  have hprod : jacobiSym ((h : Int) * (P : Int)) u = -1 := by
    rw [jacobiSym.mul_left, hhJacobi, hpJacobi]
    norm_num
  have hprodneg : jacobiSym (-((h : Int) * (P : Int))) u = -1 := by
    rw [show -((h : Int) * (P : Int)) = (-1) * ((h : Int) * (P : Int)) by ring,
      jacobiSym.mul_left, hneg, hprod]
    norm_num
  refine Exists.intro u (And.intro ?_ ?_)
  . simp only [numeratorKernel, ite_eq_left hu, hprod, Int.cast_neg, Int.cast_one]
  . simp only [numeratorKernel, ite_eq_left hu, hprodneg, Int.cast_neg, Int.cast_one]

theorem character_ne_one_of_neg_one {m : Nat}
    (chi : DirichletCharacter Complex m) (x : ZMod m) (hx : chi x = -1) :
    Not (chi = 1) := by
  intro hchi
  by_cases hu : IsUnit x
  . have ht : (1 : DirichletCharacter Complex m) x = 1 := MulChar.one_apply hu
    rw [hchi, ht] at hx
    norm_num at hx
  . have ht : (1 : DirichletCharacter Complex m) x = 0 := MulChar.map_nonunit _ hu
    rw [hchi, ht] at hx
    norm_num at hx

theorem numerator_character_ne_one_at_prime_factor (h P : Nat)
    (hh : 0 < h) (hP : Nat.Prime P) (hP2 : 2 < P) (hhP : h < P)
    (D : Int) (hD : Not (D = 0))
    (hSign : Or (D = (h : Int) * (P : Int)) (D = -((h : Int) * (P : Int)))) :
    Not (numeratorCharacter D hD = 1) := by
  let u : Nat := Classical.choose (exists_prime_factor_numerator_witness h P hh hP hP2 hhP)
  have hw := Classical.choose_spec (exists_prime_factor_numerator_witness h P hh hP hP2 hhP)
  apply character_ne_one_of_neg_one (numeratorCharacter D hD) (u : ZMod (4 * D.natAbs))
  rw [numerator_character_natCast]
  cases hSign with
  | inl hs => simpa only [hs] using hw.1
  | inr hs => simpa only [hs] using hw.2

end PrimeFactorOscillations.IntegerQuadraticCharacter

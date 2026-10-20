/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Basic.Complex.Basic
import Mathlib.NumberTheory.Zsqrtd.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# GaussianEuclidean

Maintained extraction of completed detector/packet proof components.
All original theorem hypotheses and retained proof bodies are preserved.
This module alone asserts no improved zero-free boundary.
-/

set_option autoImplicit false
set_option Elab.async false

/-
Copyright (c) 2019 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/

/-!
# Gaussian Euclidean arithmetic for the actual Gaussian sieve port

ASCII adaptation of the Mathlib proof at commit
fbc1661a327737928fe9d69b74f7deaa09eecfbc. The actual ring is
Zsqrtd (-1); no Eisenstein type is substituted for it.
-/


universe u
noncomputable section
namespace PrimeFactorOscillations.GaussianArithmetic
open Zsqrtd Complex

abbrev GaussianInt : Type := Zsqrtd (-1)

namespace GaussianInt

instance instCommRing : CommRing GaussianInt := Zsqrtd.commRing

def toComplex : RingHom GaussianInt Complex :=
  Zsqrtd.lift (Subtype.mk Complex.I (by simp))

instance : Coe GaussianInt Complex := { coe := toComplex }

theorem toComplex_def (x : GaussianInt) :
    (x : Complex) = x.re+x.im*Complex.I := rfl

theorem toComplex_def2 (x : GaussianInt) :
    (x : Complex) = Complex.mk x.re x.im := by
  apply Complex.ext <;> simp [toComplex_def]

@[simp] theorem intCast_re (x : GaussianInt) :
    ((x.re : Int) : Real) = (x : Complex).re := by simp [toComplex_def]

@[simp] theorem intCast_im (x : GaussianInt) :
    ((x.im : Int) : Real) = (x : Complex).im := by simp [toComplex_def]

@[simp] theorem re_toComplex (x y : Int) :
    ((Zsqrtd.mk x y : GaussianInt) : Complex).re = x := by
  simp [toComplex_def]

@[simp] theorem im_toComplex (x y : Int) :
    ((Zsqrtd.mk x y : GaussianInt) : Complex).im = y := by
  simp [toComplex_def]

theorem toComplex_add (x y : GaussianInt) :
    ((x+y : GaussianInt) : Complex) = x+y := toComplex.map_add _ _

theorem toComplex_mul (x y : GaussianInt) :
    ((x*y : GaussianInt) : Complex) = x*y := toComplex.map_mul _ _

theorem toComplex_one : ((1 : GaussianInt) : Complex) = 1 := toComplex.map_one

theorem toComplex_zero : ((0 : GaussianInt) : Complex) = 0 := toComplex.map_zero

theorem toComplex_neg (x : GaussianInt) :
    ((-x : GaussianInt) : Complex) = -x := toComplex.map_neg _

theorem toComplex_sub (x y : GaussianInt) :
    ((x-y : GaussianInt) : Complex) = x-y := toComplex.map_sub _ _

@[simp] theorem toComplex_star (x : GaussianInt) :
    ((star x : GaussianInt) : Complex) = star (x : Complex) := by
  rw [toComplex_def2, toComplex_def2]
  apply Complex.ext
  . rfl
  . exact Int.cast_neg x.im

@[simp] theorem toComplex_inj {x y : GaussianInt} :
    (x : Complex) = y <-> x = y := by
  cases x
  cases y
  simp [toComplex_def2]

theorem toComplex_injective : Function.Injective toComplex := by
  intro x y hxy
  exact toComplex_inj.mp hxy

@[simp] theorem toComplex_eq_zero {x : GaussianInt} :
    (x : Complex) = 0 <-> x = 0 := by
  rw [<-toComplex_zero, toComplex_inj]

@[simp] theorem intCast_real_norm (x : GaussianInt) :
    (x.norm : Real) = Complex.normSq (x : Complex) := by
  rw [Zsqrtd.norm, Complex.normSq]
  simp

@[simp] theorem intCast_complex_norm (x : GaussianInt) :
    (x.norm : Complex) = (Complex.normSq (x : Complex) : Complex) := by
  cases x
  rw [Zsqrtd.norm, Complex.normSq]
  simp

theorem norm_nonneg (x : GaussianInt) : 0 <= Zsqrtd.norm x :=
  Zsqrtd.norm_nonneg (by decide) x

@[simp] theorem norm_eq_zero {x : GaussianInt} :
    Zsqrtd.norm x = 0 <-> x = 0 := by
  constructor
  . intro hx
    have hc : (Zsqrtd.norm x : Real) = 0 := by rw [hx, Int.cast_zero]
    rw [intCast_real_norm] at hc
    exact toComplex_eq_zero.mp (Complex.normSq_eq_zero.mp hc)
  . intro hx
    rw [hx]
    simp

theorem norm_pos {x : GaussianInt} :
    0 < Zsqrtd.norm x <-> Not (x = 0) := by
  rw [lt_iff_le_and_ne, Ne, eq_comm, norm_eq_zero]
  simp [norm_nonneg]

theorem abs_natCast_norm (x : GaussianInt) :
    (x.norm.natAbs : Int) = x.norm :=
  Int.natAbs_of_nonneg (norm_nonneg x)

@[simp] theorem natCast_natAbs_norm {R : Type u} [AddGroupWithOne R]
    (x : GaussianInt) : (x.norm.natAbs : R) = x.norm := by
  simp

instance instDiv : Div GaussianInt where
  div x y :=
    let n := Inv.inv (Zsqrtd.norm y : Rat)
    let c := star y
    Zsqrtd.mk (round ((x*c).re*n : Rat)) (round ((x*c).im*n : Rat))

theorem div_def (x y : GaussianInt) :
    x/y = Zsqrtd.mk (round ((x*star y).re/Zsqrtd.norm y : Rat))
      (round ((x*star y).im/Zsqrtd.norm y : Rat)) := by
  change Zsqrtd.mk _ _ = _
  simp [div_eq_mul_inv]

theorem toComplex_re_div (x y : GaussianInt) :
    ((x/y : GaussianInt) : Complex).re = round ((x : Complex)/y).re := by
  rw [div_def, <- @Rat.round_cast Real _ _ _ _]
  simp [-Rat.round_cast, mul_assoc, div_eq_mul_inv, add_mul]

theorem toComplex_im_div (x y : GaussianInt) :
    ((x/y : GaussianInt) : Complex).im = round ((x : Complex)/y).im := by
  rw [div_def, <- @Rat.round_cast Real _ _ _ _, <- @Rat.round_cast Real _ _ _ _]
  simp [-Rat.round_cast, mul_assoc, div_eq_mul_inv, add_mul]

theorem normSq_le_normSq_of_re_le_of_im_le {x y : Complex}
    (hre : abs x.re <= abs y.re) (him : abs x.im <= abs y.im) :
    Complex.normSq x <= Complex.normSq y := by
  simp only [Complex.normSq_apply]
  nlinarith [sq_le_sq.mpr hre, sq_le_sq.mpr him]

theorem normSq_div_sub_div_lt_one (x y : GaussianInt) :
    Complex.normSq ((x : Complex)/y-((x/y : GaussianInt) : Complex)) < 1 := by
  calc
    _ = Complex.normSq
      ((((x : Complex)/y).re-((x/y : GaussianInt) : Complex).re : Real)+
       ((((x : Complex)/y).im-((x/y : GaussianInt) : Complex).im : Real) : Complex)*Complex.I) := by
      congr 1
      apply Complex.ext <;> simp
    _ <= Complex.normSq ((1/2 : Complex)+(1/2)*Complex.I) := by
      have hhalf : abs (Inv.inv (2:Real)) = Inv.inv (2:Real) :=
        abs_of_nonneg (by norm_num)
      exact normSq_le_normSq_of_re_le_of_im_le
        (by rw [toComplex_re_div]; simp [Complex.normSq, hhalf]
            simpa using abs_sub_round ((x : Complex)/y).re)
        (by rw [toComplex_im_div]; simp [Complex.normSq, hhalf]
            simpa using abs_sub_round ((x : Complex)/y).im)
    _ < 1 := by norm_num [Complex.normSq]

instance instMod : Mod GaussianInt where
  mod x y := x-y*(x/y)

theorem mod_def (x y : GaussianInt) : x%y = x-y*(x/y) := rfl

theorem norm_mod_lt (x : GaussianInt) {y : GaussianInt}
    (hy : Not (y = 0)) : Zsqrtd.norm (x%y) < Zsqrtd.norm y := by
  have hyc : Not ((y : Complex) = 0) := by
    simpa only [toComplex_eq_zero] using hy
  apply (Int.cast_lt (R := Real)).mp
  calc
    (Zsqrtd.norm (x%y) : Real) =
        Complex.normSq ((x : Complex)-y*(x/y : GaussianInt)) := by simp [mod_def]
    _ = Complex.normSq (y : Complex)*
        Complex.normSq ((x : Complex)/y-(x/y : GaussianInt)) := by
      rw [<-Complex.normSq_mul]
      congr 1
      field_simp [hyc]
    _ < Complex.normSq (y : Complex)*1 :=
      mul_lt_mul_of_pos_left (normSq_div_sub_div_lt_one x y) (Complex.normSq_pos.mpr hyc)
    _ = (Zsqrtd.norm y : Real) := by simp

theorem natAbs_norm_mod_lt (x : GaussianInt) {y : GaussianInt}
    (hy : Not (y = 0)) : (x%y).norm.natAbs < y.norm.natAbs :=
  Int.ofNat_lt.mp (by simp [norm_mod_lt x hy])

theorem norm_le_norm_mul_left (x : GaussianInt) {y : GaussianInt}
    (hy : Not (y = 0)) : (Zsqrtd.norm x).natAbs <= (Zsqrtd.norm (x*y)).natAbs := by
  rw [Zsqrtd.norm_mul, Int.natAbs_mul]
  exact le_mul_of_one_le_right (Nat.zero_le _) (Int.ofNat_le.mp (by
    rw [abs_natCast_norm]
    exact Int.add_one_le_of_lt (norm_pos.mpr hy)))

instance instNontrivial : Nontrivial GaussianInt where
  exists_pair_ne := Exists.intro 0 (Exists.intro 1 (by decide))

instance instEuclideanDomain : EuclideanDomain GaussianInt :=
  { GaussianInt.instCommRing, GaussianInt.instNontrivial with
    quotient := fun x y => x/y
    remainder := fun x y => x%y
    quotient_zero := by simp [div_def]; rfl
    quotient_mul_add_remainder_eq := fun x y => by simp [mod_def]
    r := _
    r_wellFounded := (measure (fun x : GaussianInt => (Zsqrtd.norm x).natAbs)).wf
    remainder_lt := natAbs_norm_mod_lt
    mul_left_not_lt := fun a b hb0 =>
      not_lt_of_ge (norm_le_norm_mul_left a hb0) }

end GaussianInt
end PrimeFactorOscillations.GaussianArithmetic


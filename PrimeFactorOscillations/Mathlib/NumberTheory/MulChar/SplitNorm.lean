/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.NumberTheory.MulChar.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring.Basic

/-!
# Character cancellation on split norm fibres

A nontrivial multiplicative character sums to zero on each hyperbola xy = c,
including c = 0. In odd characteristic the split change of coordinates
(a,b) -> (a + i*b, a - i*b) transfers the identity to a sum-of-squares fibre.
-/

set_option autoImplicit false
set_option Elab.async false

namespace MulChar

variable {F R : Type*} [Field F] [Fintype F] [DecidableEq F] [CommRing R] [IsDomain R]

/-- Complete character cancellation on a hyperbola, including its zero fibre. -/
theorem sum_hyperbola_eq_zero (chi : MulChar F R) (hchi : Not (chi = 1))
    (c : F) :
    Finset.univ.sum (fun x : F => Finset.univ.sum (fun y : F =>
      if x * y = c then chi x else 0)) = 0 := by
  classical
  have hrow (x : F) :
      Finset.univ.sum (fun y : F => if x * y = c then chi x else 0) = chi x := by
    by_cases hx : x = 0
    next => simp [hx]
    next =>
      have heq (y : F) : (x * y = c) <-> y = c / x := by
        rw [eq_div_iff hx, mul_comm y x]
      simp [heq]
  simp_rw [hrow]
  exact sum_eq_zero_of_ne_one hchi

/-- Complete character cancellation on a split quadratic norm fibre. -/
theorem sum_split_norm_fiber_eq_zero (chi : MulChar F R)
    (hchi : Not (chi = 1)) (i c : F) (hi : i ^ 2 = -1)
    (htwo : Not ((2 : F) = 0)) :
    Finset.univ.sum (fun a : F => Finset.univ.sum (fun b : F =>
      if a ^ 2 + b ^ 2 = c then chi (a + i * b) else 0)) = 0 := by
  classical
  have hi0 : Not (i = 0) := by
    intro h
    simp [h] at hi
  let transform : Prod F F -> Prod F F := fun z => (z.1 + i * z.2, z.1 - i * z.2)
  let inverse : Prod F F -> Prod F F := fun z => ((z.1 + z.2) / 2, (z.1 - z.2) / (2 * i))
  have hleft (z : Prod F F) : inverse (transform z) = z := by
    apply Prod.ext
    all_goals dsimp [inverse, transform]; field_simp [htwo, hi0]; ring
  have hright (z : Prod F F) : transform (inverse z) = z := by
    apply Prod.ext
    all_goals dsimp [inverse, transform]; field_simp [htwo, hi0]; ring
  let e : Equiv (Prod F F) (Prod F F) := Equiv.mk transform inverse hleft hright
  have hnorm (z : Prod F F) :
      (transform z).1 * (transform z).2 = z.1 ^ 2 + z.2 ^ 2 := by
    dsimp [transform]
    calc
      _ = z.1 ^ 2 - i ^ 2 * z.2 ^ 2 := by ring
      _ = _ := by rw [hi]; ring
  have hsum :
      Finset.univ.sum (fun z : Prod F F =>
        if z.1 ^ 2 + z.2 ^ 2 = c then chi (z.1 + i * z.2) else 0) =
      Finset.univ.sum (fun z : Prod F F => if z.1 * z.2 = c then chi z.1 else 0) := by
    apply Fintype.sum_equiv e
    intro z
    dsimp [e]
    rw [hnorm]
  rw [Fintype.sum_prod_type] at hsum
  rw [hsum, Fintype.sum_prod_type]
  exact sum_hyperbola_eq_zero chi hchi c

end MulChar

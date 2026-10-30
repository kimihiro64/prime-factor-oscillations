/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.NumberTheory.JacobiSum.Basic
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Exact finite-field quadratic discriminant pair counts

The joint nonsquare-discriminant count is expressed by the actual finite
point count of a split cubic. Both zero-discriminant rows and their
intersection are retained before cancellation. The main theorem assumes
odd characteristic and distinct nonzero cubic roots. It uses no Hasse
bound and makes no integer prime-gap claim.
-/

set_option autoImplicit false
set_option Elab.async false

open scoped BigOperators

namespace FiniteField

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem quadraticChar_jacobi_self (hF : Not (ringChar F = 2)) :
    jacobiSum (quadraticChar F) (quadraticChar F) = -(quadraticChar F) (-1) := by
  simpa only [(quadraticChar_isQuadratic F).inv] using
    jacobiSum_nontrivial_inv (quadraticChar_ne_one hF)

theorem quadraticChar_sum_mul_sub (hF : Not (ringChar F = 2))
    (a b : F) (hab : Not (a = b)) :
    (Finset.univ.sum fun x : F => (quadraticChar F) ((x - a) * (x - b))) = -1 := by
  have hd : Not (b - a = 0) := sub_ne_zero.mpr (Ne.symm hab)
  let e : Equiv F F :=
    { toFun := fun x => a + (b - a) * x
      invFun := fun x => (x - a) / (b - a)
      left_inv := by
        intro x
        field_simp [hd]
        <;> ring
      right_inv := by
        intro x
        field_simp [hd]
        <;> ring }
  have hpoint (x : F) :
      (quadraticChar F) ((e x - a) * (e x - b)) =
        (quadraticChar F) (-1) *
          ((quadraticChar F) x * (quadraticChar F) (1 - x)) := by
    change (quadraticChar F)
      ((a + (b - a) * x - a) * (a + (b - a) * x - b)) = _
    have heq :
        (a + (b - a) * x - a) * (a + (b - a) * x - b) =
          (b - a) ^ 2 * (-1) * (x * (1 - x)) := by ring
    rw [heq]
    simp only [map_mul, map_pow, quadraticChar_sq_one hd, one_mul]
  calc
    (Finset.univ.sum fun x : F => (quadraticChar F) ((x - a) * (x - b))) =
        Finset.univ.sum (fun x : F => (quadraticChar F) ((e x - a) * (e x - b))) :=
      (Equiv.sum_comp e _).symm
    _ = (quadraticChar F) (-1) *
        jacobiSum (quadraticChar F) (quadraticChar F) := by
      simp_rw [hpoint]
      rw [<- Finset.mul_sum]
      rfl
    _ = -1 := by
      rw [quadraticChar_jacobi_self hF]
      have hs := quadraticChar_sq_one (F := F) (a := (-1 : F))
        (neg_ne_zero.mpr one_ne_zero)
      calc
        (quadraticChar F) (-1) * -(quadraticChar F) (-1) =
            -((quadraticChar F) (-1) ^ 2) := by ring
        _ = -1 := by rw [hs]


theorem quadraticChar_square_pushforward (hF : Not (ringChar F = 2)) (f : F -> Int) :
    (Finset.univ.sum fun b : F => f (b ^ 2)) =
      Finset.univ.sum (fun x : F => ((quadraticChar F) x + 1) * f x) := by
  classical
  have hcard (x : F) :
      ((Finset.univ.filter fun b : F => b ^ 2 = x).card : Int) =
        (quadraticChar F) x + 1 := by
    simpa using quadraticChar_card_sqrts hF x
  have hfiber (x : F) :
      ((quadraticChar F) x + 1) * f x =
        Finset.univ.sum (fun b : F => if b ^ 2 = x then f x else 0) := by
    rw [<- hcard x, <- Finset.sum_filter]
    simp only [Finset.sum_const, nsmul_eq_mul]
  calc
    (Finset.univ.sum fun b : F => f (b ^ 2)) =
        Finset.univ.sum (fun b : F =>
          Finset.univ.sum (fun x : F => if b ^ 2 = x then f x else 0)) := by simp
    _ = Finset.univ.sum (fun x : F =>
        Finset.univ.sum (fun b : F => if b ^ 2 = x then f x else 0)) := Finset.sum_comm
    _ = Finset.univ.sum (fun x : F => ((quadraticChar F) x + 1) * f x) := by
      apply Finset.sum_congr rfl
      intro x _
      exact (hfiber x).symm

theorem quadraticChar_sum_square_sub (hF : Not (ringChar F = 2))
    (a : F) (ha : Not (a = 0)) :
    (Finset.univ.sum fun b : F => (quadraticChar F) (b ^ 2 - a)) = -1 := by
  have hpair :
      (Finset.univ.sum fun x : F => (quadraticChar F) x * (quadraticChar F) (x - a)) =
        -1 := by
    simpa only [sub_zero, map_mul] using
      quadraticChar_sum_mul_sub hF (0 : F) a (Ne.symm ha)
  let e : Equiv F F :=
    { toFun := fun x => x - a
      invFun := fun x => x + a
      left_inv := by intro x; ring
      right_inv := by intro x; ring }
  have hzero :
      (Finset.univ.sum fun x : F => (quadraticChar F) (x - a)) = 0 := by
    calc
      _ = Finset.univ.sum (fun x : F => (quadraticChar F) x) :=
        Equiv.sum_comp e (quadraticChar F)
      _ = 0 := quadraticChar_sum_zero hF
  rw [quadraticChar_square_pushforward hF (fun x : F => (quadraticChar F) (x - a))]
  simp only [add_mul, one_mul, Finset.sum_add_distrib]
  rw [hpair, hzero]
  ring


def splitCubicAffineCount (a b : F) : Nat :=
  Finset.univ.sum (fun x : F =>
    (Finset.univ.filter fun y : F => y ^ 2 = x * (x - a) * (x - b)).card)

def splitCubicPointTrace (a b : F) : Int :=
  (Fintype.card F : Int) - (splitCubicAffineCount a b : Int)

theorem splitCubicPointTrace_eq (hF : Not (ringChar F = 2)) (a b : F) :
    splitCubicPointTrace a b =
      -(Finset.univ.sum fun x : F =>
        (quadraticChar F) (x * (x - a) * (x - b))) := by
  unfold splitCubicPointTrace splitCubicAffineCount
  rw [Nat.cast_sum]
  have hcard (x : F) :
      ((Finset.univ.filter fun y : F => y ^ 2 = x * (x - a) * (x - b)).card : Int) =
        (quadraticChar F) (x * (x - a) * (x - b)) + 1 := by
    simpa using quadraticChar_card_sqrts hF (x * (x - a) * (x - b))
  simp_rw [hcard]
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  ring

theorem quadraticChar_quartic_eq_trace (hF : Not (ringChar F = 2))
    (a b : F) (hab : Not (a = b)) :
    (Finset.univ.sum fun x : F =>
      (quadraticChar F) ((x ^ 2 - a) * (x ^ 2 - b))) =
        -1 - splitCubicPointTrace a b := by
  rw [quadraticChar_square_pushforward hF
    (fun x : F => (quadraticChar F) ((x - a) * (x - b)))]
  simp only [add_mul, one_mul, Finset.sum_add_distrib]
  have hprod (x : F) :
      (quadraticChar F) x * (quadraticChar F) ((x - a) * (x - b)) =
        (quadraticChar F) (x * (x - a) * (x - b)) := by
    rw [<- map_mul]
    congr 1
    ring
  simp_rw [hprod]
  rw [quadraticChar_sum_mul_sub hF a b hab, splitCubicPointTrace_eq hF]
  ring

theorem twice_nonsquare_indicator (x : F) :
    2 * (if IsSquare x then (0 : Int) else 1) =
      1 - (quadraticChar F) x - (if x = 0 then 1 else 0) := by
  classical
  by_cases hx : x = 0
  . subst x
    simp
  . by_cases hs : IsSquare x
    . have hc : (quadraticChar F) x = 1 := (quadraticChar_one_iff_isSquare hx).mpr hs
      simp [hs, hx, hc]
    . have hc : (quadraticChar F) x = -1 :=
        quadraticChar_neg_one_iff_not_isSquare.mpr hs
      simp [hs, hx, hc]

theorem four_nonsquare_pair_indicator (x y : F) :
    4 * (if Not (IsSquare x) /\ Not (IsSquare y) then (1 : Int) else 0) =
      (1 - (quadraticChar F) x) * (1 - (quadraticChar F) y) -
        (if x = 0 then 1 - (quadraticChar F) y else 0) -
        (if y = 0 then 1 - (quadraticChar F) x else 0) +
        (if x = 0 /\ y = 0 then 1 else 0) := by
  classical
  have hp :
      (if Not (IsSquare x) /\ Not (IsSquare y) then (1 : Int) else 0) =
        (if IsSquare x then 0 else 1) * (if IsSquare y then 0 else 1) := by
    by_cases hx : IsSquare x <;> by_cases hy : IsSquare y <;> simp [hx, hy]
  rw [hp]
  calc
    4 * ((if IsSquare x then (0 : Int) else 1) *
        (if IsSquare y then (0 : Int) else 1)) =
      (2 * (if IsSquare x then (0 : Int) else 1)) *
        (2 * (if IsSquare y then (0 : Int) else 1)) := by ring
    _ = (1 - (quadraticChar F) x - (if x = 0 then 1 else 0)) *
        (1 - (quadraticChar F) y - (if y = 0 then 1 else 0)) := by
      rw [twice_nonsquare_indicator, twice_nonsquare_indicator]
    _ = _ := by
      by_cases hx : x = 0 <;> by_cases hy : y = 0 <;> simp [hx, hy] <;> ring

noncomputable def nonsquarePairCount (a b : F) : Int := by
  classical
  exact Finset.univ.sum (fun x : F =>
    if Not (IsSquare (x ^ 2 - a)) /\ Not (IsSquare (x ^ 2 - b)) then 1 else 0)


theorem quadraticChar_zero_row_sum (hF : Not (ringChar F = 2)) (a b : F) :
    (Finset.univ.sum fun x : F =>
      if x ^ 2 - a = 0 then 1 - (quadraticChar F) (x ^ 2 - b) else 0) =
        ((quadraticChar F) a + 1) * (1 - (quadraticChar F) (a - b)) := by
  classical
  have hpoint (x : F) :
      (if x ^ 2 - a = 0 then 1 - (quadraticChar F) (x ^ 2 - b) else 0) =
        (if x ^ 2 = a then (1 : Int) else 0) *
          (1 - (quadraticChar F) (a - b)) := by
    by_cases hx : x ^ 2 = a
    . simp [hx]
    . simp [hx, sub_ne_zero.mpr hx]
  simp_rw [hpoint]
  rw [<- Finset.sum_mul]
  have hsum :
      (Finset.univ.sum fun x : F => if x ^ 2 = a then (1 : Int) else 0) =
        (quadraticChar F) a + 1 := by
    calc
      _ = ((Finset.univ.filter fun x : F => x ^ 2 = a).card : Int) := by
        rw [<- Finset.sum_filter]
        simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
      _ = _ := by simpa using quadraticChar_card_sqrts hF a
  rw [hsum]

theorem nonsquarePairCount_eq_trace (hF : Not (ringChar F = 2))
    (a b : F) (ha : Not (a = 0)) (hb : Not (b = 0)) (hab : Not (a = b)) :
    4 * nonsquarePairCount a b =
      (Fintype.card F : Int) + 1 - splitCubicPointTrace a b -
        (1 + (quadraticChar F) a) * (1 - (quadraticChar F) (a - b)) -
        (1 + (quadraticChar F) b) * (1 - (quadraticChar F) (b - a)) := by
  classical
  have hcross :
      (Finset.univ.sum fun x : F =>
        (quadraticChar F) (x ^ 2 - a) * (quadraticChar F) (x ^ 2 - b)) =
          -1 - splitCubicPointTrace a b := by
    simpa only [map_mul] using quadraticChar_quartic_eq_trace hF a b hab
  have hjoint :
      (Finset.univ.sum fun x : F =>
        if x ^ 2 - a = 0 /\ x ^ 2 - b = 0 then (1 : Int) else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro x _
    have hn : Not (x ^ 2 - a = 0 /\ x ^ 2 - b = 0) := by
      intro h
      exact hab ((sub_eq_zero.mp h.1).symm.trans (sub_eq_zero.mp h.2))
    simp only [hn, ite_false]
  have hpoint (x : F) :
      (1 - (quadraticChar F) (x ^ 2 - a)) *
          (1 - (quadraticChar F) (x ^ 2 - b)) =
        1 - (quadraticChar F) (x ^ 2 - a) - (quadraticChar F) (x ^ 2 - b) +
          (quadraticChar F) (x ^ 2 - a) * (quadraticChar F) (x ^ 2 - b) := by ring
  calc
    4 * nonsquarePairCount a b =
        Finset.univ.sum (fun x : F =>
          (1 - (quadraticChar F) (x ^ 2 - a)) *
              (1 - (quadraticChar F) (x ^ 2 - b)) -
            (if x ^ 2 - a = 0 then 1 - (quadraticChar F) (x ^ 2 - b) else 0) -
            (if x ^ 2 - b = 0 then 1 - (quadraticChar F) (x ^ 2 - a) else 0) +
            (if x ^ 2 - a = 0 /\ x ^ 2 - b = 0 then 1 else 0)) := by
      unfold nonsquarePairCount
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      exact four_nonsquare_pair_indicator (x ^ 2 - a) (x ^ 2 - b)
    _ = _ := by
      simp_rw [hpoint]
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
      rw [hjoint, hcross, quadraticChar_sum_square_sub hF a ha,
        quadraticChar_sum_square_sub hF b hb,
        quadraticChar_zero_row_sum hF a b, quadraticChar_zero_row_sum hF b a]
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
      ring

end FiniteField

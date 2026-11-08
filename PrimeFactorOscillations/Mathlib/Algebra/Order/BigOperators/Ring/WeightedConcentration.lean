/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith

/-! # Concentration and unit-weight recovery from a quadratic deficit -/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 5000000

noncomputable section
namespace Finset

/-- A small square deficit forces a largest positive coordinate to have unit
natural weight and controls the weighted mass outside that coordinate. -/
theorem exists_unit_weight_of_small_square_defect {Iota : Type*} (S : Finset Iota)
    (a : Iota -> Nat) (x : Iota -> Real)
    (hx : forall i, Membership.mem S i -> 0 <= x i)
    (hX : 0 < Finset.sum S (fun i => (a i : Real) * x i))
    (hSmall : (Finset.sum S (fun i => (a i : Real) * x i)) ^ 2 -
        Finset.sum S (fun i => (a i : Real) * (x i) ^ 2) <
      (Finset.sum S (fun i => (a i : Real) * x i)) ^ 2 / 2) :
    exists j, And (Membership.mem S j) (And (a j = 1) (And (0 < x j)
      (And (forall i, Membership.mem S i -> 0 < a i -> x i <= x j)
        (And (0 <= Finset.sum S (fun i => (a i : Real) * x i) - x j)
          ((Finset.sum S (fun i => (a i : Real) * x i)) *
              (Finset.sum S (fun i => (a i : Real) * x i) - x j) <=
            (Finset.sum S (fun i => (a i : Real) * x i)) ^ 2 -
              Finset.sum S (fun i => (a i : Real) * (x i) ^ 2)))))) := by
  classical
  let w := fun i => (a i : Real)
  let X := Finset.sum S (fun i => w i * x i)
  let U := Finset.sum S (fun i => w i * (x i) ^ 2)
  have hw : forall i, 0 <= w i := fun i => Nat.cast_nonneg (a i)
  have hTerms : forall i, Membership.mem S i -> 0 <= w i * x i :=
    fun i hi => mul_nonneg (hw i) (hx i hi)
  have hPositive := (Finset.sum_pos_iff_of_nonneg hTerms).mp hX
  choose k hk hkPos using hPositive
  have hkA : 0 < a k := by
    by_contra hn
    have hz : a k = 0 := by omega
    simp [w, hz] at hkPos
  have hkX : 0 < x k := by
    by_contra hn
    have hm := mul_nonpos_of_nonneg_of_nonpos (hw k) (le_of_not_gt hn)
    linarith only [hkPos, hm]
  let T := S.filter (fun i => 0 < a i)
  have hT : T.Nonempty :=
    Exists.intro k (Finset.mem_filter.mpr (And.intro hk hkA))
  choose j hj hMax using Finset.exists_max_image T x hT
  have hjS : Membership.mem S j := (Finset.mem_filter.mp hj).1
  have hjA : 0 < a j := (Finset.mem_filter.mp hj).2
  have hMaxAll : forall i, Membership.mem S i -> 0 < a i -> x i <= x j := by
    intro i hi hai
    exact hMax i (Finset.mem_filter.mpr (And.intro hi hai))
  have hjX : 0 < x j := lt_of_lt_of_le hkX (hMaxAll k hk hkA)
  have hMass : w j * x j <= X := Finset.single_le_sum hTerms hjS
  have hEach : forall i, Membership.mem S i -> w i * (x i) ^ 2 <= x j * (w i * x i) := by
    intro i hi
    by_cases hz : a i = 0
    case pos => simp [w, hz]
    case neg =>
      have hp : 0 < a i := Nat.pos_of_ne_zero hz
      have hm := mul_nonneg (mul_nonneg (hw i) (hx i hi))
        (sub_nonneg.mpr (hMaxAll i hi hp))
      nlinarith only [hm]
  have hU : U <= x j * X := by
    have hs := Finset.sum_le_sum hEach
    simpa only [<- Finset.mul_sum, X, U] using hs
  have hjOne : a j = 1 := by
    by_contra hn
    have hTwo : 2 <= a j := by omega
    have hTwoR : (2 : Real) <= (a j : Real) := by exact_mod_cast hTwo
    have hTwoW : 2 <= w j := hTwoR
    have hm := mul_nonneg (sub_nonneg.mpr hTwoW) hjX.le
    have hTX : 2 * x j <= X := by linarith only [hMass, hm]
    have hProduct := mul_nonneg (sub_nonneg.mpr hTX) hX.le
    change X ^ 2 - U < X ^ 2 / 2 at hSmall
    nlinarith only [hU, hProduct, hSmall]
  have hWj : w j = 1 := by simp only [w, hjOne, Nat.cast_one]
  have hR : 0 <= X - x j := by rw [hWj, one_mul] at hMass; linarith only [hMass]
  have hDefect : X * (X - x j) <= X ^ 2 - U := by
    nlinarith only [hU]
  exact Exists.intro j (And.intro hjS (And.intro hjOne (And.intro hjX
    (And.intro hMaxAll (And.intro hR hDefect)))))

end Finset

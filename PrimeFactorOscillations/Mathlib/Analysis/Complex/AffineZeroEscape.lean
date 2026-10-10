/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# Escape under an expanding affine map

A subset of the real line bounded above cannot be closed under an affine dilation
of factor greater than one at a point above its center. Applied to real parts of
complex zeros, this gives a zero-exclusion principle from a separately supplied
transport identity and upper bound. No analytic transport identity is assumed to
hold for any particular L-function here.
-/

set_option autoImplicit false
set_option Elab.async false

namespace Function

/-- A bounded set cannot carry a point strictly above the center of an outward dilation. -/
theorem bounded_affine_dilation_le_center
    (P : Real -> Prop) (center upper factor : Real) (hfactor : 1 < factor)
    (hBound : forall x, P x -> x <= upper)
    (hStep : forall x, P x -> center < x -> P (center + factor * (x - center)))
    (x : Real) (hx : P x) : x <= center := by
  by_cases hle : x <= center
  . exact hle
  . exfalso
    have hcx : center < x := lt_of_not_ge hle
    let delta : Real := (factor - 1) * (x - center)
    have hdelta : 0 < delta := mul_pos (sub_pos.mpr hfactor) (sub_pos.mpr hcx)
    let a : Nat -> Real := Nat.rec x (fun _ y => center + factor * (y - center))
    have hSucc (n : Nat) : a (n + 1) = center + factor * (a n - center) := rfl
    have hAll : forall n : Nat, P (a n) /\ x + (n : Real) * delta <= a n := by
      intro n
      induction n with
      | zero =>
          simpa [a] using And.intro hx (le_refl x)
      | succ n ih =>
          have hnonneg : 0 <= (n : Real) * delta :=
            mul_nonneg (Nat.cast_nonneg n) hdelta.le
          have hxa : x <= a n := by linarith [ih.2]
          have hca : center < a n := lt_of_lt_of_le hcx hxa
          have hinc : delta <= (factor - 1) * (a n - center) :=
            mul_le_mul_of_nonneg_left (sub_le_sub_right hxa center)
              (sub_pos.mpr hfactor).le
          constructor
          . rw [hSucc]
            exact hStep (a n) ih.1 hca
          . rw [hSucc]
            simp only [Nat.cast_succ]
            nlinarith [ih.2, hinc]
    choose n hn using exists_nat_gt ((upper - x) / delta)
    have hmul := mul_lt_mul_of_pos_right hn hdelta
    have hdiv : (upper - x) / delta * delta = upper - x := by
      field_simp [ne_of_gt hdelta]
    rw [hdiv] at hmul
    have hupper := hBound (a n) (hAll n).1
    have hlower := (hAll n).2
    linarith

/-- Zero transport plus an independent real-part bound excludes zeros beyond alpha.
This is a propagation lemma, not an assertion of an analytic transport identity. -/
theorem no_zero_of_bounded_affine_transport
    (f : Complex -> Complex) (center alpha upper factor : Real)
    (hfactor : 1 < factor) (hAlpha : center <= alpha)
    (hBound : forall z : Complex, alpha < z.re -> f z = 0 -> z.re <= upper)
    (hStep : forall z : Complex, alpha < z.re -> f z = 0 ->
      f ((center : Complex) + (factor : Complex) * (z - center)) = 0)
    (z : Complex) (hz : alpha < z.re) : Not (f z = 0) := by
  intro hzero
  let P : Real -> Prop := fun t => Exists (fun w : Complex =>
    w.re = t /\ alpha < w.re /\ f w = 0)
  have hRealBound : forall t, P t -> t <= upper := by
    intro t ht
    choose w hw using ht
    rw [<- hw.1]
    exact hBound w hw.2.1 hw.2.2
  have hRealStep : forall t, P t -> center < t ->
      P (center + factor * (t - center)) := by
    intro t ht hct
    choose w hw using ht
    let v : Complex := (center : Complex) + (factor : Complex) * (w - center)
    have hre : v.re = center + factor * (w.re - center) := by simp [v]
    have hcw : center < w.re := lt_of_le_of_lt hAlpha hw.2.1
    have hgrow : w.re < v.re := by
      rw [hre]
      nlinarith [mul_pos (sub_pos.mpr hfactor) (sub_pos.mpr hcw)]
    apply Exists.intro v
    refine And.intro ?_ (And.intro (lt_trans hw.2.1 hgrow) ?_)
    . rw [hre, hw.1]
    . exact hStep w hw.2.1 hw.2.2
  have hp : P z.re := Exists.intro z (And.intro rfl (And.intro hz hzero))
  have hle := bounded_affine_dilation_le_center P center upper factor hfactor
    hRealBound hRealStep z.re hp
  exact (not_lt_of_ge (hle.trans hAlpha)) hz

end Function

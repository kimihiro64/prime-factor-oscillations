/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Mathlib.Analysis.SpecialFunctions.Log.CubicRemainder

/-! # The signed logarithmic scaling remainder

The existing nonnegative cubic estimate is retained. Negative
displacements are controlled on their whole interval by the exact
derivative. The finite sum keeps the complete quadratic term; only its
cubic Taylor remainder is estimated by absolute values.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

theorem hamiltonian_log_one_add_cubic_small (x : Real) (hx : abs x <= 1 / 2) :
    abs (Real.log (1 + x) - x + x ^ 2 / 2) <= 2 * abs x ^ 3 := by
  by_cases hx0 : 0 <= x
  case pos =>
    have h := Real.log_one_add_cubic_remainder_bounds x hx0
    rw [abs_of_nonneg h.1, abs_of_nonneg hx0]
    nlinarith only [h.2, pow_nonneg hx0 3]
  case neg =>
    have hxNeg : x < 0 := lt_of_not_ge hx0
    let a := abs x
    let f : Real -> Real := fun y => Real.log (1 + y) - y + y ^ 2 / 2
    have ha : 0 <= a := abs_nonneg x
    have hX : -(1 / 2 : Real) <= x := (abs_le.mp hx).1
    have hDeriv (y : Real) (hy : Membership.mem (Set.Icc x 0) y) :
        HasDerivAt f (y ^ 2 / (1 + y)) y := by
      have hOne : Not (1 + y = 0) := by linarith only [hy.1, hX]
      have hLog := (Real.hasDerivAt_log hOne).comp y
        ((hasDerivAt_const y (1 : Real)).add (hasDerivAt_id y))
      have hBase := (hLog.sub (hasDerivAt_id y)).add
        (((hasDerivAt_id y).pow 2).div_const 2)
      convert hBase using 1
      next =>
        funext z
        rfl
      next =>
        norm_num
        field_simp <;> ring
    have hBound (y : Real) (hy : Membership.mem (Set.Icc x 0) y) :
        norm (y ^ 2 / (1 + y)) <= 2 * a ^ 2 := by
      have hOne : 0 < 1 + y := by linarith only [hy.1, hX]
      have hDen : Not (1 + y = 0) := ne_of_gt hOne
      have hAbs : abs y <= a := by
        rw [abs_of_nonpos hy.2]
        dsimp only [a]
        rw [abs_of_neg hxNeg]
        linarith only [hy.1]
      have hSq : y ^ 2 <= a ^ 2 := by
        have h := mul_le_mul hAbs hAbs (abs_nonneg y) ha
        simpa only [<- pow_two, sq_abs] using h
      have hRat0 : 0 <= y ^ 2 / (1 + y) := div_nonneg (sq_nonneg y) (le_of_lt hOne)
      have hClear : (y ^ 2 / (1 + y)) * (1 + y) = y ^ 2 := by field_simp
      have hProd : a ^ 2 <= (2 * a ^ 2) * (1 + y) := by
        have h := mul_le_mul_of_nonneg_left
          (show (1 / 2 : Real) <= 1 + y by linarith only [hy.1, hX]) (sq_nonneg a)
        nlinarith only [h]
      rw [Real.norm_eq_abs, abs_of_nonneg hRat0]
      by_contra hNot
      have hPos := mul_pos (sub_pos.mpr (lt_of_not_ge hNot)) hOne
      nlinarith only [hPos, hClear, hSq, hProd]
    have hMVT := (convex_Icc x 0).norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun y hy => (hDeriv y hy).hasDerivWithinAt) hBound
      (show Membership.mem (Set.Icc x 0) x from And.intro (le_refl _) (le_of_lt hxNeg))
      (show Membership.mem (Set.Icc x 0) 0 from And.intro (le_of_lt hxNeg) (le_refl _))
    have hF0 : f 0 = 0 := by simp [f]
    simp only [hF0, zero_sub, norm_neg, Real.norm_eq_abs] at hMVT
    calc
      _ = abs (f x) := rfl
      _ <= 2 * a ^ 2 * abs x := hMVT
      _ = _ := by dsimp only [a]; ring

theorem hamiltonian_scaling_log_sum_remainder
    {Iota : Type*} [Fintype Iota] (z : Iota -> Real) (radius : Real)
    (hRadius : 0 <= radius) (hSmall : radius <= 1 / 2)
    (hz : forall i, abs (z i) <= radius) :
    abs (Finset.sum Finset.univ (fun i => Real.log (1 + z i)) -
      Finset.sum Finset.univ z +
      Finset.sum Finset.univ (fun i => z i ^ 2) / 2) <=
      2 * (Fintype.card Iota : Real) * radius ^ 3 := by
  have hExact :
      Finset.sum Finset.univ (fun i => Real.log (1 + z i)) -
        Finset.sum Finset.univ z + Finset.sum Finset.univ (fun i => z i ^ 2) / 2 =
      Finset.sum Finset.univ (fun i => Real.log (1 + z i) - z i + z i ^ 2 / 2) := by
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_div]
  have hCube (i : Iota) : abs (z i) ^ 3 <= radius ^ 3 := by
    have hSq := mul_le_mul (hz i) (hz i) (abs_nonneg _) hRadius
    have h := mul_le_mul hSq (hz i) (abs_nonneg _) (mul_nonneg hRadius hRadius)
    nlinarith only [h]
  rw [hExact]
  calc
    _ <= Finset.sum Finset.univ (fun i => abs (Real.log (1 + z i) - z i + z i ^ 2 / 2)) :=
      Finset.abs_sum_le_sum_abs _ _
    _ <= Finset.sum Finset.univ (fun _ : Iota => 2 * radius ^ 3) := by
      apply Finset.sum_le_sum
      intro i hi
      exact le_trans (hamiltonian_log_one_add_cubic_small (z i) (le_trans (hz i) hSmall))
        (mul_le_mul_of_nonneg_left (hCube i) (by norm_num))
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      ring

end PrimeFactorOscillations

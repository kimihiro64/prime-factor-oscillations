/-
Copyright (c) 2026 Jonas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas
-/
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Reciprocal radii and a constrained two-point budget

The derivatives and strict convexity below control the coefficient of a
compensated pair of resolvents while retaining the finite-radius constraint.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace Real

def reciprocalRadius (w x : Real) : Real :=
  (w ^ 2 + x ^ 2) ^ (-1 / 2 : Real)

def reciprocalRadiusSlope (w x : Real) : Real :=
  -x * (w ^ 2 + x ^ 2) ^ (-3 / 2 : Real)

theorem reciprocalRadius_base_pos (w x : Real) (hw : 0 < w) :
    0 < w ^ 2 + x ^ 2 := by
  nlinarith only [sq_pos_of_pos hw, sq_nonneg x]

theorem reciprocalRadius_hasDerivAt (w x : Real) (hw : 0 < w) :
    HasDerivAt (reciprocalRadius w) (reciprocalRadiusSlope w x) x := by
  have hb : HasDerivAt (fun y : Real => w ^ 2 + y ^ 2) (2 * x) x := by
    convert ((hasDerivAt_id x).pow 2).const_add (w ^ 2) using 1 <;> norm_num
  have hp := hb.rpow_const (p := (-1 / 2 : Real))
    (Or.inl (ne_of_gt (reciprocalRadius_base_pos w x hw)))
  have he : 2 * x * (-1 / 2 : Real) *
      (w ^ 2 + x ^ 2) ^ (-1 / 2 - 1 : Real) = reciprocalRadiusSlope w x := by
    rw [show (-1 / 2 - 1 : Real) = -3 / 2 by norm_num]
    dsimp only [reciprocalRadiusSlope]
    ring
  rw [he] at hp
  exact hp

theorem reciprocalRadiusSlope_hasDerivAt (w x : Real) (hw : 0 < w) :
    HasDerivAt (reciprocalRadiusSlope w)
      ((2 * x ^ 2 - w ^ 2) * (w ^ 2 + x ^ 2) ^ (-5 / 2 : Real)) x := by
  have hb : HasDerivAt (fun y : Real => w ^ 2 + y ^ 2) (2 * x) x := by
    convert ((hasDerivAt_id x).pow 2).const_add (w ^ 2) using 1 <;> norm_num
  have hp := hb.rpow_const (p := (-3 / 2 : Real))
    (Or.inl (ne_of_gt (reciprocalRadius_base_pos w x hw)))
  have hs : (w ^ 2 + x ^ 2) ^ (-3 / 2 : Real) =
      (w ^ 2 + x ^ 2) * (w ^ 2 + x ^ 2) ^ (-5 / 2 : Real) := by
    convert rpow_add (reciprocalRadius_base_pos w x hw) 1 (-5 / 2 : Real) using 1 <;>
      norm_num
  norm_num at hs
  convert (hasDerivAt_id x).neg.mul hp using 1 <;>
    first
    | (funext z; simp only [reciprocalRadiusSlope, Pi.mul_apply, Pi.neg_apply, id_eq, neg_mul])
    | (norm_num; rw [hs]; ring)

theorem reciprocalRadius_strictAnti (w : Real) (hw : 0 < w) :
    StrictAntiOn (reciprocalRadius w) (Set.Ici 0) := by
  intro x hx y hy hxy
  change 0 <= x at hx
  change 0 <= y at hy
  have hb : w ^ 2 + x ^ 2 < w ^ 2 + y ^ 2 := by
    have hprod := mul_pos (sub_pos.mpr hxy) (by linarith : 0 < y + x)
    nlinarith only [hprod]
  exact rpow_lt_rpow_of_neg (reciprocalRadius_base_pos w x hw) hb (by norm_num)

theorem reciprocalRadius_strictConvex (w a : Real) (hw : 0 < w)
    (ha : 0 <= a) (hcurv : w ^ 2 < 2 * a ^ 2) :
    StrictConvexOn Real (Set.Ici a) (reciprocalRadius w) := by
  refine strictConvexOn_of_deriv2_pos (convex_Ici a) ?cont ?positive
  case cont =>
    intro x _
    exact (reciprocalRadius_hasDerivAt w x hw).continuousAt.continuousWithinAt
  case positive =>
    intro x hx
    have hxa : a < x := by simpa only [interior_Ici, Set.mem_Ioi] using hx
    have hxx : a ^ 2 <= x ^ 2 := by
      have hprod := mul_nonneg (sub_nonneg.mpr (le_of_lt hxa))
        (by linarith : 0 <= x + a)
      nlinarith only [hprod]
    have hfirst : deriv (reciprocalRadius w) = reciprocalRadiusSlope w := by
      funext z
      exact (reciprocalRadius_hasDerivAt w z hw).deriv
    change 0 < deriv (deriv (reciprocalRadius w)) x
    rw [hfirst, (reciprocalRadiusSlope_hasDerivAt w x hw).deriv]
    exact mul_pos (by nlinarith only [hcurv, hxx])
      (rpow_pos_of_pos (reciprocalRadius_base_pos w x hw) _)

theorem strictConvexOn_chord_mul {f : Real -> Real} (a b z : Real)
    (hconv : StrictConvexOn Real (Set.Ici a) f) (haz : a < z) (hzb : z < b) :
    (b - a) * f z < (b - z) * f a + (z - a) * f b := by
  have hab : a < b := lt_trans haz hzb
  have hne : Not (b - a = 0) := ne_of_gt (sub_pos.mpr hab)
  let u := (b - z) / (b - a)
  let v := (z - a) / (b - a)
  have hu : 0 < u := div_pos (sub_pos.mpr hzb) (sub_pos.mpr hab)
  have hv : 0 < v := div_pos (sub_pos.mpr haz) (sub_pos.mpr hab)
  have huv : u + v = 1 := by
    dsimp only [u, v]
    field_simp
    ring
  have hz : u * a + v * b = z := by
    dsimp only [u, v]
    field_simp
    ring
  have hum : (b - a) * u = b - z := by
    dsimp only [u]
    field_simp [hne]
  have hvm : (b - a) * v = z - a := by
    dsimp only [v]
    field_simp [hne]
  have hh := hconv.2 (x := a) (le_refl a) (y := b) (le_of_lt hab)
    (ne_of_lt hab) hu hv huv
  simp only [smul_eq_mul] at hh
  rw [hz] at hh
  calc
    (b - a) * f z < (b - a) * (u * f a + v * f b) :=
      mul_lt_mul_of_pos_left hh (sub_pos.mpr hab)
    _ = (b - z) * f a + (z - a) * f b := by
      rw [mul_add, <- mul_assoc, <- mul_assoc, hum, hvm]

theorem strictConvexOn_ordered_budget_strict {f : Real -> Real} (a b x y : Real)
    (hab : a < b) (hconv : StrictConvexOn Real (Set.Ici a) f)
    (hanti : StrictAntiOn f (Set.Ici a)) (hax : a < x) (hxy : x <= y)
    (hbudget : a + b <= x + y) : f x + f y < f a + f b := by
  have hay : a < y := lt_of_lt_of_le hax hxy
  by_cases hby : b <= y
  case pos =>
    have hfx := hanti (le_refl a) (le_of_lt hax) hax
    have hfy : f y <= f b := by
      by_cases heq : b = y
      case pos => rw [<- heq]
      case neg =>
        have hlt : b < y := lt_of_le_of_ne hby heq
        exact le_of_lt (hanti (le_of_lt hab) (le_of_lt hay) hlt)
    linarith only [hfx, hfy]
  case neg =>
    have hyb : y < b := lt_of_not_ge hby
    have hxb : x < b := lt_of_le_of_lt hxy hyb
    have hxChord := strictConvexOn_chord_mul a b x hconv hax hxb
    have hyChord := strictConvexOn_chord_mul a b y hconv hay hyb
    have hfa := hanti (le_refl a) (le_of_lt hab) hab
    have hProduct := mul_nonneg (sub_nonneg.mpr hbudget)
      (sub_nonneg.mpr (le_of_lt hfa))
    have hScaled : (b - a) * (f x + f y) < (b - a) * (f a + f b) := by
      nlinarith only [hxChord, hyChord, hProduct]
    by_contra hn
    have hprod := mul_nonneg (le_of_lt (sub_pos.mpr hab))
      (sub_nonneg.mpr (le_of_not_gt hn))
    nlinarith only [hScaled, hprod]

theorem strictConvexOn_ordered_budget_le {f : Real -> Real} (a b x y : Real)
    (hab : a < b) (hconv : StrictConvexOn Real (Set.Ici a) f)
    (hanti : StrictAntiOn f (Set.Ici a)) (hax : a <= x) (hxy : x <= y)
    (hbudget : a + b <= x + y) : f x + f y <= f a + f b := by
  by_cases hxa : x = a
  case pos =>
    have hby : b <= y := by linarith only [hbudget, hxa]
    have hfy : f y <= f b := by
      by_cases heq : b = y
      case pos => rw [<- heq]
      case neg =>
        have hlt : b < y := lt_of_le_of_ne hby heq
        exact le_of_lt (hanti (le_of_lt hab) (le_trans (le_of_lt hab) hby) hlt)
    rw [hxa]
    linarith only [hfy]
  case neg =>
    exact le_of_lt (strictConvexOn_ordered_budget_strict a b x y hab hconv hanti
      (lt_of_le_of_ne hax (Ne.symm hxa)) hxy hbudget)

theorem strictConvexOn_ordered_budget_eq_iff {f : Real -> Real} (a b x y : Real)
    (hab : a < b) (hconv : StrictConvexOn Real (Set.Ici a) f)
    (hanti : StrictAntiOn f (Set.Ici a)) (hax : a <= x) (hxy : x <= y)
    (hbudget : a + b <= x + y) :
    (f x + f y = f a + f b) <-> And (x = a) (y = b) := by
  constructor
  case mp =>
    intro heq
    have hxa : x = a := by
      by_contra hn
      have hh := strictConvexOn_ordered_budget_strict a b x y hab hconv hanti
        (lt_of_le_of_ne hax (Ne.symm hn)) hxy hbudget
      linarith only [hh, heq]
    have hby : b <= y := by linarith only [hbudget, hxa]
    have hyb : y = b := by
      by_contra hn
      have hlt : b < y := lt_of_le_of_ne hby (Ne.symm hn)
      have hh := hanti (le_of_lt hab) (le_trans (le_of_lt hab) hby) hlt
      rw [hxa] at heq
      linarith only [hh, heq]
    exact And.intro hxa hyb
  case mpr =>
    intro hh
    rw [hh.1, hh.2]

end Real

/-
Copyright (c) 2026 Jonas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas
-/
import PrimeFactorOscillations.Mathlib.Analysis.Complex.PairedResolventSharpStrip
import PrimeFactorOscillations.Mathlib.Analysis.Complex.ReciprocalRadiusConvexity

/-!
# Sharp finite radii for the seven-eighths strip

The coefficient is optimized only in the compensated class with weight r / R.
The inner radius is at least one half, as required by independent Euler bounds.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace Real

def sharpResolventSemiaxis : Real := sqrt 7 / 8

def sharpResolventOuter : Real := sqrt (13 - 3 * sqrt 7) / 4

def pairedResolventCoefficient (r R : Real) : Real := r * R / (2 * (r + R))

def sharpResolventCoefficient : Real :=
  sqrt (13 - 3 * sqrt 7) / (4 * (2 + sqrt (13 - 3 * sqrt 7)))

theorem sharpResolventSemiaxis_pos : 0 < sharpResolventSemiaxis := by
  exact div_pos (sqrt_pos.mpr (by norm_num)) (by norm_num)

theorem sharpResolventSemiaxis_sq : sharpResolventSemiaxis ^ 2 = 7 / 64 := by
  have hh := sq_sqrt (by norm_num : (0 : Real) <= 7)
  dsimp only [sharpResolventSemiaxis]
  nlinarith only [hh]

theorem sharpResolventSemiaxis_lt : sharpResolventSemiaxis < 3 / 8 := by
  have h0 := sharpResolventSemiaxis_pos
  have h2 := sharpResolventSemiaxis_sq
  nlinarith only [h0, h2]

theorem sharpResolventOuter_sq :
    sharpResolventOuter ^ 2 = (3 / 8 : Real) ^ 2 +
      (3 / 4 - sharpResolventSemiaxis) ^ 2 := by
  have h7 : (sqrt 7) ^ 2 = (7 : Real) := sq_sqrt (by norm_num)
  have h7p : 0 <= sqrt (7 : Real) := sqrt_nonneg _
  have h7b : sqrt (7 : Real) < 3 := by nlinarith only [h7, h7p]
  have hd : 0 <= (13 - 3 * sqrt 7 : Real) := by linarith only [h7b]
  have hs := sq_sqrt hd
  dsimp only [sharpResolventOuter, sharpResolventSemiaxis]
  nlinarith only [h7, hs]

theorem sharpResolventOuter_gt_half : 1 / 2 < sharpResolventOuter := by
  have h0 : 0 <= sharpResolventOuter := div_nonneg (sqrt_nonneg _) (by norm_num)
  have ha0 := sharpResolventSemiaxis_pos
  have ha1 := sharpResolventSemiaxis_lt
  have ha2 := sharpResolventSemiaxis_sq
  have hsq := sharpResolventOuter_sq
  nlinarith only [h0, ha0, ha1, ha2, hsq]

theorem sharpResolvent_floor_coordinate :
    sqrt ((1 / 2 : Real) ^ 2 - (3 / 8 : Real) ^ 2) = sharpResolventSemiaxis := by
  apply (sqrt_eq_iff_eq_sq (by norm_num) (le_of_lt sharpResolventSemiaxis_pos)).mpr
  rw [sharpResolventSemiaxis_sq]
  norm_num

theorem sharpResolvent_outer_coordinate :
    sqrt (sharpResolventOuter ^ 2 - (3 / 8 : Real) ^ 2) =
      3 / 4 - sharpResolventSemiaxis := by
  have ha := sharpResolventSemiaxis_lt
  have hs := sharpResolventOuter_sq
  have hb := sq_nonneg (3 / 4 - sharpResolventSemiaxis)
  apply (sqrt_eq_iff_eq_sq (by linarith only [hs, hb]) (by linarith only [ha])).mpr
  linarith only [hs]

theorem reciprocalRadius_sqrt (w r : Real) (hw : 0 < w) (hr : w < r) :
    reciprocalRadius w (sqrt (r ^ 2 - w ^ 2)) = 1 / r := by
  have hr0 : 0 < r := hw.trans hr
  have hd : 0 <= r ^ 2 - w ^ 2 := by
    have hh := mul_nonneg (sub_nonneg.mpr (le_of_lt hr))
      (by linarith only [hr0, hw] : 0 <= r + w)
    nlinarith only [hh]
  have hb : w ^ 2 + (sqrt (r ^ 2 - w ^ 2)) ^ 2 = r ^ 2 := by
    rw [sq_sqrt hd]
    ring
  dsimp only [reciprocalRadius]
  rw [hb, show (-1 / 2 : Real) = -(1 / 2 : Real) by ring,
    rpow_neg (sq_nonneg r), <- sqrt_eq_rpow, sqrt_sq hr0.le]
  simp only [one_div]

theorem sharpResolvent_endpoint_reciprocals :
    And (reciprocalRadius (3 / 8) sharpResolventSemiaxis = 2)
      (reciprocalRadius (3 / 8) (3 / 4 - sharpResolventSemiaxis) =
        1 / sharpResolventOuter) := by
  constructor
  case left =>
    rw [<- sharpResolvent_floor_coordinate,
      reciprocalRadius_sqrt (3 / 8) (1 / 2) (by norm_num) (by norm_num)]
    norm_num
  case right =>
    rw [<- sharpResolvent_outer_coordinate]
    exact reciprocalRadius_sqrt (3 / 8) sharpResolventOuter (by norm_num)
      (by linarith only [sharpResolventOuter_gt_half])

theorem sharpResolvent_budget (r R : Real) (hr : 1 / 2 <= r) (hR : r < R)
    (hPos : 2 * (3 / 8 : Real) <= sqrt (r ^ 2 - (3 / 8 : Real) ^ 2) +
      sqrt (R ^ 2 - (3 / 8 : Real) ^ 2)) :
    And (1 / r + 1 / R <= 2 + 1 / sharpResolventOuter)
      ((1 / r + 1 / R = 2 + 1 / sharpResolventOuter) <->
        And (r = 1 / 2) (R = sharpResolventOuter)) := by
  let a := sharpResolventSemiaxis
  let b := 3 / 4 - a
  let u := sqrt (r ^ 2 - (3 / 8 : Real) ^ 2)
  let v := sqrt (R ^ 2 - (3 / 8 : Real) ^ 2)
  have ha0 : 0 <= a := le_of_lt sharpResolventSemiaxis_pos
  have ha2 : a ^ 2 = 7 / 64 := sharpResolventSemiaxis_sq
  have hab : a < b := by dsimp only [a, b]; linarith only [sharpResolventSemiaxis_lt]
  have hu0 : 0 <= u := sqrt_nonneg _
  have hu2 : u ^ 2 = r ^ 2 - (3 / 8 : Real) ^ 2 := by
    apply sq_sqrt
    have hh := mul_nonneg (by linarith only [hr] : 0 <= r - 1 / 2)
      (by linarith only [hr] : 0 <= r + 1 / 2)
    nlinarith only [hh]
  have hau : a <= u := by nlinarith only [ha0, ha2, hu0, hu2, hr]
  have huv : u <= v := by
    apply sqrt_le_sqrt
    have hh := mul_nonneg (sub_nonneg.mpr hR.le)
      (by linarith only [hr, hR] : 0 <= R + r)
    nlinarith only [hh]
  have hbudget : a + b <= u + v := by dsimp only [a, b, u, v]; linarith only [hPos]
  have hconv : StrictConvexOn Real (Set.Ici a) (reciprocalRadius (3 / 8)) :=
    reciprocalRadius_strictConvex (3 / 8) a (by norm_num) ha0
      (by nlinarith only [ha2])
  have hanti : StrictAntiOn (reciprocalRadius (3 / 8)) (Set.Ici a) := by
    intro x hx y hy hxy
    exact reciprocalRadius_strictAnti (3 / 8) (by norm_num)
      (le_trans ha0 hx) (le_trans ha0 hy) hxy
  have hh := strictConvexOn_ordered_budget_le a b u v hab hconv hanti hau huv hbudget
  have hEq := strictConvexOn_ordered_budget_eq_iff a b u v hab hconv hanti hau huv hbudget
  rw [reciprocalRadius_sqrt (3 / 8) r (by norm_num) (by linarith only [hr]),
    reciprocalRadius_sqrt (3 / 8) R (by norm_num) (by linarith only [hr, hR])] at hh hEq
  simp only [a, b, sharpResolvent_endpoint_reciprocals.1,
    sharpResolvent_endpoint_reciprocals.2] at hh hEq
  refine And.intro hh ?_
  constructor
  case mp =>
    intro hRecip
    have hCoords := hEq.mp hRecip
    have hFirst : r = 1 / 2 := by
      rw [hCoords.1] at hu2
      nlinarith only [hu2, sharpResolventSemiaxis_sq, hr]
    have hv2 : v ^ 2 = R ^ 2 - (3 / 8 : Real) ^ 2 := by
      apply sq_sqrt
      have hx := mul_nonneg (by linarith only [hr, hR] : 0 <= R - 1 / 2)
        (by linarith only [hr, hR] : 0 <= R + 1 / 2)
      nlinarith only [hx]
    rw [hCoords.2] at hv2
    have hSecond : R = sharpResolventOuter := by
      nlinarith only [hv2, sharpResolventOuter_sq, hr, hR, sharpResolventOuter_gt_half]
    exact And.intro hFirst hSecond
  case mpr =>
    intro h
    rw [h.1, h.2]
    norm_num

theorem sharpResolventCoefficient_eq :
    sharpResolventCoefficient = sharpResolventOuter /
      (2 * (1 + 2 * sharpResolventOuter)) := by
  unfold sharpResolventCoefficient sharpResolventOuter
  field_simp
  ring

theorem pairedResolventCoefficient_ge_sharp (r R : Real)
    (hr : 1 / 2 <= r) (hR : r < R)
    (hPos : 2 * (3 / 8 : Real) <= sqrt (r ^ 2 - (3 / 8 : Real) ^ 2) +
      sqrt (R ^ 2 - (3 / 8 : Real) ^ 2)) :
    sharpResolventCoefficient <= pairedResolventCoefficient r R := by
  have hr0 : 0 < r := by linarith only [hr]
  have hR0 : 0 < R := hr0.trans hR
  have hs0 : 0 < sharpResolventOuter := by linarith only [sharpResolventOuter_gt_half]
  have hh := (sharpResolvent_budget r R hr hR hPos).1
  have hm := mul_le_mul_of_nonneg_right hh (le_of_lt (mul_pos (mul_pos hr0 hR0) hs0))
  have hp : sharpResolventOuter * (r + R) <=
      r * R * (2 * sharpResolventOuter + 1) := by
    convert hm using 1 <;> field_simp [hr0.ne', hR0.ne', hs0.ne'] <;> ring
  rw [sharpResolventCoefficient_eq]
  unfold pairedResolventCoefficient
  have hc : sharpResolventOuter * (2 * (r + R)) <=
      r * R * (2 * (1 + 2 * sharpResolventOuter)) := by nlinarith only [hp]
  have hd1 : 0 < 2 * (1 + 2 * sharpResolventOuter) := by positivity
  have hd2 : 0 < 2 * (r + R) := by positivity
  have hmul := mul_le_mul_of_nonneg_right hc
    (div_nonneg (by norm_num : (0 : Real) <= 1) (mul_nonneg hd1.le hd2.le))
  convert hmul using 1 <;> field_simp [hd1.ne', hd2.ne'] <;> ring

theorem pairedResolventCoefficient_eq_sharp_iff (r R : Real)
    (hr : 1 / 2 <= r) (hR : r < R)
    (hPos : 2 * (3 / 8 : Real) <= sqrt (r ^ 2 - (3 / 8 : Real) ^ 2) +
      sqrt (R ^ 2 - (3 / 8 : Real) ^ 2)) :
    (pairedResolventCoefficient r R = sharpResolventCoefficient) <->
      And (r = 1 / 2) (R = sharpResolventOuter) := by
  have hr0 : 0 < r := by linarith only [hr]
  have hR0 : 0 < R := hr0.trans hR
  have hs0 : 0 < sharpResolventOuter := by linarith only [sharpResolventOuter_gt_half]
  have hd : Not (r + R = 0) := ne_of_gt (add_pos hr0 hR0)
  have he : Not (1 + 2 * sharpResolventOuter = 0) := by positivity
  constructor
  case mp =>
    intro h
    rw [sharpResolventCoefficient_eq] at h
    unfold pairedResolventCoefficient at h
    field_simp [hd, he] at h
    have hRecip : 1 / r + 1 / R = 2 + 1 / sharpResolventOuter := by
      field_simp [hr0.ne', hR0.ne', hs0.ne']
      nlinarith only [h]
    exact (sharpResolvent_budget r R hr hR hPos).2.mp hRecip
  case mpr =>
    intro h
    rw [h.1, h.2, sharpResolventCoefficient_eq]
    unfold pairedResolventCoefficient
    field_simp

theorem sharpResolvent_positive_of_inner (r : Real) (hr : 1 / 2 <= r) :
    2 * (3 / 8 : Real) <= sqrt (r ^ 2 - (3 / 8 : Real) ^ 2) +
      sqrt (sharpResolventOuter ^ 2 - (3 / 8 : Real) ^ 2) := by
  have hprod := mul_nonneg (by linarith only [hr] : 0 <= r - 1 / 2)
    (by linarith only [hr] : 0 <= r + 1 / 2)
  have hh : sqrt ((1 / 2 : Real) ^ 2 - (3 / 8 : Real) ^ 2) <=
      sqrt (r ^ 2 - (3 / 8 : Real) ^ 2) := sqrt_le_sqrt (by nlinarith only [hprod])
  rw [sharpResolvent_floor_coordinate] at hh
  rw [sharpResolvent_outer_coordinate]
  linarith only [hh]

theorem pairedResolventCoefficient_increment (r s : Real) (hr : 1 / 2 <= r)
    (hs : 0 < s) : pairedResolventCoefficient r s <=
      pairedResolventCoefficient (1 / 2) s + (r - 1 / 2) / 2 := by
  have hr0 : 0 < r := by linarith only [hr]
  have hd1 : 0 < r + s := add_pos hr0 hs
  have hd2 : 0 < 1 / 2 + s := by linarith only [hs]
  have hId : pairedResolventCoefficient r s - pairedResolventCoefficient (1 / 2) s =
      s ^ 2 * (r - 1 / 2) / (2 * (r + s) * (1 / 2 + s)) := by
    unfold pairedResolventCoefficient
    field_simp [hd1.ne', hd2.ne']
    ring
  have hDen : s ^ 2 <= (r + s) * (1 / 2 + s) := by
    nlinarith only [hr, hs, mul_nonneg hr0.le hs.le]
  have hNum := mul_le_mul_of_nonneg_right hDen (sub_nonneg.mpr hr)
  have hd : 0 < 2 * (r + s) * (1 / 2 + s) := by positivity
  have hMul := mul_le_mul_of_nonneg_right hNum
    (div_nonneg (by norm_num : (0 : Real) <= 1) hd.le)
  have hBound : pairedResolventCoefficient r s - pairedResolventCoefficient (1 / 2) s <=
      (r - 1 / 2) / 2 := by
    rw [hId]
    convert hMul using 1 <;> field_simp [hd1.ne', hd2.ne'] <;> ring
  linarith only [hBound]

theorem sharpResolvent_admissible_approximation (eps : Real) (heps : 0 < eps) :
    Exists (fun r : Real => Exists (fun R : Real => And (1 / 2 < r) (And (r < R)
      (And (2 * (3 / 8 : Real) <= sqrt (r ^ 2 - (3 / 8 : Real) ^ 2) +
        sqrt (R ^ 2 - (3 / 8 : Real) ^ 2))
        (pairedResolventCoefficient r R < sharpResolventCoefficient + eps))))) := by
  let d := min ((sharpResolventOuter - 1 / 2) / 2) eps
  let r := 1 / 2 + d
  have hd : 0 < d := lt_min (by linarith only [sharpResolventOuter_gt_half]) heps
  have hdOuter : d <= (sharpResolventOuter - 1 / 2) / 2 := min_le_left _ _
  have hdEps : d <= eps := min_le_right _ _
  have hr : 1 / 2 < r := by dsimp only [r]; linarith only [hd]
  have hR : r < sharpResolventOuter := by
    dsimp only [r]
    linarith only [hdOuter, sharpResolventOuter_gt_half]
  have hBound := pairedResolventCoefficient_increment r sharpResolventOuter hr.le
    (by linarith only [sharpResolventOuter_gt_half])
  have hBase : pairedResolventCoefficient (1 / 2) sharpResolventOuter =
      sharpResolventCoefficient := by
    rw [sharpResolventCoefficient_eq]
    unfold pairedResolventCoefficient
    field_simp
  rw [hBase] at hBound
  refine Exists.intro r (Exists.intro sharpResolventOuter
    (And.intro hr (And.intro hR (And.intro (sharpResolvent_positive_of_inner r hr.le) ?_))))
  dsimp only [r] at hBound
  linarith only [hBound, hdEps, heps]

end Real

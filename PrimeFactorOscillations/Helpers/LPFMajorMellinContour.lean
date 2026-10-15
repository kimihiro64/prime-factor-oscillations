/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.LPFMajorContourBudget
import PrimeFactorOscillations.Helpers.LPFMajorContourNorm

/-!
# A numerical Mellin contour estimate

Common growth 26624*B on the specified rectangle, together with
holomorphy to the right of seven eighths, gives the normalized bound
54912*X^(15/16)*B^2. The proof includes both horizontal edges and the
logarithmic vertical integral. Every growth, height and cutoff input is
explicit; the character application supplies these inputs separately.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.QRH

noncomputable def lpfMellinKernel (g : Complex -> Complex) (X : Real) : Complex -> Complex :=
  g * (fun s : Complex => (X : Complex) ^ s) / id

theorem lpf_mellin_kernel_norm (g : Complex -> Complex) (X : Real)
    (hX : 0 < X) (s : Complex) :
    norm (lpfMellinKernel g X s) = norm (g s) * X ^ s.re / norm s := by
  simp only [lpfMellinKernel, Pi.div_apply, Pi.mul_apply, id_eq,
    norm_div, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hX]

private theorem curve_intervalIntegrable (F : Complex -> Complex)
    (curve : Real -> Complex) (a b : Real) (hCurve : Continuous curve)
    (hD : forall t, Membership.mem (Set.uIcc a b) t ->
      DifferentiableAt Complex F (curve t)) :
    IntervalIntegrable (Function.comp F curve) MeasureTheory.volume a b := by
  have hCont : ContinuousOn (Function.comp F curve) (Set.uIcc a b) := by
    intro t ht
    exact (hD t ht).continuousAt.comp_continuousWithinAt hCurve.continuousWithinAt
  exact hCont.intervalIntegrable

theorem lpf_mellin_contour_numeric (g : Complex -> Complex) (X c B : Real)
    (hX : 4 <= X) (hB : 1 <= B) (hc : 1 < c) (hc2 : c <= 2)
    (hLog : Real.log (1 + X) <= B) (hPower : X ^ c <= 3 * X)
    (hDiff : forall s : Complex, 7 / 8 < s.re ->
      DifferentiableAt Complex (lpfMellinKernel g X) s)
    (hGrowth : forall sigma t : Real, 15 / 16 <= sigma -> sigma <= 2 ->
      abs t <= X -> norm (g ((sigma : Complex) + (t : Complex) * Complex.I)) <= 26624 * B) :
    norm ((1 / (2 * (Real.pi : Complex) * Complex.I)) * Complex.I *
      intervalIntegral (fun t : Real =>
        lpfMellinKernel g X ((c : Complex) + (t : Complex) * Complex.I))
        (-X) X MeasureTheory.volume) <= 54912 * X ^ (15 / 16 : Real) * B ^ 2 := by
  let a : Real := 15 / 16
  let R : Real := X ^ a
  let C : Real := 79872 * B * R
  let H : Real := 79872 * B
  let F : Complex -> Complex := lpfMellinKernel g X
  have hX0 : 0 < X := by linarith
  have hX1 : 1 <= X := by linarith
  have hB0 : 0 <= B := by linarith
  have hAC : a <= c := by dsimp [a]; linarith
  have hR : 1 <= R := Real.one_le_rpow hX1 (by norm_num [a])
  have hR0 : 0 <= R := by linarith
  have hLeft : forall t : Real, Membership.mem (Set.Icc (-X) X) t ->
      norm (F ((a : Complex) + (t : Complex) * Complex.I)) <= C / (1 + abs t) := by
    intro t ht
    have hMag : abs t <= X := abs_le.mpr (Set.mem_Icc.mp ht)
    let s : Complex := (a : Complex) + (t : Complex) * Complex.I
    have hRe : s.re = a := by simp [s]
    have hG := hGrowth a t (by norm_num [a]) (by norm_num [a]) hMag
    have hRecip : 1 / norm s <= 3 / (1 + abs t) := by
      simpa only [s, mul_comm] using
        lpf_vertical_reciprocal_kernel_bound a t (by norm_num [a])
    change norm (lpfMellinKernel g X s) <= C / (1 + abs t)
    rw [lpf_mellin_kernel_norm g X hX0 s, hRe]
    calc
      _ <= (26624 * B * R) / norm s :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right hG hR0) (norm_nonneg s)
      _ = (26624 * B * R) * (1 / norm s) := by ring
      _ <= (26624 * B * R) * (3 / (1 + abs t)) :=
        mul_le_mul_of_nonneg_left hRecip (by positivity)
      _ = _ := by dsimp [C]; ring
  have hHorizontal (t : Real) (ht : abs t = X) :
      forall sigma : Real, Membership.mem (Set.Icc a c) sigma ->
        norm (F ((sigma : Complex) + (t : Complex) * Complex.I)) <= H := by
    intro sigma hs
    have hS := Set.mem_Icc.mp hs
    let s : Complex := (sigma : Complex) + (t : Complex) * Complex.I
    have hRe : s.re = sigma := by simp [s]
    have hIm : s.im = t := by simp [s]
    have hNorm : X <= norm s := by
      rw [<- ht, <- hIm]
      exact Complex.abs_im_le_norm s
    have hG := hGrowth sigma t hS.1 (hS.2.trans hc2) ht.le
    have hPow := Real.rpow_le_rpow_of_exponent_le hX1 hS.2
    have hPow0 : 0 <= X ^ sigma := Real.rpow_nonneg hX0.le sigma
    change norm (lpfMellinKernel g X s) <= H
    rw [lpf_mellin_kernel_norm g X hX0 s, hRe]
    calc
      _ <= (26624 * B * X ^ sigma) / norm s :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right hG hPow0) (norm_nonneg s)
      _ <= (26624 * B * X ^ sigma) / X :=
        div_le_div_of_nonneg_left (by positivity) hX0 hNorm
      _ <= (26624 * B * X ^ c) / X :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hPow (by positivity)) hX0.le
      _ <= (26624 * B * (3 * X)) / X :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hPower (by positivity)) hX0.le
      _ = _ := by dsimp [H]; field_simp [ne_of_gt hX0]; ring
  have hFRect (s : Complex) (h1 : a <= s.re) (_h2 : s.re <= c)
      (_h3 : -X <= s.im) (_h4 : s.im <= X) : DifferentiableAt Complex F s := by
    apply hDiff
    dsimp [a] at h1
    linarith
  have hLeftCurve : Continuous (fun t : Real =>
      (a : Complex) + (t : Complex) * Complex.I) :=
    continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
  have hLeftInt : IntervalIntegrable (fun t : Real =>
      F ((a : Complex) + (t : Complex) * Complex.I)) MeasureTheory.volume (-X) X := by
    apply curve_intervalIntegrable F _ (-X) X hLeftCurve
    intro t _ht
    apply hDiff
    norm_num [a]
  have hHorInt (t : Real) : IntervalIntegrable (fun sigma : Real =>
      F ((sigma : Complex) + (t : Complex) * Complex.I)) MeasureTheory.volume a c := by
    have hCurve : Continuous (fun sigma : Real =>
        (sigma : Complex) + (t : Complex) * Complex.I) :=
      Complex.continuous_ofReal.add continuous_const
    apply curve_intervalIntegrable F _ a c hCurve
    intro sigma hs
    rw [Set.uIcc_of_le hAC] at hs
    have h1 := (Set.mem_Icc.mp hs).1
    have hRe : ((sigma : Complex) + (t : Complex) * Complex.I).re = sigma := by simp
    apply hDiff
    rw [hRe]
    dsimp [a] at h1
    linarith
  have hBottom := hHorizontal (-X) (by rw [abs_neg, abs_of_pos hX0])
  have hTop := hHorizontal X (abs_of_pos hX0)
  have hRect := lpf_rectangle_contour_integral_bound F a c X C H hAC hX0.le
    hFRect hLeftInt (hHorInt (-X)) (hHorInt X) hLeft hBottom hTop
  let z : Complex := intervalIntegral (fun t : Real =>
    F ((c : Complex) + (t : Complex) * Complex.I)) (-X) X MeasureTheory.volume
  have hReplace := mul_le_mul_of_nonneg_left hLog (show 0 <= 2 * C by positivity)
  have hNorm : norm z <= 2 * (79872 * B * R) * B +
      2 * (c - 15 / 16) * (79872 * B) := by
    change norm z <= _ at hRect
    calc
      _ <= 2 * C * Real.log (1 + X) + 2 * (c - a) * H := hRect
      _ <= 2 * C * B + 2 * (c - a) * H := by linarith only [hReplace]
      _ = _ := by rfl
  exact lpf_contour_numeric_budget B R c z hB hR hc2 hNorm

end PrimeFactorOscillations.QRH


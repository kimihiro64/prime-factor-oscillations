/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.LPFMajorZetaIntegral

/-!
# Numerical envelopes for a rectangular contour shift

The reciprocal vertical kernel has logarithmic integral growth. Its exact
integral, both horizontal bounds and Cauchy's rectangular identity give one
bound retaining all three shifted edges. This is pure complex analysis;
the character growth and prime-prefix applications are separate consumers.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.QRH

theorem lpf_vertical_reciprocal_kernel_bound (sigma t : Real)
    (hSigma : 15 / 16 <= sigma) :
    1 / norm ((sigma : Complex) + Complex.I * (t : Complex)) <=
      3 / (1 + abs t) := by
  let s : Complex := (sigma : Complex) + Complex.I * (t : Complex)
  have hRe : s.re = sigma := by simp [s]
  have hIm : s.im = t := by simp [s]
  have hs1 : sigma <= norm s := by
    exact (le_abs_self sigma).trans (by simpa only [hRe] using Complex.abs_re_le_norm s)
  have hs2 : abs t <= norm s := by
    simpa only [hIm] using Complex.abs_im_le_norm s
  have hs0 : 0 < norm s := by linarith
  have hDen : 0 < 1 + abs t := by linarith [abs_nonneg t]
  change 1 / norm s <= 3 / (1 + abs t)
  have hCross : 1 + abs t <= 3 * norm s := by linarith
  have hMul := mul_le_mul_of_nonneg_right hCross
    (show 0 <= 1 / (norm s * (1 + abs t)) by positivity)
  calc
    1 / norm s = (1 + abs t) * (1 / (norm s * (1 + abs t))) := by
      field_simp [ne_of_gt hs0, ne_of_gt hDen]
    _ <= (3 * norm s) * (1 / (norm s * (1 + abs t))) := hMul
    _ = 3 / (1 + abs t) := by
      field_simp [ne_of_gt hs0, ne_of_gt hDen]

theorem lpf_integral_inverse_one_add_abs (T : Real) (hT : 0 <= T) :
    intervalIntegral (fun t : Real => 1 / (1 + abs t)) (-T) T MeasureTheory.volume =
      2 * Real.log (1 + T) := by
  let f : Real -> Real := fun t => 1 / (1 + abs t)
  have hCont : Continuous f :=
    continuous_const.div (continuous_const.add continuous_abs)
      (fun t => by dsimp; linarith [abs_nonneg t])
  have hDeriv : forall t, Membership.mem (Set.uIcc (0 : Real) T) t ->
      HasDerivAt (fun u : Real => Real.log (1 + u)) (f t) t := by
    intro t ht
    rw [Set.uIcc_of_le hT] at ht
    have ht0 : 0 <= t := (Set.mem_Icc.mp ht).1
    have hn : Not (1 + t = 0) := by linarith
    have hd := ((hasDerivAt_id t).const_add (1 : Real)).log hn
    simpa only [f, id_eq, abs_of_nonneg ht0] using hd
  have hPos := intervalIntegral.integral_eq_sub_of_hasDerivAt hDeriv
    (hCont.intervalIntegrable 0 T)
  simp only [add_zero, Real.log_one, sub_zero] at hPos
  have he : (fun t : Real => f (-t)) = f := by
    funext t
    simp only [f, abs_neg]
  have hNeg := intervalIntegral.integral_comp_neg (a := -T) (b := (0 : Real)) f
  rw [he] at hNeg
  simp only [neg_zero, neg_neg] at hNeg
  have hSplit : intervalIntegral f (-T) 0 MeasureTheory.volume +
      intervalIntegral f 0 T MeasureTheory.volume =
        intervalIntegral f (-T) T MeasureTheory.volume :=
    intervalIntegral.integral_add_adjacent_intervals
      (hCont.intervalIntegrable (-T) 0) (hCont.intervalIntegrable 0 T)
  change intervalIntegral f (-T) T MeasureTheory.volume = 2 * Real.log (1 + T)
  rw [<- hSplit]
  simp only [hNeg, hPos]
  ring

theorem lpf_vertical_integral_envelope (f : Real -> Complex) (C T : Real)
    (hT : 0 <= T) (hf : IntervalIntegrable f MeasureTheory.volume (-T) T)
    (hBound : forall t, Membership.mem (Set.Icc (-T) T) t ->
      norm (f t) <= C / (1 + abs t)) :
    norm (intervalIntegral f (-T) T MeasureTheory.volume) <= 2 * C * Real.log (1 + T) := by
  have hCont : Continuous (fun t : Real => C / (1 + abs t)) :=
    continuous_const.div (continuous_const.add continuous_abs)
      (fun t => by linarith [abs_nonneg t])
  calc
    _ <= intervalIntegral (fun t => norm (f t)) (-T) T MeasureTheory.volume :=
      intervalIntegral.norm_integral_le_integral_norm (by linarith)
    _ <= intervalIntegral (fun t : Real => C / (1 + abs t)) (-T) T MeasureTheory.volume :=
      intervalIntegral.integral_mono_on (by linarith) hf.norm
        (hCont.intervalIntegrable (-T) T) hBound
    _ = _ := by
      have he : (fun t : Real => C / (1 + abs t)) =
          (fun t : Real => C * (1 / (1 + abs t))) := by
        funext t
        ring
      rw [he, intervalIntegral.integral_const_mul, lpf_integral_inverse_one_add_abs T hT]
      ring

theorem lpf_horizontal_integral_envelope (f : Real -> Complex) (C a b : Real)
    (hab : a <= b) (hf : IntervalIntegrable f MeasureTheory.volume a b)
    (hBound : forall t, Membership.mem (Set.Icc a b) t -> norm (f t) <= C) :
    norm (intervalIntegral f a b MeasureTheory.volume) <= (b - a) * C := by
  calc
    _ <= intervalIntegral (fun t => norm (f t)) a b MeasureTheory.volume :=
      intervalIntegral.norm_integral_le_integral_norm hab
    _ <= intervalIntegral (fun _ : Real => C) a b MeasureTheory.volume :=
      intervalIntegral.integral_mono_on hab hf.norm
        (continuous_const.intervalIntegrable a b) hBound
    _ = _ := by simp only [intervalIntegral.integral_const, smul_eq_mul]

theorem lpf_rectangle_contour_integral_bound
    (f : Complex -> Complex) (sigma c T C H : Real)
    (hSC : sigma <= c) (hT : 0 <= T)
    (hDiff : forall s : Complex, sigma <= s.re -> s.re <= c ->
      -T <= s.im -> s.im <= T -> DifferentiableAt Complex f s)
    (hLeftInt : IntervalIntegrable (fun t : Real =>
      f ((sigma : Complex) + (t : Complex) * Complex.I)) MeasureTheory.volume (-T) T)
    (hBottomInt : IntervalIntegrable (fun u : Real =>
      f ((u : Complex) + ((-T : Real) : Complex) * Complex.I)) MeasureTheory.volume sigma c)
    (hTopInt : IntervalIntegrable (fun u : Real =>
      f ((u : Complex) + (T : Complex) * Complex.I)) MeasureTheory.volume sigma c)
    (hLeft : forall t : Real, Membership.mem (Set.Icc (-T) T) t ->
      norm (f ((sigma : Complex) + (t : Complex) * Complex.I)) <= C / (1 + abs t))
    (hBottom : forall u : Real, Membership.mem (Set.Icc sigma c) u ->
      norm (f ((u : Complex) + ((-T : Real) : Complex) * Complex.I)) <= H)
    (hTop : forall u : Real, Membership.mem (Set.Icc sigma c) u ->
      norm (f ((u : Complex) + (T : Complex) * Complex.I)) <= H) :
    norm (intervalIntegral (fun t : Real =>
      f ((c : Complex) + (t : Complex) * Complex.I)) (-T) T MeasureTheory.volume) <=
        2 * C * Real.log (1 + T) + 2 * (c - sigma) * H := by
  let z : Complex := (sigma : Complex) + ((-T : Real) : Complex) * Complex.I
  let w : Complex := (c : Complex) + (T : Complex) * Complex.I
  have hzRe : z.re = sigma := by simp [z]
  have hzIm : z.im = -T := by simp [z]
  have hwRe : w.re = c := by simp [w]
  have hwIm : w.im = T := by simp [w]
  have hTT : -T <= T := by linarith
  have hC := Complex.integral_boundary_rect_eq_zero_of_differentiableOn f z w (by
    intro s hs
    change And (Membership.mem (Set.uIcc z.re w.re) s.re)
      (Membership.mem (Set.uIcc z.im w.im) s.im) at hs
    simp only [hzRe, hwRe, hzIm, hwIm, Set.uIcc_of_le hSC,
      Set.uIcc_of_le hTT, Set.mem_Icc] at hs
    exact (hDiff s hs.1.1 hs.1.2 hs.2.1 hs.2.2).differentiableWithinAt)
  simp only [hzRe, hwRe, hzIm, hwIm, smul_eq_mul] at hC
  let A : Complex := intervalIntegral (fun u : Real =>
    f ((u : Complex) + ((-T : Real) : Complex) * Complex.I)) sigma c MeasureTheory.volume
  let B : Complex := intervalIntegral (fun u : Real =>
    f ((u : Complex) + (T : Complex) * Complex.I)) sigma c MeasureTheory.volume
  let L : Complex := intervalIntegral (fun t : Real =>
    f ((sigma : Complex) + (t : Complex) * Complex.I)) (-T) T MeasureTheory.volume
  let R : Complex := intervalIntegral (fun t : Real =>
    f ((c : Complex) + (t : Complex) * Complex.I)) (-T) T MeasureTheory.volume
  change (A - B + Complex.I * R) - Complex.I * L = 0 at hC
  have hE : Complex.I * R = Complex.I * L - (A - B) := by
    apply eq_sub_of_add_eq
    calc
      _ = A - B + Complex.I * R := add_comm _ _
      _ = _ := sub_eq_zero.mp hC
  have hTri := norm_sub_le (Complex.I * L) (A - B)
  rw [<- hE] at hTri
  simp only [norm_mul, Complex.norm_I, one_mul] at hTri
  have hAB := norm_sub_le A B
  have hNorm : norm R <= norm L + norm A + norm B := by linarith
  have hL := lpf_vertical_integral_envelope
    (fun t : Real => f ((sigma : Complex) + (t : Complex) * Complex.I))
    C T hT hLeftInt hLeft
  have hA := lpf_horizontal_integral_envelope
    (fun u : Real => f ((u : Complex) + ((-T : Real) : Complex) * Complex.I))
    H sigma c hSC hBottomInt hBottom
  have hB := lpf_horizontal_integral_envelope
    (fun u : Real => f ((u : Complex) + (T : Complex) * Complex.I))
    H sigma c hSC hTopInt hTop
  change norm L <= _ at hL
  change norm A <= _ at hA
  change norm B <= _ at hB
  change norm R <= _
  linarith only [hNorm, hL, hA, hB]

end PrimeFactorOscillations.QRH


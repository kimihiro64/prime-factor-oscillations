/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Assembly.DetectorPackets.MobiusWindowMellin

/-!
# MobiusWindowShift

Maintained extraction of completed detector/packet proof components.
All original theorem hypotheses and retained proof bodies are preserved.
This module alone asserts no improved zero-free boundary.
-/

set_option autoImplicit false
set_option Elab.async false

/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described by LICENSE.
Authors: Prime Factor Oscillations contributors
-/


noncomputable section
open scoped BigOperators Classical
open MeasureTheory
open PrimeFactorOscillations.RationalInverseLine

namespace PrimeFactorOscillations.MobiusWindow

theorem quadratic_cube_le_sixth (t : Real) :
    (1 + t ^ 2) ^ 3 <= (1 + abs t) ^ 6 := by
  have hbase : 1 + t ^ 2 <= (1 + abs t) ^ 2 := by
    nlinarith [sq_abs t, abs_nonneg t]
  have hsq := mul_le_mul hbase hbase
    (show 0 <= 1 + t ^ 2 by positivity) (sq_nonneg (1 + abs t))
  have hc := mul_le_mul hsq hbase
    (show 0 <= 1 + t ^ 2 by positivity)
    (show 0 <= (1 + abs t) ^ 2 * (1 + abs t) ^ 2 by positivity)
  nlinarith only [hc]

def mellinInverseData {q : Nat} [NeZero q] (chi : DirichletCharacter Complex q)
    (W : Real -> Complex) (s : Complex) : Complex :=
  mellin W s * regularizedInverse chi s

def windowIntegrand {q : Nat} [NeZero q] (chi : DirichletCharacter Complex q)
    (W : Real -> Complex) (y : Real) (s : Complex) : Complex :=
  mellin W s * (y : Complex) ^ s * regularizedInverse chi s

theorem mellinInverseData_strip_weighted_bound {q : Nat}
    (chi : DirichletCharacter Complex q) (hq : 0 < q)
    (W : Real -> Complex) (lo hi : Real) (hlo : 0 < lo)
    (hsupp : Function.support W <= Set.Icc lo hi)
    (hW : ContDiff Real ((Top.top : ENat) : WithTop ENat) W)
    (a : Real) (ha : (7 / 8 : Real) < a) :
    letI : NeZero q := NeZero.mk (Nat.ne_of_gt hq)
    Exists (fun A : Real => 0 <= A /\
      forall sigma : Real, Membership.mem (Set.Icc a 2) sigma -> forall t : Real,
        (1 + t ^ 2) * norm (mellinInverseData chi W
          ((sigma : Complex) + (t : Complex) * Complex.I)) <= A) := by
  letI : NeZero q := NeZero.mk (Nat.ne_of_gt hq)
  choose C hC using OAI.CubicReflectionKernel.compact_source_mellin_strip_decay
    W lo hi hlo hsupp hW a 2 6
  choose K hK using regularizedInverse_strip_bound chi hq a ha
  refine Exists.intro (K * C) (And.intro (mul_nonneg hK.1 hC.1.le) ?_)
  intro sigma hsigma t
  let s : Complex := (sigma : Complex) + (t : Complex) * Complex.I
  have hsre : s.re = sigma := by simp [s]
  have hsim : s.im = t := by simp [s]
  have hI := hK.2 s (by rw [hsre]; exact hsigma.1) (by rw [hsre]; exact hsigma.2)
  rw [hsim] at hI
  have hM := hC.2 sigma hsigma t
  change (1 + abs t) ^ 6 * norm (mellin W s) <= C at hM
  have hM3 : (1 + t ^ 2) ^ 3 * norm (mellin W s) <= C :=
    (mul_le_mul_of_nonneg_right (quadratic_cube_le_sixth t) (norm_nonneg _)).trans hM
  change (1 + t ^ 2) * norm (mellinInverseData chi W s) <= _
  calc
    _ = ((1 + t ^ 2) * norm (mellin W s)) * norm (regularizedInverse chi s) := by
      rw [mellinInverseData, norm_mul]
      ring
    _ <= ((1 + t ^ 2) * norm (mellin W s)) * (K * (1 + t ^ 2) ^ 2) :=
      mul_le_mul_of_nonneg_left hI (by positivity)
    _ = K * ((1 + t ^ 2) ^ 3 * norm (mellin W s)) := by ring
    _ <= K * C := mul_le_mul_of_nonneg_left hM3 hK.1

theorem mellinInverseData_strip_decay {q : Nat}
    (chi : DirichletCharacter Complex q) (hq : 0 < q)
    (W : Real -> Complex) (lo hi : Real) (hlo : 0 < lo)
    (hsupp : Function.support W <= Set.Icc lo hi)
    (hW : ContDiff Real ((Top.top : ENat) : WithTop ENat) W)
    (a : Real) (ha : (7 / 8 : Real) < a) :
    letI : NeZero q := NeZero.mk (Nat.ne_of_gt hq)
    Exists (fun A : Real => 0 <= A /\
      forall sigma : Real, Membership.mem (Set.Icc a 2) sigma -> forall t : Real,
        norm (mellinInverseData chi W
          ((sigma : Complex) + (t : Complex) * Complex.I)) <= A / (1 + t ^ 2)) := by
  letI : NeZero q := NeZero.mk (Nat.ne_of_gt hq)
  choose A hA using mellinInverseData_strip_weighted_bound chi hq W lo hi hlo hsupp hW a ha
  refine Exists.intro A (And.intro hA.1 ?_)
  intro sigma hsigma t
  calc
    _ = ((1 + t ^ 2) * norm (mellinInverseData chi W
        ((sigma : Complex) + (t : Complex) * Complex.I))) / (1 + t ^ 2) := by
      field_simp
    _ <= _ := div_le_div_of_nonneg_right (hA.2 sigma hsigma t) (by positivity)

theorem windowIntegrand_differentiableAt {q : Nat}
    (chi : DirichletCharacter Complex q) (hq : 0 < q)
    (W : Real -> Complex) (lo hi : Real) (hlo : 0 < lo)
    (hsupp : Function.support W <= Set.Icc lo hi)
    (hW : ContDiff Real ((Top.top : ENat) : WithTop ENat) W)
    (y : Real) (hy : 0 < y) (s : Complex) (hs : (7 / 8 : Real) < s.re) :
    letI : NeZero q := NeZero.mk (Nat.ne_of_gt hq)
    DifferentiableAt Complex (windowIntegrand chi W y) s := by
  letI : NeZero q := NeZero.mk (Nat.ne_of_gt hq)
  exact (((OAI.CubicReflectionKernel.compact_source_mellin_differentiable
    W lo hi hlo hsupp hW) s).mul
      (differentiableAt_id.const_cpow (Or.inl (Complex.ofReal_ne_zero.mpr (ne_of_gt hy))))).mul
        (regularizedInverse_differentiableAt chi hq s hs)

theorem windowIntegrand_norm {q : Nat} [NeZero q]
    (chi : DirichletCharacter Complex q) (W : Real -> Complex)
    (y : Real) (hy : 0 < y) (sigma t : Real) :
    norm (windowIntegrand chi W y ((sigma : Complex) + (t : Complex) * Complex.I)) =
      y ^ sigma * norm (mellinInverseData chi W
        ((sigma : Complex) + (t : Complex) * Complex.I)) := by
  unfold windowIntegrand mellinInverseData
  rw [norm_mul, norm_mul, norm_mul,
    OAI.CompletedGauss.positive_cpow_vertical_norm y sigma t hy]
  ring

theorem windowIntegrand_vertical_integrable {q : Nat}
    (chi : DirichletCharacter Complex q) (hq : 0 < q)
    (W : Real -> Complex) (lo hi : Real) (hlo : 0 < lo)
    (hsupp : Function.support W <= Set.Icc lo hi)
    (hW : ContDiff Real ((Top.top : ENat) : WithTop ENat) W)
    (sigma : Real) (hsigma : (7 / 8 : Real) < sigma) (hsigma2 : sigma <= 2)
    (y : Real) (hy : 0 < y) :
    letI : NeZero q := NeZero.mk (Nat.ne_of_gt hq)
    Integrable (fun t : Real => windowIntegrand chi W y
      ((sigma : Complex) + (t : Complex) * Complex.I)) := by
  letI : NeZero q := NeZero.mk (Nat.ne_of_gt hq)
  choose A hA using mellinInverseData_strip_decay chi hq W lo hi hlo hsupp hW sigma hsigma
  have hcont : Continuous (fun t : Real => windowIntegrand chi W y
      ((sigma : Complex) + (t : Complex) * Complex.I)) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    have hline : ContinuousAt (fun u : Real =>
        (sigma : Complex) + (u : Complex) * Complex.I) t := by fun_prop
    exact (windowIntegrand_differentiableAt chi hq W lo hi hlo hsupp hW y hy
      ((sigma : Complex) + (t : Complex) * Complex.I) (by simpa using hsigma)).continuousAt.comp
        (f := fun u : Real => (sigma : Complex) + (u : Complex) * Complex.I) hline
  have hmajor := integrable_inv_one_add_sq.const_mul (y ^ sigma * A)
  apply hmajor.mono' hcont.aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun t => by
    rw [windowIntegrand_norm chi W y hy sigma t]
    calc
      _ <= y ^ sigma * (A / (1 + t ^ 2)) :=
        mul_le_mul_of_nonneg_left (hA.2 sigma (And.intro le_rfl hsigma2) t)
          (Real.rpow_nonneg hy.le _)
      _ = _ := by rw [div_eq_mul_inv]; ring)

theorem smoothWindow_mellin_shift {q : Nat}
    (chi : DirichletCharacter Complex q) (hq : 0 < q)
    (W : Real -> Complex) (lo hi : Real) (hlo : 0 < lo)
    (hsupp : Function.support W <= Set.Icc lo hi)
    (hW : ContDiff Real ((Top.top : ENat) : WithTop ENat) W)
    (a : Real) (ha : (7 / 8 : Real) < a) (ha2 : a <= 2)
    (y : Real) (hy : 0 < y) :
    letI : NeZero q := NeZero.mk (Nat.ne_of_gt hq)
    smoothWindow chi W y = (1 / (2 * Real.pi) : Complex) *
      integral volume (fun t : Real =>
        windowIntegrand chi W y ((a : Complex) + (t : Complex) * Complex.I)) := by
  letI : NeZero q := NeZero.mk (Nat.ne_of_gt hq)
  choose A hA using mellinInverseData_strip_decay chi hq W lo hi hlo hsupp hW a ha
  have hright : smoothWindow chi W y = (1 / (2 * Real.pi) : Complex) *
      integral volume (fun t : Real =>
        windowIntegrand chi W y ((2 : Complex) + (t : Complex) * Complex.I)) := by
    rw [smoothWindow_mellin_right chi hq W lo hi hlo hsupp hW y hy]
    congr 1
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun t => by
      dsimp only [windowIntegrand]
      rw [regularizedInverse_eq_inv chi hq _ (by simp)
        (by intro h; have hr := congrArg Complex.re h; norm_num at hr)])
  have hshift : integral volume (fun t : Real =>
      windowIntegrand chi W y ((a : Complex) + (t : Complex) * Complex.I)) =
      integral volume (fun t : Real =>
        windowIntegrand chi W y ((2 : Complex) + (t : Complex) * Complex.I)) := by
    apply OAI.VerticalContourShift.integral_eq_of_strip_decay
      (windowIntegrand chi W y) a 2 ((y ^ a + y ^ (2 : Real)) * A) ha2
    . intro s hslo _
      exact windowIntegrand_differentiableAt chi hq W lo hi hlo hsupp hW y hy s
        (ha.trans_le hslo)
    . exact windowIntegrand_vertical_integrable chi hq W lo hi hlo hsupp hW a ha ha2 y hy
    . exact windowIntegrand_vertical_integrable chi hq W lo hi hlo hsupp hW
        2 (by norm_num) le_rfl y hy
    . intro sigma hsigma t
      rw [windowIntegrand_norm chi W y hy sigma t]
      have hpow := OAI.VerticalContourShift.rpow_between_endpoints
        y a 2 sigma hy hsigma.1 hsigma.2
      calc
        _ <= (y ^ a + y ^ (2 : Real)) * norm (mellinInverseData chi W
            ((sigma : Complex) + (t : Complex) * Complex.I)) :=
          mul_le_mul_of_nonneg_right hpow (norm_nonneg _)
        _ <= (y ^ a + y ^ (2 : Real)) * (A / (1 + t ^ 2)) :=
          mul_le_mul_of_nonneg_left (hA.2 sigma hsigma t) (by positivity)
        _ = _ := by ring
  exact hright.trans (congrArg (fun z : Complex => (1 / (2 * Real.pi) : Complex) * z)
    hshift.symm)

end PrimeFactorOscillations.MobiusWindow

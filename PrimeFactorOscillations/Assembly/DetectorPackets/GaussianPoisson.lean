/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import OAI.NumberTheory.DirichletL.Poisson.EisensteinLattice
import PrimeFactorOscillations.Assembly.DetectorPackets.GaussianMobiusDivisors

/-!
# GaussianPoisson

Maintained extraction of completed detector/packet proof components.
All original theorem hypotheses and retained proof bodies are preserved.
This module alone asserts no improved zero-free boundary.
-/

set_option autoImplicit false
set_option Elab.async false

/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

/-!
# Gaussian smooth Poisson input for the centered Mobius packet

The generic complex-lattice Poisson interface is reused from the pinned OAI
source fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb. Its affine theorem is valid
for every complex real-linear lattice, independently of its Eisenstein uses.
Here the lattice is exactly Z[i], with covolume one.
-/


noncomputable section
namespace PrimeFactorOscillations.GaussianPoisson

open MeasureTheory
open OAI.EisensteinSchwartzPoisson
open GaussianMobiusDivisors
open scoped BigOperators FourierTransform SchwartzMap

def point (p : Prod Int Int) : Complex :=
  complexPoint (p.1 : Real) (p.2 : Real)

def embed (z : G) : Complex :=
  complexPoint (z.re : Real) (z.im : Real)

theorem point_norm_sq (p : Prod Int Int) :
    norm (point p) ^ 2 = (p.1 : Real) ^ 2 + (p.2 : Real) ^ 2 := by
  rw [Complex.sq_norm]
  simp only [point, complexPoint, Complex.normSq_apply]
  ring

theorem point_norm_sq_one_le (p : Prod Int Int) (hp : Not (p = 0)) :
    1 <= norm (point p) ^ 2 := by
  have hpos : (0 : Int) < p.1 ^ 2 + p.2 ^ 2 := by
    by_cases h1 : p.1 = 0
    . have h2 : Not (p.2 = 0) := by
        intro h2
        exact hp (Prod.ext h1 h2)
      simpa only [h1, zero_pow (by decide : Not (2 = 0)), zero_add] using
        (sq_pos_of_ne_zero h2)
    . have hsq := sq_pos_of_ne_zero h1
      have hs2 := sq_nonneg p.2
      linarith
  have hle : (1 : Int) <= p.1 ^ 2 + p.2 ^ 2 :=
    Int.add_one_le_iff.mpr hpos
  rw [point_norm_sq]
  exact_mod_cast hle

def weight (p : Prod Int Int) : Real :=
  Inv.inv (1 + (p.1 : Real) ^ 2) *
    Inv.inv (1 + (p.2 : Real) ^ 2)

theorem weight_nonnegative (p : Prod Int Int) : 0 <= weight p := by
  unfold weight
  positivity

theorem weight_summable : Summable weight := by
  exact summable_int_cauchy_product

def rescale (f : SchwartzMap Complex Complex) (X : Real) (hX : 0 < X) :
    SchwartzMap Complex Complex :=
  affinePullback f
    (complexMulEquiv (Inv.inv (Real.sqrt X : Complex)) (by
      exact inv_ne_zero (Complex.ofReal_ne_zero.mpr
        (ne_of_gt (Real.sqrt_pos.mpr hX))))) 0

theorem rescale_apply (f : SchwartzMap Complex Complex) (X : Real) (hX : 0 < X)
    (z : Complex) :
    rescale f X hX z = f (Inv.inv (Real.sqrt X : Complex) * z) := by
  simp only [rescale, affinePullback_apply, complexMulEquiv_apply, add_zero]

theorem rescaled_poisson (f : SchwartzMap Complex Complex) (X : Real) (hX : 0 < X) :
    (tsum fun p : Prod Int Int => f (Inv.inv (Real.sqrt X : Complex) * point p)) =
      X * (tsum fun p : Prod Int Int => (FourierTransform.fourier f)
        ((Real.sqrt X : Complex) * point p)) := by
  let c : Complex := Inv.inv (Real.sqrt X : Complex)
  have hc : Not (c = 0) := by
    dsimp only [c]
    exact inv_ne_zero (Complex.ofReal_ne_zero.mpr
      (ne_of_gt (Real.sqrt_pos.mpr hX)))
  let A := complexMulEquiv c hc
  have hj : inverseJacobian A = X := by
    dsimp only [A, inverseJacobian]
    rw [complexMulEquiv_det]
    dsimp only [c]
    rw [Complex.normSq_inv, Complex.normSq_ofReal, <- pow_two, Real.sq_sqrt hX.le, inv_inv,
      abs_of_pos hX]
  have hd (z : Complex) : dualMap A z = (Real.sqrt X : Complex) * z := by
    dsimp only [A]
    rw [dual_mul_apply]
    simp [c]
  have hh := affine_lattice_poisson f A 0
  rw [hj] at hh
  simp only [hd] at hh
  change (tsum fun p : Prod Int Int => f (c * point p)) =
    X * (tsum fun p : Prod Int Int => (FourierTransform.fourier f)
      ((Real.sqrt X : Complex) * point p))
  simpa [A, point, Algebra.smul_def] using hh

theorem gaussian_rescaled_poisson (f : SchwartzMap Complex Complex)
    (X : Real) (hX : 0 < X) :
    (tsum fun z : G => f (Inv.inv (Real.sqrt X : Complex) * embed z)) =
      X * (tsum fun p : Prod Int Int => (FourierTransform.fourier f)
        ((Real.sqrt X : Complex) * point p)) := by
  calc
    _ = tsum (fun p : Prod Int Int =>
        f (Inv.inv (Real.sqrt X : Complex) * point p)) := by
      exact (integerCoordinates.toEquiv.symm.tsum_eq
        (fun z : G => f (Inv.inv (Real.sqrt X : Complex) * embed z))).symm
    _ = _ := rescaled_poisson f X hX


@[simp] theorem point_zero : point (0 : Prod Int Int) = 0 := by
  apply Complex.ext <;> simp [point, complexPoint]

def weightMass : Real := tsum weight

theorem weightMass_nonnegative : 0 <= weightMass :=
  tsum_nonneg weight_nonnegative

theorem point_real_mul (r : Real) (p : Prod Int Int) :
    complexPoint (r * (p.1 : Real)) (r * (p.2 : Real)) =
      (r : Complex) * point p := by
  apply Complex.ext <;> simp [point, complexPoint]

theorem dilate_norm_le (f : SchwartzMap Complex Complex) (r : Real)
    (hr : 1 <= r) (p : Prod Int Int) :
    norm (f ((r : Complex) * point p)) <= planeDecayConstant f * weight p := by
  let x : Real := p.1
  let y : Real := p.2
  have hx : 0 < 1 + x ^ 2 := by positivity
  have hy : 0 < 1 + y ^ 2 := by positivity
  have hr2 : 1 <= r ^ 2 := by nlinarith
  have hdx : 1 + x ^ 2 <= 1 + (r * x) ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_right hr2 (sq_nonneg x)]
  have hdy : 1 + y ^ 2 <= 1 + (r * y) ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_right hr2 (sq_nonneg y)]
  have hden : (1 + x ^ 2) * (1 + y ^ 2) <=
      (1 + (r * x) ^ 2) * (1 + (r * y) ^ 2) :=
    mul_le_mul hdx hdy (le_of_lt hy) (by positivity)
  have hs := plane_schwartz_product_decay f (r * x) (r * y)
  rw [show complexPoint (r * x) (r * y) = (r : Complex) * point p from
    point_real_mul r p] at hs
  have heq : ((1 + x ^ 2) * (1 + y ^ 2)) *
      (planeDecayConstant f * weight p) = planeDecayConstant f := by
    dsimp only [weight, x, y]
    field_simp
  have hb := (mul_le_mul_of_nonneg_right hden
    (norm_nonneg (f ((r : Complex) * point p)))).trans hs
  by_contra hn
  have hh := mul_pos (mul_pos hx hy) (sub_pos.mpr (lt_of_not_ge hn))
  nlinarith

theorem dilate_nonzero_norm_le (f : SchwartzMap Complex Complex) (X : Real)
    (hX : 1 <= X) (p : Prod Int Int) (hp : Not (p = 0)) :
    norm (f ((Real.sqrt X : Complex) * point p)) <=
      (2 * planeDecayConstant f / X) * weight p := by
  let x : Real := p.1
  let y : Real := p.2
  have hX0 : 0 < X := by linarith
  have hx : 0 < 1 + x ^ 2 := by positivity
  have hy : 0 < 1 + y ^ 2 := by positivity
  have hr : 1 <= x ^ 2 + y ^ 2 := by
    simpa only [point_norm_sq] using point_norm_sq_one_le p hp
  have hs := plane_schwartz_product_decay f (Real.sqrt X * x) (Real.sqrt X * y)
  rw [show complexPoint (Real.sqrt X * x) (Real.sqrt X * y) =
    (Real.sqrt X : Complex) * point p from point_real_mul (Real.sqrt X) p] at hs
  simp only [mul_pow, Real.sq_sqrt hX0.le] at hs
  have hXsq : X <= X ^ 2 := by nlinarith
  have huv : 0 <= x ^ 2 * y ^ 2 := by positivity
  have hXR := mul_le_mul_of_nonneg_left hr hX0.le
  have hXuv := mul_le_mul_of_nonneg_right hXsq huv
  have hden : X * ((1 + x ^ 2) * (1 + y ^ 2)) <=
      2 * ((1 + X * x ^ 2) * (1 + X * y ^ 2)) := by
    nlinarith [mul_nonneg hX0.le huv]
  have heq : (X * ((1 + x ^ 2) * (1 + y ^ 2))) *
      ((2 * planeDecayConstant f / X) * weight p) = 2 * planeDecayConstant f := by
    dsimp only [weight, x, y]
    field_simp
  have hb : (X * ((1 + x ^ 2) * (1 + y ^ 2))) *
      norm (f ((Real.sqrt X : Complex) * point p)) <= 2 * planeDecayConstant f := by
    nlinarith [mul_le_mul_of_nonneg_right hden
      (norm_nonneg (f ((Real.sqrt X : Complex) * point p)))]
  by_contra hn
  have hh := mul_pos (mul_pos hX0 (mul_pos hx hy))
    (sub_pos.mpr (lt_of_not_ge hn))
  nlinarith

theorem large_scale_error (f : SchwartzMap Complex Complex) (X : Real) (hX : 1 <= X) :
    norm ((tsum fun p : Prod Int Int => f (Inv.inv (Real.sqrt X : Complex) * point p)) -
      (X : Complex) * (FourierTransform.fourier f) 0) <=
      2 * planeDecayConstant (FourierTransform.fourier f) * weightMass := by
  classical
  let F : SchwartzMap Complex Complex := FourierTransform.fourier f
  have hX0 : 0 < X := by linarith
  let B : Real := 2 * planeDecayConstant F / X
  let tail : Prod Int Int -> Complex := fun p =>
    if p = 0 then 0 else F ((Real.sqrt X : Complex) * point p)
  have hB : 0 <= B := by
    exact div_nonneg (mul_nonneg (by norm_num) (planeDecayConstant_nonneg F)) hX0.le
  have ht (p : Prod Int Int) : norm (tail p) <= B * weight p := by
    by_cases hp : p = 0
    . simp only [tail, hp, ite_eq_left rfl, norm_zero]
      exact mul_nonneg hB (weight_nonnegative 0)
    . simpa only [tail, ite_eq_right hp] using dilate_nonzero_norm_le F X hX p hp
  have hn : Summable (fun p => norm (tail p)) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) ht (weight_summable.mul_left B)
  have hb := (norm_tsum_le_tsum_norm hn).trans
    (hn.tsum_le_tsum ht (weight_summable.mul_left B))
  rw [tsum_mul_left] at hb
  change norm (tsum tail) <= B * weightMass at hb
  let A := complexMulEquiv (Real.sqrt X : Complex)
    (Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.mpr hX0)))
  have hsn := plane_lattice_summable_norm (affinePullback F A 0)
  have hss : Summable (fun p : Prod Int Int => F ((Real.sqrt X : Complex) * point p)) := by
    apply Summable.of_norm
    simpa only [A, affinePullback_apply, complexMulEquiv_apply, add_zero, point] using hsn
  have hsplit : (tsum fun p : Prod Int Int => F ((Real.sqrt X : Complex) * point p)) =
      F 0 + tsum tail := by
    simpa only [point_zero, mul_zero] using hss.tsum_eq_add_tsum_ite (0 : Prod Int Int)
  have heq :
      (tsum fun p : Prod Int Int => f (Inv.inv (Real.sqrt X : Complex) * point p)) -
        (X : Complex) * F 0 = (X : Complex) * tsum tail := by
    rw [rescaled_poisson f X hX0, hsplit]
    ring
  rw [heq, norm_mul, Complex.norm_real, Real.norm_of_nonneg hX0.le]
  calc
    X * norm (tsum tail) <= X * (B * weightMass) :=
      mul_le_mul_of_nonneg_left hb hX0.le
    _ = 2 * planeDecayConstant F * weightMass := by
      dsimp only [B]
      field_simp

theorem small_scale_sum_bound (f : SchwartzMap Complex Complex) (X : Real)
    (hX : 0 < X) (hX1 : X <= 1) :
    norm (tsum fun p : Prod Int Int => f (Inv.inv (Real.sqrt X : Complex) * point p)) <=
      planeDecayConstant f * weightMass := by
  have hs : 0 < Real.sqrt X := Real.sqrt_pos.mpr hX
  have hs1 : Real.sqrt X <= 1 := by nlinarith [Real.sq_sqrt hX.le]
  let r : Real := Inv.inv (Real.sqrt X)
  have hr0 : 0 < r := inv_pos.mpr hs
  have hmul : Real.sqrt X * r = 1 := by dsimp only [r]; field_simp
  have hr : 1 <= r := by
    nlinarith [mul_le_mul_of_nonneg_right hs1 hr0.le]
  have hp (p : Prod Int Int) :
      norm (f (Inv.inv (Real.sqrt X : Complex) * point p)) <=
        planeDecayConstant f * weight p := by
    simpa only [r, Complex.ofReal_inv] using dilate_norm_le f r hr p
  have hn : Summable (fun p : Prod Int Int =>
      norm (f (Inv.inv (Real.sqrt X : Complex) * point p))) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hp
      (weight_summable.mul_left (planeDecayConstant f))
  have hb := (norm_tsum_le_tsum_norm hn).trans
    (hn.tsum_le_tsum hp (weight_summable.mul_left (planeDecayConstant f)))
  simpa only [tsum_mul_left, weightMass] using hb

def poissonBound (f : SchwartzMap Complex Complex) : Real :=
  (planeDecayConstant f + 2 * planeDecayConstant (FourierTransform.fourier f)) *
    weightMass + norm ((FourierTransform.fourier f) 0)

/-- Uniform in the positive scale, with no zero-free hypothesis. -/
theorem uniform_pairs_error (f : SchwartzMap Complex Complex) (X : Real) (hX : 0 < X) :
    norm ((tsum fun p : Prod Int Int => f (Inv.inv (Real.sqrt X : Complex) * point p)) -
      (X : Complex) * (FourierTransform.fourier f) 0) <= poissonBound f := by
  have hC := planeDecayConstant_nonneg f
  have hF := planeDecayConstant_nonneg (FourierTransform.fourier f)
  have hS := weightMass_nonnegative
  by_cases hX1 : 1 <= X
  . apply (large_scale_error f X hX1).trans
    dsimp only [poissonBound]
    nlinarith [mul_nonneg hC hS, norm_nonneg ((FourierTransform.fourier f) 0)]
  . have hx1 : X <= 1 := le_of_lt (lt_of_not_ge hX1)
    have hb := norm_sub_le
      (tsum fun p : Prod Int Int => f (Inv.inv (Real.sqrt X : Complex) * point p))
      ((X : Complex) * (FourierTransform.fourier f) 0)
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hX.le] at hb
    have hm := mul_le_mul_of_nonneg_right hx1 (norm_nonneg ((FourierTransform.fourier f) 0))
    have hs := small_scale_sum_bound f X hX hx1
    dsimp only [poissonBound]
    nlinarith [mul_nonneg hF hS]

theorem uniform_gaussian_error (f : SchwartzMap Complex Complex) (X : Real) (hX : 0 < X) :
    norm ((tsum fun z : G => f (Inv.inv (Real.sqrt X : Complex) * embed z)) -
      (X : Complex) * (FourierTransform.fourier f) 0) <= poissonBound f := by
  have heq : (tsum fun z : G => f (Inv.inv (Real.sqrt X : Complex) * embed z)) =
      tsum (fun p : Prod Int Int => f (Inv.inv (Real.sqrt X : Complex) * point p)) :=
    (integerCoordinates.toEquiv.symm.tsum_eq
      (fun z : G => f (Inv.inv (Real.sqrt X : Complex) * embed z))).symm
  rw [heq]
  exact uniform_pairs_error f X hX

end PrimeFactorOscillations.GaussianPoisson

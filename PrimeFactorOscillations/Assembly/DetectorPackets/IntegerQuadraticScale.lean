/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Assembly.DetectorPackets.IntegerQuadraticPoissonInteger

/-!
# IntegerQuadraticScale

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
# Exact positive-scale quadratic Poisson formula

The dilation is a real Schwartz function composition. Its Fourier
Jacobian is proved from the pushforward of Lebesgue measure. The final
formula retains T/q and the full raw Gauss factor for every positive T.
-/


noncomputable section
namespace PrimeFactorOscillations.IntegerQuadraticScale

open IntegerQuadraticCharacter IntegerQuadraticInitial IntegerQuadraticPoissonInteger
open MeasureTheory

def scaleEquiv (a : Real) (ha : Not (a = 0)) :
    ContinuousLinearEquiv (RingHom.id Real) Real Real where
  toFun x := a * x
  invFun x := x / a
  map_add' x y := by ring
  map_smul' r x := by simp only [smul_eq_mul, RingHom.id_apply]; ring
  left_inv x := by field_simp
  right_inv x := by field_simp
  continuous_toFun := continuous_const.mul continuous_id
  continuous_invFun := continuous_id.div_const a

def dilate (a : Real) (ha : Not (a = 0)) (f : SchwartzMap Real Complex) :
    SchwartzMap Real Complex :=
  SchwartzMap.compCLMOfContinuousLinearEquiv Real (scaleEquiv a ha) f

theorem dilate_apply (a : Real) (ha : Not (a = 0))
    (f : SchwartzMap Real Complex) (x : Real) :
    dilate a ha f x = f (a * x) := rfl

theorem integral_scale (a : Real) (ha : 0 < a) (F : Real -> Complex) :
    integral volume (fun x : Real => F (a * x)) =
      ((a ^ (-1 : Int) : Real) : Complex) * integral volume F := by
  have hmap :
      integral (Measure.map (scaleEquiv a (ne_of_gt ha)) volume) F =
        integral volume (fun x : Real => F (scaleEquiv a (ne_of_gt ha) x)) :=
    (scaleEquiv a (ne_of_gt ha)).toHomeomorph.measurableEmbedding.integral_map F
  change integral (Measure.map (fun x : Real => a * x) volume) F =
    integral volume (fun x : Real => F (a * x)) at hmap
  rw [Real.map_volume_mul_left (ne_of_gt ha), integral_smul_measure,
    ENNReal.toReal_ofReal (abs_nonneg _), abs_of_pos (inv_pos.mpr ha)] at hmap
  simpa only [zpow_neg_one, Algebra.smul_def, Complex.coe_algebraMap] using hmap.symm

theorem fourier_scale (a : Real) (ha : 0 < a) (f : Real -> Complex) (t : Real) :
    FourierTransform.fourier (fun x : Real => f (a * x)) t =
      ((a ^ (-1 : Int) : Real) : Complex) * FourierTransform.fourier f (t / a) := by
  let F : Real -> Complex := fun y =>
    Complex.exp (((-2 * Real.pi * y * (t / a) : Real) : Complex) * Complex.I) * f y
  have harg (x : Real) :
      -2 * Real.pi * x * t = -2 * Real.pi * (a * x) * (t / a) := by
    field_simp
  rw [Real.fourier_real_eq_integral_exp_smul,
    Real.fourier_real_eq_integral_exp_smul]
  simp only [smul_eq_mul]
  calc
    _ = integral volume (fun x : Real => F (a * x)) := by
      congr 1
      funext x
      rw [harg x]
    _ = ((a ^ (-1 : Int) : Real) : Complex) * integral volume F := integral_scale a ha F
    _ = _ := rfl

theorem fourier_dilate (a : Real) (ha : 0 < a)
    (f : SchwartzMap Real Complex) (t : Real) :
    (FourierTransform.fourier (dilate a (ne_of_gt ha) f)) t =
      ((a ^ (-1 : Int) : Real) : Complex) * (FourierTransform.fourier f) (t / a) := by
  change ((FourierTransform.fourier (dilate a (ne_of_gt ha) f)) : Real -> Complex) t = _
  rw [SchwartzMap.fourier_coe]
  change FourierTransform.fourier (fun x : Real => f (a * x)) t = _
  exact fourier_scale a ha f t

theorem dilate_support_bound (a : Real) (ha : 0 < a)
    (f : SchwartzMap Real Complex) (B : Nat)
    (hB : forall x : Real, (B : Real) < abs x -> f x = 0) :
    exists K : Nat, forall x : Real, (K : Real) < abs x ->
      dilate a (ne_of_gt ha) f x = 0 := by
  choose K hK using exists_nat_gt ((B : Real) / a)
  refine Exists.intro K ?_
  intro x hx
  rw [dilate_apply]
  apply hB
  rw [abs_mul, abs_of_pos ha]
  have hm : ((B : Real) / a) * a = (B : Real) := by field_simp
  nlinarith

theorem poisson_scaled (q : Nat) [NeZero q] (hq : Good q)
    (T : Real) (hT : 0 < T) (f : SchwartzMap Real Complex) (B : Nat)
    (hB : forall x : Real, (B : Real) < abs x -> f x = 0) :
    tsum (fun z : Int => character q hq.1 (z : ZMod q) * f ((z : Real) / T)) =
      (((T / (q : Real) : Real) : Complex) *
        gaussSum (character q hq.1) ZMod.stdAddChar) *
          tsum (fun h : Int => character q hq.1 (h : ZMod q) *
            (FourierTransform.fourier f) ((h : Real) * T / (q : Real))) := by
  have hqpos : (0 : Real) < (q : Real) := by exact_mod_cast NeZero.pos q
  have ha : 0 < (q : Real) / T := div_pos hqpos hT
  let a : Real := (q : Real) / T
  let fT : SchwartzMap Real Complex := dilate a (ne_of_gt ha) f
  choose K hK using dilate_support_bound a ha f B hB
  have hp := integer_poisson q hq fT K hK
  have hl (z : Int) : fT ((z : Real) / (q : Real)) = f ((z : Real) / T) := by
    rw [dilate_apply]
    congr 1
    dsimp [a]
    field_simp
  have hr (h : Int) :
      (FourierTransform.fourier fT) (h : Real) =
        (((T / (q : Real) : Real) : Complex) *
          (FourierTransform.fourier f) ((h : Real) * T / (q : Real))) := by
    rw [fourier_dilate a ha f]
    have hi : a ^ (-1 : Int) = T / (q : Real) := by
      dsimp [a]
      simp only [zpow_neg_one, inv_div]
    have ht : (h : Real) / a = (h : Real) * T / (q : Real) := by
      dsimp [a]
      field_simp
    rw [hi, ht]
  simp_rw [hl, hr] at hp
  rw [hp]
  have hrearrange :
      (fun h : Int => character q hq.1 (h : ZMod q) *
        (((T / (q : Real) : Real) : Complex) *
          (FourierTransform.fourier f) ((h : Real) * T / (q : Real)))) =
      (fun h : Int => (((T / (q : Real) : Real) : Complex) *
        (character q hq.1 (h : ZMod q) *
          (FourierTransform.fourier f) ((h : Real) * T / (q : Real))))) := by
    funext h
    ring
  rw [hrearrange, tsum_mul_left]
  ring

end PrimeFactorOscillations.IntegerQuadraticScale


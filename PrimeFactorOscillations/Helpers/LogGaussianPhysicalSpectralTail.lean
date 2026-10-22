/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.LogGaussianLeftZeroError

/-!
# Exact physical spectral tail and the full Gaussian moment

The logarithmic substitution is proved for every complex rho.
No zero term or phase is removed, and the full moment uses the
paper's variance and normalization.
-/

set_option autoImplicit false
set_option Elab.async false

open MeasureTheory Set Filter

namespace PrimeFactorOscillations.PrimeClassDeletion

theorem logGaussianWeightedWave_integral (V tau : Real) (rho : Complex) (hV : 0 < V) :
    integral volume (logGaussianWeightedWave V tau rho) =
      Complex.exp ((V : Complex) / 2 * (rho - (tau : Complex) * Complex.I) ^ 2) := by
  have he (u : Real) :
      logGaussianWeightedWave V tau rho u =
        (logGaussianDensity V u : Complex) *
          Complex.exp ((rho - (tau : Complex) * Complex.I) * (u : Complex)) := by
    dsimp only [logGaussianWeightedWave, logGaussianWave]
    rw [show (rho - (tau : Complex) * Complex.I) * (u : Complex) =
      rho * (u : Complex) + (-(tau : Complex) * Complex.I * (u : Complex)) by ring,
      Complex.exp_add]
    ring
  calc
    _ = integral volume (fun u : Real => (logGaussianDensity V u : Complex) *
        Complex.exp ((rho - (tau : Complex) * Complex.I) * (u : Complex))) :=
      integral_congr_ae (Eventually.of_forall he)
    _ = _ := logGaussianDensity_complex_moment V hV _

theorem logGaussianSpectralTail_eq_physical_spectral_tail
    (X V tau : Real) (rho : Complex) (hX : 0 < X) :
    logGaussianSpectralTail X V tau 1 rho =
      (X : Complex) ^ rho *
        integral (volume.restrict (Ioi (-Real.log X))) (logGaussianWeightedWave V tau rho) := by
  let a : Real := -Real.log X
  let f : Real -> Complex := logGaussianWeightedWave V tau rho
  let g : Real -> Complex := fun w =>
    Complex.exp (rho * (w : Complex)) * logGaussianWave V tau (w + a)
  have hXc : Not ((X : Complex) = 0) := Complex.ofReal_ne_zero.mpr hX.ne'
  have hFirst : logGaussianSpectralTail X V tau 1 rho =
      integral (volume.restrict (Ioi (1 : Real))) (fun u : Real =>
        ((Inv.inv u : Real) : Complex) * g (Real.log u)) := by
    unfold logGaussianSpectralTail
    apply setIntegral_congr_fun measurableSet_Ioi
    intro u hu
    dsimp only
    have huPos : 0 < u := lt_trans Real.zero_lt_one hu
    have huc : Not ((u : Complex) = 0) := Complex.ofReal_ne_zero.mpr huPos.ne'
    have hp : (u : Complex) ^ (rho - 1) =
        Inv.inv (u : Complex) * Complex.exp (rho * ((Real.log u : Real) : Complex)) := by
      rw [Complex.cpow_def_of_ne_zero huc,
        show Complex.log (u : Complex) * (rho - 1) =
          rho * Complex.log (u : Complex) - Complex.log (u : Complex) by ring,
        Complex.exp_sub, Complex.exp_log huc, <- Complex.ofReal_log huPos.le]
      ring
    have he : Real.log (1 * u) - Real.log X = Real.log u + a := by
      dsimp [a]
      simp only [one_mul]
      ring
    rw [hp, he]
    dsimp only [g, logGaussianWave]
    rw [Complex.ofReal_inv]
    ring
  have hMiddle : integral (volume.restrict (Ioi (1 : Real))) (fun u : Real =>
      ((Inv.inv u : Real) : Complex) * g (Real.log u)) =
      integral (volume.restrict (Ioi (0 : Real))) g := by
    have h := integral_comp_log_Ioi g (a := (1 : Real)) (by norm_num)
    simpa only [Real.log_one, RCLike.real_smul_eq_coe_mul] using! h
  have hFactor (w : Real) : g w = (X : Complex) ^ rho * f (w + a) := by
    have he : (X : Complex) ^ rho *
        Complex.exp (rho * ((w + a : Real) : Complex)) =
      Complex.exp (rho * (w : Complex)) := by
      rw [Complex.cpow_def_of_ne_zero hXc, <- Complex.exp_add]
      congr 1
      rw [<- Complex.ofReal_log hX.le]
      dsimp [a]
      push_cast
      ring
    dsimp only [g, f, logGaussianWeightedWave]
    rw [<- mul_assoc, he]
  let F : Real -> Complex := (Ioi a).indicator f
  have hShift : integral volume (fun w : Real => F (w + a)) = integral volume F :=
    integral_add_right_eq_self F a
  have hPoint (w : Real) :
      F (w + a) = (Ioi (0 : Real)).indicator (fun v : Real => f (v + a)) w := by
    have he : a < w + a <-> 0 < w := by constructor <;> intro h <;> linarith
    simp only [F, Set.indicator, mem_Ioi, he]
  have hLast : integral (volume.restrict (Ioi (0 : Real))) (fun w : Real => f (w + a)) =
      integral (volume.restrict (Ioi a)) f := by
    calc
      _ = integral volume ((Ioi (0 : Real)).indicator (fun w : Real => f (w + a))) :=
        (integral_indicator measurableSet_Ioi).symm
      _ = integral volume (fun w : Real => F (w + a)) :=
        integral_congr_ae (Eventually.of_forall fun w => (hPoint w).symm)
      _ = integral volume F := hShift
      _ = _ := integral_indicator measurableSet_Ioi
  rw [hFirst, hMiddle]
  calc
    integral (volume.restrict (Ioi (0 : Real))) g =
        integral (volume.restrict (Ioi (0 : Real))) (fun w : Real =>
          (X : Complex) ^ rho * f (w + a)) :=
      integral_congr_ae (Eventually.of_forall hFactor)
    _ = (X : Complex) ^ rho *
        integral (volume.restrict (Ioi (0 : Real))) (fun w : Real => f (w + a)) :=
      integral_const_mul _ _
    _ = _ := by rw [hLast]

end PrimeFactorOscillations.PrimeClassDeletion

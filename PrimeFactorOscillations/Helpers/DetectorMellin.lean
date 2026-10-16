/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.MellinTransform

/-!
# Detector Mellin

Holomorphic continuation of compensated Mellin errors and their differentiated readouts.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace PrimeFactorOscillations.DetectorMellin

open Filter Asymptotics MeasureTheory Set

def errorTransform (e : Real -> Complex) (s : Complex) : Complex :=
  (s - 1) * mellin e (1 - s)

theorem differentiableOn_errorTransform (e : Real -> Complex) (C : Real)
    (hlocal : LocallyIntegrableOn e (Ioi 0))
    (hzero : forall x : Real, x < 1 -> e x = 0)
    (herror : forall x : Real, 1 <= x -> norm (e x) <= C / x) :
    DifferentiableOn Complex (errorTransform e) {s : Complex | 0 < s.re} := by
  have htop : e =O[atTop] (fun x : Real => x ^ (-(1 : Real))) := by
    apply IsBigO.of_bound C
    filter_upwards [eventually_ge_atTop (1 : Real)] with x hx
    have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
    calc
      norm (e x) <= C / x := herror x hx
      _ = C * norm (x ^ (-(1 : Real))) := by
        rw [Real.rpow_neg_one, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hx0)]
        ring
  intro s hs
  have hbot : e =O[nhdsWithin (0 : Real) (Ioi 0)]
      (fun x : Real => x ^ (-(-s.re))) := by
    apply IsBigO.of_bound 0
    have hlt : Filter.Eventually (fun x : Real => x < 1)
        (nhdsWithin (0 : Real) (Ioi 0)) :=
      (eventually_lt_nhds zero_lt_one).filter_mono nhdsWithin_le_nhds
    filter_upwards [hlt] with x hx
    simp only [hzero x hx, norm_zero, zero_mul, le_refl]
  have hM := mellin_differentiableAt_of_isBigO_rpow hlocal htop
    (show (1 - s).re < 1 by simpa using hs) hbot
    (show -s.re < (1 - s).re by simp only [Complex.sub_re, Complex.one_re]; linarith)
  have hcomp := hM.comp s
    ((differentiableAt_const (1 : Complex)).sub differentiableAt_id)
  exact ((differentiableAt_id.sub (differentiableAt_const (1 : Complex))).mul hcomp).differentiableWithinAt

/-- The explicit Mellin error integral, with its correct shift. -/
theorem errorTransform_eq_integral (e : Real -> Complex) (s : Complex) :
    errorTransform e s =
      (s - 1) * integral (volume.restrict (Ioi (0 : Real)))
        (fun x : Real => (x : Complex) ^ (-s) * e x) := by
  unfold errorTransform mellin
  congr 1
  apply integral_congr_ae
  filter_upwards [] with x
  have hshift : (1 : Complex) - s - 1 = -s := by ring
  simp only [hshift, smul_eq_mul]

def errorReadout (e : Real -> Complex) (s : Complex) : Complex :=
  -deriv (errorTransform e) s

theorem analyticOnNhd_errorReadout (e : Real -> Complex) (C : Real)
    (hlocal : LocallyIntegrableOn e (Ioi 0))
    (hzero : forall x : Real, x < 1 -> e x = 0)
    (herror : forall x : Real, 1 <= x -> norm (e x) <= C / x) :
    AnalyticOnNhd Complex (errorReadout e) {s : Complex | 0 < s.re} := by
  have h := differentiableOn_errorTransform e C hlocal hzero herror
  have ha := h.analyticOnNhd (isOpen_lt continuous_const Complex.continuous_re)
  exact ha.deriv.neg

end PrimeFactorOscillations.DetectorMellin

/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The normalized log-Gaussian complex moment

The density has the paper's variance V and normalization sqrt(2*pi*V).
These are actual integrals for every complex argument, without an RH input.
The moment is the analytic input for the physical Gaussian Perron formula.
-/

set_option autoImplicit false
set_option Elab.async false

open MeasureTheory

namespace PrimeFactorOscillations.PrimeClassDeletion

noncomputable def logGaussianDensity (V u : Real) : Real :=
  Real.exp (-u ^ 2 / (2 * V)) / Real.sqrt (2 * Real.pi * V)

theorem logGaussian_unnormalized_moment (V : Real) (hV : 0 < V) (z : Complex) :
    (integral volume fun u : Real =>
      Complex.exp (((-(1 / (2 * V)) : Real) : Complex) * (u : Complex) ^ 2 +
        z * (u : Complex))) =
      (Real.sqrt (2 * Real.pi * V) : Complex) *
        Complex.exp ((V : Complex) / 2 * z ^ 2) := by
  let b : Complex := ((-(1 / (2 * V)) : Real) : Complex)
  have hVc : Not ((V : Complex) = 0) := Complex.ofReal_ne_zero.mpr hV.ne'
  have hb : b.re < 0 := by
    change -(1 / (2 * V)) < 0
    exact neg_lt_zero.mpr (one_div_pos.mpr (mul_pos (by norm_num) hV))
  have hbase : (Real.pi : Complex) / -b = ((2 * Real.pi * V : Real) : Complex) := by
    dsimp [b]
    push_cast
    field_simp [hVc]
  have hpref : ((Real.pi : Complex) / -b) ^ (1 / 2 : Complex) =
      (Real.sqrt (2 * Real.pi * V) : Complex) := by
    rw [hbase, Real.sqrt_eq_rpow]
    have hnonneg : 0 <= 2 * Real.pi * V := le_of_lt (by positivity)
    simpa only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat] using
      (Complex.ofReal_cpow hnonneg (1 / 2 : Real)).symm
  have hexp : (0 : Complex) - z ^ 2 / (4 * b) = (V : Complex) / 2 * z ^ 2 := by
    dsimp [b]
    push_cast
    field_simp [hVc]
    ring
  have h := integral_cexp_quadratic hb z 0
  simp only [add_zero] at h
  change (integral volume fun u : Real => Complex.exp (b * (u : Complex) ^ 2 +
    z * (u : Complex))) = _
  rw [h, hpref, hexp]

theorem logGaussianDensity_integrable_complex_moment
    (V : Real) (hV : 0 < V) (z : Complex) :
    Integrable (fun u : Real =>
      (logGaussianDensity V u : Complex) * Complex.exp (z * (u : Complex))) := by
  let b : Complex := ((-(1 / (2 * V)) : Real) : Complex)
  have hb : b.re < 0 := by
    change -(1 / (2 * V)) < 0
    exact neg_lt_zero.mpr (one_div_pos.mpr (mul_pos (by norm_num) hV))
  have hi (u : Real) :
      (logGaussianDensity V u : Complex) * Complex.exp (z * (u : Complex)) =
        Complex.exp (b * (u : Complex) ^ 2 + z * (u : Complex) + 0) *
          (Real.sqrt (2 * Real.pi * V) : Complex) ^ (-1 : Int) := by
    have hr : ((-u ^ 2 / (2 * V) : Real) : Complex) = b * (u : Complex) ^ 2 := by
      dsimp [b]
      push_cast
      ring
    rw [logGaussianDensity, Complex.ofReal_div, Complex.ofReal_exp, hr]
    simp only [add_zero, Complex.exp_add, zpow_neg_one]
    ring
  exact ((integrable_cexp_quadratic' hb z 0).mul_const _).congr
    (Filter.Eventually.of_forall fun u => (hi u).symm)

theorem logGaussianDensity_complex_moment (V : Real) (hV : 0 < V) (z : Complex) :
    (integral volume fun u : Real =>
      (logGaussianDensity V u : Complex) * Complex.exp (z * (u : Complex))) =
        Complex.exp ((V : Complex) / 2 * z ^ 2) := by
  have hroot : Not ((Real.sqrt (2 * Real.pi * V) : Complex) = 0) :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (by positivity)).ne'
  have hi (u : Real) :
      (logGaussianDensity V u : Complex) * Complex.exp (z * (u : Complex)) =
        Complex.exp (((-(1 / (2 * V)) : Real) : Complex) * (u : Complex) ^ 2 +
          z * (u : Complex)) * (Real.sqrt (2 * Real.pi * V) : Complex) ^ (-1 : Int) := by
    have hr : ((-u ^ 2 / (2 * V) : Real) : Complex) =
        ((-(1 / (2 * V)) : Real) : Complex) * (u : Complex) ^ 2 := by
      push_cast
      ring
    rw [logGaussianDensity, Complex.ofReal_div, Complex.ofReal_exp, hr, Complex.exp_add]
    simp only [zpow_neg_one]
    ring
  simp_rw [hi]
  rw [integral_mul_const, logGaussian_unnormalized_moment V hV z]
  simp only [zpow_neg_one]
  field_simp

end PrimeFactorOscillations.PrimeClassDeletion

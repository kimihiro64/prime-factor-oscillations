/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.LogGaussianLeftTailMajorant
import PrimeFactorOscillations.Helpers.LogGaussianPhysicalWeight

/-!
# The actual Gaussian-wave derivative and its uniform tail bound

This supplies the derivative and majorant used for integration by parts
on the separated left tail of each physical zero contribution.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.PrimeClassDeletion

noncomputable def logGaussianWaveSlope (V tau u : Real) : Complex :=
  ((-u / V : Real) : Complex) - (tau : Complex) * Complex.I

theorem logGaussianWave_eq_quadratic (V tau u : Real) :
    logGaussianWave V tau u =
      (1 / (Real.sqrt (2 * Real.pi * V) : Complex)) *
        Complex.exp (((-(1 / (2 * V)) : Real) : Complex) * (u : Complex) ^ 2 +
          (-(tau : Complex) * Complex.I) * (u : Complex)) := by
  have he : (((-(1 / (2 * V)) : Real) : Complex) * (u : Complex) ^ 2) =
      ((-u ^ 2 / (2 * V) : Real) : Complex) := by
    push_cast
    ring
  rw [logGaussianWave, logGaussianDensity, Complex.ofReal_div, Complex.ofReal_exp,
    he, Complex.exp_add]
  ring

theorem logGaussianWave_hasDerivAt (V tau u : Real) (hV : 0 < V) :
    HasDerivAt (logGaussianWave V tau)
      (logGaussianWaveSlope V tau u * logGaussianWave V tau u) u := by
  let b : Complex := ((-(1 / (2 * V)) : Real) : Complex)
  let z : Complex := -(tau : Complex) * Complex.I
  let f : Real -> Complex := fun v =>
    (1 / (Real.sqrt (2 * Real.pi * V) : Complex)) *
      Complex.exp (b * (v : Complex) ^ 2 + z * (v : Complex))
  have hEq : f = logGaussianWave V tau := by
    funext v
    exact (logGaussianWave_eq_quadratic V tau v).symm
  have hReal : HasDerivAt (fun v : Real => (v : Complex)) 1 u := by
    simpa using! (Complex.ofRealCLM.hasDerivAt (x := u))
  have hPoly := (HasDerivAt.const_mul b (hReal.pow 2)).add (HasDerivAt.const_mul z hReal)
  have hBase := HasDerivAt.const_mul
    (1 / (Real.sqrt (2 * Real.pi * V) : Complex)) hPoly.cexp
  simp only [<- hEq]
  convert hBase using 1
  dsimp [f, b, z, logGaussianWaveSlope]
  push_cast
  field_simp [hV.ne'] <;> ring

theorem logGaussianWave_derivative_norm_bound (V tau u : Real) (hV : 1 <= V) :
    norm (logGaussianWaveSlope V tau u * logGaussianWave V tau u) <=
      (4 + abs tau) * logGaussianTailScale V * Real.exp u := by
  have hVPos : 0 < V := lt_of_lt_of_le Real.zero_lt_one hV
  have hSlope : norm (logGaussianWaveSlope V tau u) <= abs u / V + abs tau := by
    calc
      _ <= norm (((-u / V : Real) : Complex)) + norm ((tau : Complex) * Complex.I) :=
        norm_sub_le _ _
      _ = _ := by
        simp [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hVPos]
  have hd : 0 <= logGaussianDensity V u :=
    (div_pos (Real.exp_pos _) (Real.sqrt_pos.mpr (by positivity))).le
  rw [norm_mul, logGaussianWave_norm V tau u hVPos]
  exact (mul_le_mul_of_nonneg_right hSlope hd).trans
    (logGaussianDensity_derivative_size_bound V tau u hV)

end PrimeFactorOscillations.PrimeClassDeletion

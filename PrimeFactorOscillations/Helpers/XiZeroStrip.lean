/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Robin1984.NicolasLandau.XiLogDerivative

/-!
# Unconditional strip bounds for actual xi zeros

These are the geometric inputs for safe-line Gaussian zero pairings.
Neither the arbitrary-zero theorem nor its divisor-index application
assumes RH or a zero-free substrip of the critical strip.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.PrimeClassDeletion

theorem riemannXi_zero_re_bounds (z : Complex) (hz : Complex.riemannXi z = 0) :
    And (0 < z.re) (z.re < 1) := by
  have upper (w : Complex) (hw : Complex.riemannXi w = 0) : w.re < 1 := by
    have hw0 : Not (w = 0) := by
      intro h
      rw [h, Complex.riemannXi_zero] at hw
      norm_num at hw
    have hw1 : Not (w = 1) := by
      intro h
      rw [h, Robin1984.riemannXi_one_eq_half] at hw
      norm_num at hw
    apply lt_of_not_ge
    intro hre
    exact riemannZeta_ne_zero_of_one_le_re hre
      (Robin1984.riemannZeta_eq_zero_of_riemannXi_eq_zero hw0 hw1 hw)
  have hzUpper := upper z hz
  have href : Complex.riemannXi (1 - z) = 0 := by
    rw [Complex.riemannXi_one_sub]
    exact hz
  have hzLower := upper (1 - z) href
  rw [Complex.sub_re, Complex.one_re] at hzLower
  exact And.intro (by linarith only [hzLower]) hzUpper

theorem xiDivisorZeroValue_re_bounds (p : RiemannXiDivisorZeroIndex) :
    And (0 < (riemannXiDivisorZeroValue p).re)
      ((riemannXiDivisorZeroValue p).re < 1) :=
  riemannXi_zero_re_bounds (riemannXiDivisorZeroValue p)
    (riemannXiDivisorZeroValue_eq_zero p)

end PrimeFactorOscillations.PrimeClassDeletion

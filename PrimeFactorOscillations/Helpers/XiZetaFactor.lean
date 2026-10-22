/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.XiZeroStrip
import PrimeFactorOscillations.Helpers.XiZetaMultiplicity

/-!
# Identification of the actual xi and nontrivial zeta zero sets

The existing analytic unit and multiplicity bridge are reused unchanged.
No zero-location hypothesis beyond the unconditional xi strip is added.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.PrimeClassDeletion

theorem riemannXi_zero_iff_nontrivial_zeta_zero (s : Complex) :
    Complex.riemannXi s = 0 <->
      And (riemannZeta s = 0) (And (0 < s.re) (s.re < 1)) := by
  constructor
  . intro hs
    have hStrip := riemannXi_zero_re_bounds s hs
    have hOne : Not (s = 1) := by
      intro h
      rw [h, Complex.one_re] at hStrip
      exact (lt_irrefl 1) hStrip.2
    have hZeta : riemannZeta s = 0 := by
      rw [riemannXi_eq_xiZetaUnit_mul hStrip.1 hOne] at hs
      exact (mul_eq_zero.mp hs).resolve_left (xiZetaUnit_ne_zero hStrip.1 hOne)
    exact And.intro hZeta hStrip
  . intro hs
    have hOne : Not (s = 1) := by
      intro h
      have hRe := hs.2.2
      rw [h, Complex.one_re] at hRe
      exact (lt_irrefl 1) hRe
    rw [riemannXi_eq_xiZetaUnit_mul hs.2.1 hOne, hs.1, mul_zero]

end PrimeFactorOscillations.PrimeClassDeletion

/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.NicolasStripError

/-!
# From a zeta zero-free half-plane to the Nicolas error

The xi functional equation supplies both strip endpoints from an explicit
zeta nonvanishing hypothesis. The complete arithmetic error estimate then
retains its leading spectral term and both remainder terms. This module
does not prove the nonvanishing hypothesis.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace PrimeFactorOscillations
open Complex Robin1984

theorem xi_zero_strip_of_zeta_nonvanishing {b : Real} (hb : 0 <= b)
    (hZeroFree : forall s : Complex, b < s.re -> Not (s = 1) ->
      Not (riemannZeta s = 0)) {rho : Complex} (hXi : rho.riemannXi = 0) :
    1 - b <= rho.re /\ rho.re <= b := by
  have hUpper (z : Complex) (hz : z.riemannXi = 0) : z.re <= b := by
    by_contra hn
    have hRe : b < z.re := lt_of_not_ge hn
    have hzZero : Not (z = 0) := by
      intro h
      rw [h] at hRe
      simp only [Complex.zero_re] at hRe
      linarith
    have hzOne : Not (z = 1) := by
      intro h
      rw [h, riemannXi_one_eq_half] at hz
      norm_num at hz
    exact hZeroFree z hRe hzOne
      (riemannZeta_eq_zero_of_riemannXi_eq_zero hzZero hzOne hz)
  have hReflected : (1 - rho).riemannXi = 0 := by
    rw [Complex.riemannXi_one_sub]
    exact hXi
  have hLower := hUpper (1 - rho) hReflected
  simp only [Complex.sub_re, Complex.one_re] at hLower
  exact And.intro (by linarith) (hUpper rho hXi)

theorem canonical_xi_strip_of_zeta_nonvanishing {b : Real} (hb : 0 <= b)
    (hZeroFree : forall s : Complex, b < s.re -> Not (s = 1) ->
      Not (riemannZeta s = 0)) :
    forall p : RiemannXiDivisorZeroIndex,
      1 - b <= (riemannXiDivisorZeroValue p).re /\
        (riemannXiDivisorZeroValue p).re <= b := by
  intro p
  exact xi_zero_strip_of_zeta_nonvanishing hb hZeroFree
    (riemannXiDivisorZeroValue_eq_zero p)

/-- A zeta zero-free half-plane controls the complete arithmetic error.
The zero-free premise is explicit and is not discharged by this theorem. -/
theorem nicolasJ_envelope_of_zeta_nonvanishing {b : Real}
    (hb : 0 < b) (hbOne : b < 1)
    (hZeroFree : forall s : Complex, b < s.re -> Not (s = 1) ->
      Not (riemannZeta s = 0))
    {x : Real} (hx : 3 <= x) :
    abs (nicolasJ x) <=
      ((Real.eulerMascheroniConstant + 2 - Real.log (4 * Real.pi)) /
        (2 * Real.sqrt (b * (1 - b)))) *
          x ^ (b - 1) * Inv.inv (Real.log x) +
      ((Real.eulerMascheroniConstant + 2 - Real.log (4 * Real.pi)) / (1 - b)) *
        nicolasStripRemainderScale b x +
      Real.log (2 * Real.pi) * x ^ (-(1 : Real)) * Inv.inv (Real.log x) := by
  exact nicolasJ_strip_envelope hb hbOne
    (canonical_xi_strip_of_zeta_nonvanishing hb.le hZeroFree) hx

end PrimeFactorOscillations

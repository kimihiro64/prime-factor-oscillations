/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.CarmichaelMultiplicityCarrier
import PrimeFactorOscillations.Assembly.CarmichaelStripReadout

/-!
# Actual zeta zeros as finite reflected multiplicity spectra

Every positive-height finite zeta window has its actual analytic orders,
reflection, and the established unconditional seven-eighths strip.
Quadratic and quartic reference orders are the complete actual zeta orders,
including references that vanish. No RH or simplicity hypothesis is used.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations.CarmichaelDyadicSharpness

open DirichletCompensatedProbe CarmichaelWeightedSignal
open CarmichaelStripCarrier CarmichaelTraceSharpness

abbrev ZetaIndex (T : Real) :=
  {rho : Complex // Membership.mem (upperZeroValues T) rho}

instance zetaIndexFintype (T : Real) : Fintype (ZetaIndex T) := by
  classical
  exact Finset.fintypeCoeSort _

theorem window_re_upper (T : Real) (rho : Complex)
    (h : Membership.mem (upperZeroValues T) rho) : rho.re <= (7 / 8 : Real) := by
  classical
  by_cases hHalf : rho.re <= (1 / 2 : Real)
  . linarith
  . apply rightZeroSupport_seven_eighths T rho
    exact Finset.mem_filter.mpr (And.intro h (lt_of_not_ge hHalf))

def zetaSpectrum (T : Real) : ReflectedSpectrum (ZetaIndex T) (7 / 8) where
  point := Subtype.val
  mult := fun i => analyticOrderNatAt riemannZeta i.val
  point_injective := Subtype.val_injective
  mult_pos := fun i => zeta_order_pos_of_window T i.val
    ((mem_upperZeroValues T i.val).mp i.property)
  im_pos := fun i => ((mem_upperZeroValues T i.val).mp i.property).2.2.2.1
  re_lower := by
    intro i
    have h := window_re_upper T (zeroReflection i.val)
      (reflection_mem_upperZeroValues i.property)
    rw [zeroReflection_re] at h
    linarith
  re_upper := fun i => window_re_upper T i.val i.property
  mirror := fun i => Subtype.mk (zeroReflection i.val)
    (reflection_mem_upperZeroValues i.property)
  mirror_involutive := by
    intro i
    apply Subtype.ext
    exact zeroReflection_involutive i.val
  point_mirror := fun _ => rfl
  mult_mirror := by
    intro i
    exact zetaMultiplicity_reflection
      (And.intro ((mem_upperZeroValues T i.val).mp i.property).2.1
        ((mem_upperZeroValues T i.val).mp i.property).2.2.1)

theorem zetaSpectrum_rowOrder (T d : Real) (hd : 2 <= d) (i : ZetaIndex T) :
    (zetaSpectrum T).rowOrder d i =
      analyticOrderNatAt riemannZeta (powerMap d i.val) := by
  classical
  let S := zetaSpectrum T
  by_cases hm : 0 < analyticOrderNatAt riemannZeta (powerMap d i.val)
  . have hw := (powerMap_window d T hd i.val
      ((mem_upperZeroValues T i.val).mp i.property) hm).1
    let j : ZetaIndex T := Subtype.mk (powerMap d i.val)
      ((mem_upperZeroValues T _).mpr hw)
    have hp : S.point j = powerMap d i.val := rfl
    change atomicOrder S.point S.mult (powerMap d i.val) = _
    rw [<- hp, atomicOrder_at _ _ S.point_injective]
    rfl
  . have hZero := Nat.eq_zero_of_not_pos hm
    change atomicOrder S.point S.mult (powerMap d i.val) = _
    rw [hZero]
    apply atomicOrder_zero
    intro j hj
    have he : S.mult j = 0 := by
      change analyticOrderNatAt riemannZeta j.val = 0
      have hp : j.val = powerMap d i.val := hj
      rw [hp, hZero]
    exact (Nat.ne_of_gt (S.mult_pos j)) he

theorem sum_zetaIndex (T : Real) (f : Complex -> Real) :
    (Finset.univ : Finset (ZetaIndex T)).sum (fun i => f i.val) =
      (upperZeroValues T).sum f := by
  classical
  change (upperZeroValues T).attach.sum (fun i => f i.val) = _
  exact Finset.sum_attach _ _

theorem zetaSpectrum_totalMass (T : Real) :
    (zetaSpectrum T).totalMass = (upperZeroValues T).sum zetaSquareMass := by
  unfold ReflectedSpectrum.totalMass
  calc
    _ = (Finset.univ : Finset (ZetaIndex T)).sum (fun i => zetaSquareMass i.val) := by
      apply Finset.sum_congr rfl
      intro i _
      change (analyticOrderNatAt riemannZeta i.val : Real) / i.val.im ^ 2 =
        (analyticOrderNatAt riemannZeta i.val : Real) * (1 / i.val.im ^ 2)
      ring
    _ = _ := sum_zetaIndex T zetaSquareMass

end PrimeFactorOscillations.CarmichaelDyadicSharpness

/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.CarmichaelEffectiveMultiplicity
import PrimeFactorOscillations.Helpers.CoprimalityDirichletCarrier
import PrimeFactorOscillations.Helpers.ZeroSmallValueArea

/-! # A coprimality-probability criterion for global zeta simplicity

The theorem is an equivalence, not a proof of its global area hypothesis.
All assertions are unconditional. The area is two-dimensional Lebesgue area.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace PrimeFactorOscillations

def ZetaNontrivialZerosSimple : Prop :=
  forall w : Complex, And (0 < w.re) (w.re < 1) -> analyticOrderNatAt riemannZeta w <= 1

def CoprimalityCarrierGlobalAreaCriterion : Prop :=
  forall w : Complex, And (0 < w.re) (w.re < 1) ->
    SublevelAreaVanishingAt coprimalityDirichletCarrier w

theorem coprimalityCarrier_local_simplicity_iff (w : Complex)
    (hw : And (0 < w.re) (w.re < 1)) :
    analyticOrderNatAt riemannZeta w <= 1 <->
      SublevelAreaVanishingAt coprimalityDirichletCarrier w := by
  have hw1 : Not (w = 1) := by
    intro h
    have hh := hw.2
    rw [h] at hh
    norm_num at hh
  have ha := coprimalityDirichletCarrier_analyticAt w hw.1 hw1
  have hf := analyticOrderAt_coprimalityDirichletCarrier_ne_top w hw.1 hw1
  rw [<- analyticOrderNatAt_coprimalityDirichletCarrier w hw.1 hw1]
  exact analyticOrderNatAt_le_one_iff_sublevelAreaVanishingAt _ w ha hf

theorem zeta_global_simplicity_iff_coprimality_area :
    ZetaNontrivialZerosSimple <-> CoprimalityCarrierGlobalAreaCriterion := by
  constructor
  case mp =>
    intro h w hw
    exact (coprimalityCarrier_local_simplicity_iff w hw).mp (h w hw)
  case mpr =>
    intro h w hw
    exact (coprimalityCarrier_local_simplicity_iff w hw).mpr (h w hw)

theorem coprimalityCarrier_area_on_effective_window (w : Complex)
    (hw : And (0 < w.re) (w.re < 1)) (ht : 2 <= abs w.im)
    (hmax : abs w.im < Real.exp (63 / 20)) :
    SublevelAreaVanishingAt coprimalityDirichletCarrier w :=
  (coprimalityCarrier_local_simplicity_iff w hw).mp (zeta_simplicity_window hw ht hmax)

theorem zeta_global_simplicity_iff_coprimality_area_outside_window :
    ZetaNontrivialZerosSimple <->
      (forall w : Complex, And (0 < w.re) (w.re < 1) ->
        Not (And (2 <= abs w.im) (abs w.im < Real.exp (63 / 20))) ->
        SublevelAreaVanishingAt coprimalityDirichletCarrier w) := by
  constructor
  case mp =>
    intro h w hw _
    exact (coprimalityCarrier_local_simplicity_iff w hw).mp (h w hw)
  case mpr =>
    intro h
    apply zeta_global_simplicity_iff_coprimality_area.mpr
    intro w hw
    by_cases hin : And (2 <= abs w.im) (abs w.im < Real.exp (63 / 20))
    case pos => exact coprimalityCarrier_area_on_effective_window w hw hin.1 hin.2
    case neg => exact h w hw hin

end PrimeFactorOscillations

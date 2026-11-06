/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.CarmichaelFifthSupport
import PrimeFactorOscillations.Assembly.CarmichaelZetaTripleMultiplicity

/-!
# Actual zeta fifth-multiplicity stability and equality rigidity

The fifth-order unit tail is bounded by one quarter of the full joint
carrier gap. Exact equality in the previous joint bound forces every
common-weak zero in the window to have order at most four. No RH is assumed.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations.CarmichaelDyadicSharpness

open DirichletCompensatedProbe CarmichaelWeightedSignal CarmichaelStripCarrier

def zetaFifthUnitAt (rho : Complex) : Real :=
  if 5 <= analyticOrderNatAt riemannZeta rho then zetaUnitMassAt rho else 0

theorem zetaSpectrum_weakFifthUnitMass (T : Real) :
    (zetaSpectrum T).weakFifthUnitMass =
      (jointWeakSupport 2 4 T).sum zetaFifthUnitAt := by
  classical
  unfold ReflectedSpectrum.weakFifthUnitMass ReflectedSpectrum.weakIndices
  simp_rw [zetaSpectrum_rowOrder T 2 (by norm_num),
    zetaSpectrum_rowOrder T 4 (by norm_num)]
  exact sum_zetaIndex_filter T
    (fun rho => (analyticOrderNatAt riemannZeta rho : Real) <=
        2 * (analyticOrderNatAt riemannZeta (powerMap 2 rho) : Real) /\
      (analyticOrderNatAt riemannZeta rho : Real) <=
        4 * (analyticOrderNatAt riemannZeta (powerMap 4 rho) : Real)) zetaFifthUnitAt

theorem zeta_carrier_fifth_support_bound (T : Real) :
    39 * (jointWeakSupport 2 4 T).sum zetaUnitMassAt +
        (jointWeakSupport 2 4 T).sum zetaRepeatedUnitAt +
        4 * (jointWeakSupport 2 4 T).sum zetaFifthUnitAt <=
      (jointCarrierSupport 2 4 T).sum zetaSquareMass := by
  have h := (zetaSpectrum T).carrier_fifth_support_bound
  rw [zetaSpectrum_carrierMass, zetaSpectrum_weakUnitMass,
    zetaSpectrum_weakRepeatedUnitMass, zetaSpectrum_weakFifthUnitMass] at h
  exact h

theorem zeta_fifth_tail_bound (T : Real) :
    (jointWeakSupport 2 4 T).sum zetaFifthUnitAt <=
      ((jointCarrierSupport 2 4 T).sum zetaSquareMass -
        39 * (jointWeakSupport 2 4 T).sum zetaUnitMassAt -
          (jointWeakSupport 2 4 T).sum zetaRepeatedUnitAt) / 4 := by
  have h := zeta_carrier_fifth_support_bound T
  linarith

theorem zeta_weakFifth_zero_iff (T : Real) :
    (jointWeakSupport 2 4 T).sum zetaFifthUnitAt = 0 <->
      forall rho, Membership.mem (jointWeakSupport 2 4 T) rho ->
        analyticOrderNatAt riemannZeta rho <= 4 := by
  classical
  rw [<- zetaSpectrum_weakFifthUnitMass, ReflectedSpectrum.weakFifthUnitMass_eq_zero_iff]
  constructor
  . intro h rho hrho
    let i : ZetaIndex T := Subtype.mk rho (Finset.mem_filter.mp hrho).1
    have hi : Membership.mem (zetaSpectrum T).weakIndices i := by
      rw [ReflectedSpectrum.weakIndices, Finset.mem_filter]
      refine And.intro (Finset.mem_univ i) ?_
      rw [zetaSpectrum_rowOrder T 2 (by norm_num),
        zetaSpectrum_rowOrder T 4 (by norm_num)]
      exact (Finset.mem_filter.mp hrho).2
    exact h i hi
  . intro h i hi
    have hw := (Finset.mem_filter.mp hi).2
    rw [zetaSpectrum_rowOrder T 2 (by norm_num),
      zetaSpectrum_rowOrder T 4 (by norm_num)] at hw
    exact h i.val (Finset.mem_filter.mpr (And.intro i.property hw))

theorem zeta_weak_order_le_four_of_joint_equality (T : Real)
    (hEquality : (jointCarrierSupport 2 4 T).sum zetaSquareMass =
      39 * (jointWeakSupport 2 4 T).sum zetaUnitMassAt +
        (jointWeakSupport 2 4 T).sum zetaRepeatedUnitAt) :
    forall rho, Membership.mem (jointWeakSupport 2 4 T) rho ->
      analyticOrderNatAt riemannZeta rho <= 4 := by
  have hEqualityS : (zetaSpectrum T).carrierMass =
      39 * (zetaSpectrum T).weakUnitMass + (zetaSpectrum T).weakRepeatedUnitMass := by
    rw [zetaSpectrum_carrierMass, zetaSpectrum_weakUnitMass,
      zetaSpectrum_weakRepeatedUnitMass]
    exact hEquality
  have hSmall := (zetaSpectrum T).weak_order_le_four_of_joint_equality hEqualityS
  have hZero : (zetaSpectrum T).weakFifthUnitMass = 0 :=
    (zetaSpectrum T).weakFifthUnitMass_eq_zero_iff.mpr hSmall
  rw [zetaSpectrum_weakFifthUnitMass] at hZero
  exact (zeta_weakFifth_zero_iff T).mp hZero

theorem zeta_readout_carrier_fifth_bound (G : Complex -> Complex)
    (hG : AnalyticOnNhd Complex G {s : Complex | 0 < s.re /\ s.re < 1})
    (T : Real) (r2 r4 : Complex -> Complex)
    (h2 : forall rho, Membership.mem (upperZeroValues T) rho -> Filter.Tendsto
      (fun s => (s - rho) * affinePowerReadout (zetaMultiplicityReadout G) 2 s)
      (nhdsWithin rho (Set.compl {rho})) (nhds (r2 rho)))
    (h4 : forall rho, Membership.mem (upperZeroValues T) rho -> Filter.Tendsto
      (fun s => (s - rho) * affinePowerReadout (zetaMultiplicityReadout G) 4 s)
      (nhdsWithin rho (Set.compl {rho})) (nhds (r4 rho))) :
    39 * (jointWeakSupport 2 4 T).sum zetaUnitMassAt +
        (jointWeakSupport 2 4 T).sum zetaRepeatedUnitAt +
        4 * (jointWeakSupport 2 4 T).sum zetaFifthUnitAt <=
      ((upperZeroValues T).filter (fun rho =>
        (r2 rho * (rho + (2 : Complex) - 1)).im < 0 \/
          (r4 rho * (rho + (4 : Complex) - 1)).im < 0)).sum zetaSquareMass := by
  have h := zeta_carrier_fifth_support_bound T
  rw [joint_readout_carrier_eq G hG 2 4 T (by norm_num) (by norm_num) r2 r4 h2 h4] at h
  simpa using h

end PrimeFactorOscillations.CarmichaelDyadicSharpness

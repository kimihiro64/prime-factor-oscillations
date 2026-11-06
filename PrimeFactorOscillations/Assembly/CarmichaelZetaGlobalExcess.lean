/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.CarmichaelNinthSupport
import PrimeFactorOscillations.Assembly.CarmichaelZetaMinimalCarrier

/-!
# Actual zeta global multiplicity-excess certificates

The excess ranges over the entire offcritical window, independently of common
weak membership. Full quadratic and quartic residue readouts retain every
reference contribution and analytic correction. No RH hypothesis is used.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations.CarmichaelDyadicSharpness

open DirichletCompensatedProbe CarmichaelWeightedSignal CarmichaelStripCarrier

def zetaNinthUnitAt (rho : Complex) : Real :=
  if 9 <= analyticOrderNatAt riemannZeta rho then zetaUnitMassAt rho else 0

def zetaOffcriticalOrderExcessAt (rho : Complex) : Real :=
  if rho.re < 1 / 2 then
    ((analyticOrderNatAt riemannZeta rho - 3 : Nat) : Real) * zetaUnitMassAt rho else 0

theorem zetaSpectrum_weakNinthUnitMass (T : Real) :
    (zetaSpectrum T).weakNinthUnitMass =
      (jointWeakSupport 2 4 T).sum zetaNinthUnitAt := by
  classical
  unfold ReflectedSpectrum.weakNinthUnitMass ReflectedSpectrum.weakIndices
  simp_rw [zetaSpectrum_rowOrder T 2 (by norm_num),
    zetaSpectrum_rowOrder T 4 (by norm_num)]
  exact sum_zetaIndex_filter T
    (fun rho => (analyticOrderNatAt riemannZeta rho : Real) <=
        2 * (analyticOrderNatAt riemannZeta (powerMap 2 rho) : Real) /\
      (analyticOrderNatAt riemannZeta rho : Real) <=
        4 * (analyticOrderNatAt riemannZeta (powerMap 4 rho) : Real)) zetaNinthUnitAt

theorem zetaSpectrum_globalOffcriticalExcess (T : Real) :
    (zetaSpectrum T).globalOffcriticalExcess =
      (upperZeroValues T).sum zetaOffcriticalOrderExcessAt := by
  classical
  change Finset.univ.sum (fun i : ZetaIndex T => zetaOffcriticalOrderExcessAt i.val) = _
  simpa using sum_zetaIndex_filter T (fun _ => True) zetaOffcriticalOrderExcessAt

theorem zeta_carrier_global_excess_bound (T : Real) :
    39 * (jointWeakSupport 2 4 T).sum zetaUnitMassAt +
      (jointWeakSupport 2 4 T).sum zetaRepeatedUnitAt +
      4 * (jointWeakSupport 2 4 T).sum zetaFifthUnitAt +
      16 * (jointWeakSupport 2 4 T).sum zetaNinthUnitAt +
      (upperZeroValues T).sum zetaOffcriticalOrderExcessAt <=
        (jointCarrierSupport 2 4 T).sum zetaSquareMass := by
  have h := (zetaSpectrum T).carrier_global_excess_bound
  rw [zetaSpectrum_carrierMass, zetaSpectrum_weakUnitMass,
    zetaSpectrum_weakRepeatedUnitMass, zetaSpectrum_weakFifthUnitMass,
    zetaSpectrum_weakNinthUnitMass, zetaSpectrum_globalOffcriticalExcess] at h
  exact h

theorem zeta_offcritical_order_excess_le_carrier_remainder (T : Real)
    (rho : Complex) (hWindow : Membership.mem (upperZeroValues T) rho)
    (hCenter : Not (rho.re = 1 / 2)) :
    ((analyticOrderNatAt riemannZeta rho - 3 : Nat) : Real) * zetaUnitMassAt rho <=
      (jointCarrierSupport 2 4 T).sum zetaSquareMass -
      39 * (jointWeakSupport 2 4 T).sum zetaUnitMassAt -
      (jointWeakSupport 2 4 T).sum zetaRepeatedUnitAt -
      4 * (jointWeakSupport 2 4 T).sum zetaFifthUnitAt -
      16 * (jointWeakSupport 2 4 T).sum zetaNinthUnitAt := by
  have h := (zetaSpectrum T).offcritical_order_excess_le_carrier_remainder
    (Subtype.mk rho hWindow) hCenter
  rw [zetaSpectrum_carrierMass, zetaSpectrum_weakUnitMass,
    zetaSpectrum_weakRepeatedUnitMass, zetaSpectrum_weakFifthUnitMass,
    zetaSpectrum_weakNinthUnitMass] at h
  exact h

theorem zeta_globalOffcriticalExcess_zero_iff (T : Real) :
    (upperZeroValues T).sum zetaOffcriticalOrderExcessAt = 0 <->
      forall rho, Membership.mem (upperZeroValues T) rho ->
        Not (rho.re = 1 / 2) -> analyticOrderNatAt riemannZeta rho <= 3 := by
  rw [<- zetaSpectrum_globalOffcriticalExcess,
    ReflectedSpectrum.globalOffcriticalExcess_eq_zero_iff]
  constructor
  . intro h rho hr hc
    exact h (Subtype.mk rho hr) hc
  . intro h i hc
    exact h i.val i.property hc

theorem zeta_offcritical_order_le_three_of_zero_remainder (T : Real)
    (hEq : (jointCarrierSupport 2 4 T).sum zetaSquareMass =
      39 * (jointWeakSupport 2 4 T).sum zetaUnitMassAt +
      (jointWeakSupport 2 4 T).sum zetaRepeatedUnitAt +
      4 * (jointWeakSupport 2 4 T).sum zetaFifthUnitAt +
      16 * (jointWeakSupport 2 4 T).sum zetaNinthUnitAt) :
    forall rho, Membership.mem (upperZeroValues T) rho ->
      Not (rho.re = 1 / 2) -> analyticOrderNatAt riemannZeta rho <= 3 := by
  have hb := zeta_carrier_global_excess_bound T
  have hn : 0 <= (upperZeroValues T).sum zetaOffcriticalOrderExcessAt := by
    rw [<- zetaSpectrum_globalOffcriticalExcess]
    exact (zetaSpectrum T).globalOffcriticalExcess_nonneg
  have hz : (upperZeroValues T).sum zetaOffcriticalOrderExcessAt = 0 := by linarith
  exact (zeta_globalOffcriticalExcess_zero_iff T).mp hz

theorem zeta_readout_carrier_global_excess_bound (G : Complex -> Complex)
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
      4 * (jointWeakSupport 2 4 T).sum zetaFifthUnitAt +
      16 * (jointWeakSupport 2 4 T).sum zetaNinthUnitAt +
      (upperZeroValues T).sum zetaOffcriticalOrderExcessAt <=
        ((upperZeroValues T).filter (fun rho =>
          (r2 rho * (rho + (2 : Complex) - 1)).im < 0 \/
            (r4 rho * (rho + (4 : Complex) - 1)).im < 0)).sum zetaSquareMass := by
  have h := zeta_carrier_global_excess_bound T
  rw [joint_readout_carrier_eq G hG 2 4 T (by norm_num) (by norm_num) r2 r4 h2 h4] at h
  simpa using h

end PrimeFactorOscillations.CarmichaelDyadicSharpness


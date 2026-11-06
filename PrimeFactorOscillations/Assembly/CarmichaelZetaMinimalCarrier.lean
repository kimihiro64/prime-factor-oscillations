/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.CarmichaelSeventeenRigidity
import PrimeFactorOscillations.Assembly.CarmichaelZetaTwoTail

/-!
# Actual zeta minimum-support and equality classification

The exact signed equality and positive fifth tail imply at least seventeen
distinct zeros. Every smallest window has the classified geometry and orders.
Both full compensated readouts can supply the carrier equality without RH.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations.CarmichaelDyadicSharpness

open DirichletCompensatedProbe CarmichaelWeightedSignal CarmichaelStripCarrier

theorem zeta_fifth_equality_spectrum (T : Real)
    (hEq : (jointCarrierSupport 2 4 T).sum zetaSquareMass =
      39 * (jointWeakSupport 2 4 T).sum zetaUnitMassAt +
        (jointWeakSupport 2 4 T).sum zetaRepeatedUnitAt +
        4 * (jointWeakSupport 2 4 T).sum zetaFifthUnitAt) :
    (zetaSpectrum T).carrierMass = 39 * (zetaSpectrum T).weakUnitMass +
      (zetaSpectrum T).weakRepeatedUnitMass + 4 * (zetaSpectrum T).weakFifthUnitMass := by
  rw [zetaSpectrum_carrierMass, zetaSpectrum_weakUnitMass,
    zetaSpectrum_weakRepeatedUnitMass, zetaSpectrum_weakFifthUnitMass]
  exact hEq

theorem zeta_fifth_equality_card_minimum (T : Real)
    (hEq : (jointCarrierSupport 2 4 T).sum zetaSquareMass =
      39 * (jointWeakSupport 2 4 T).sum zetaUnitMassAt +
        (jointWeakSupport 2 4 T).sum zetaRepeatedUnitAt +
        4 * (jointWeakSupport 2 4 T).sum zetaFifthUnitAt)
    (hPos : 0 < (jointWeakSupport 2 4 T).sum zetaFifthUnitAt) :
    17 <= (upperZeroValues T).card := by
  have hp : 0 < (zetaSpectrum T).weakFifthUnitMass := by
    rwa [zetaSpectrum_weakFifthUnitMass]
  have h := (zetaSpectrum T).fifth_equality_card_minimum
    (zeta_fifth_equality_spectrum T hEq) hp
  simpa only [Fintype.card_coe] using h

theorem zeta_fifth_equality_noncentral_order (T : Real)
    (hEq : (jointCarrierSupport 2 4 T).sum zetaSquareMass =
      39 * (jointWeakSupport 2 4 T).sum zetaUnitMassAt +
        (jointWeakSupport 2 4 T).sum zetaRepeatedUnitAt +
        4 * (jointWeakSupport 2 4 T).sum zetaFifthUnitAt)
    (rho : Complex) (hWindow : Membership.mem (upperZeroValues T) rho)
    (hCenter : Not (rho.re = 1 / 2)) :
    analyticOrderNatAt riemannZeta rho <= 3 := by
  exact (zetaSpectrum T).fifth_equality_noncentral_order_le_three
    (zeta_fifth_equality_spectrum T hEq) (Subtype.mk rho hWindow) hCenter

theorem zeta_fifth_minimal_configuration (T : Real)
    (hEq : (jointCarrierSupport 2 4 T).sum zetaSquareMass =
      39 * (jointWeakSupport 2 4 T).sum zetaUnitMassAt +
        (jointWeakSupport 2 4 T).sum zetaRepeatedUnitAt +
        4 * (jointWeakSupport 2 4 T).sum zetaFifthUnitAt)
    (hPos : 0 < (jointWeakSupport 2 4 T).sum zetaFifthUnitAt)
    (hCard : (upperZeroValues T).card = 17) :
    exists H : Real, 0 < H /\ exists M : Nat, (M = 5 \/ M = 6) /\
      exists e : Equiv (Fin 17) (ZetaIndex T),
        (forall k, (e k).val = seventeenPoint H k) /\
        (forall k, analyticOrderNatAt riemannZeta (e k).val =
          seventeenRootMultiplicity M k) := by
  have hp : 0 < (zetaSpectrum T).weakFifthUnitMass := by
    rwa [zetaSpectrum_weakFifthUnitMass]
  have hc : Fintype.card (ZetaIndex T) = 17 := by
    simpa only [Fintype.card_coe] using hCard
  exact (zetaSpectrum T).fifth_minimal_configuration_classification
    (zeta_fifth_equality_spectrum T hEq) hp hc

theorem zeta_readout_fifth_minimal_configuration (G : Complex -> Complex)
    (hG : AnalyticOnNhd Complex G {s : Complex | 0 < s.re /\ s.re < 1})
    (T : Real) (r2 r4 : Complex -> Complex)
    (h2 : forall rho, Membership.mem (upperZeroValues T) rho -> Filter.Tendsto
      (fun s => (s - rho) * affinePowerReadout (zetaMultiplicityReadout G) 2 s)
      (nhdsWithin rho (Set.compl {rho})) (nhds (r2 rho)))
    (h4 : forall rho, Membership.mem (upperZeroValues T) rho -> Filter.Tendsto
      (fun s => (s - rho) * affinePowerReadout (zetaMultiplicityReadout G) 4 s)
      (nhdsWithin rho (Set.compl {rho})) (nhds (r4 rho)))
    (hEq : ((upperZeroValues T).filter (fun rho =>
        (r2 rho * (rho + (2 : Complex) - 1)).im < 0 \/
          (r4 rho * (rho + (4 : Complex) - 1)).im < 0)).sum zetaSquareMass =
      39 * (jointWeakSupport 2 4 T).sum zetaUnitMassAt +
        (jointWeakSupport 2 4 T).sum zetaRepeatedUnitAt +
        4 * (jointWeakSupport 2 4 T).sum zetaFifthUnitAt)
    (hPos : 0 < (jointWeakSupport 2 4 T).sum zetaFifthUnitAt) :
    17 <= (upperZeroValues T).card /\
      ((upperZeroValues T).card = 17 ->
        exists H : Real, 0 < H /\ exists M : Nat, (M = 5 \/ M = 6) /\
          exists e : Equiv (Fin 17) (ZetaIndex T),
            (forall k, (e k).val = seventeenPoint H k) /\
            (forall k, analyticOrderNatAt riemannZeta (e k).val =
              seventeenRootMultiplicity M k)) := by
  have he : (jointCarrierSupport 2 4 T).sum zetaSquareMass =
      39 * (jointWeakSupport 2 4 T).sum zetaUnitMassAt +
        (jointWeakSupport 2 4 T).sum zetaRepeatedUnitAt +
        4 * (jointWeakSupport 2 4 T).sum zetaFifthUnitAt := by
    rw [joint_readout_carrier_eq G hG 2 4 T (by norm_num) (by norm_num) r2 r4 h2 h4]
    exact hEq
  exact And.intro (zeta_fifth_equality_card_minimum T he hPos)
    (zeta_fifth_minimal_configuration T he hPos)

end PrimeFactorOscillations.CarmichaelDyadicSharpness


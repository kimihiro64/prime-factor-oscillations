/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.CarmichaelTripleMultiplicity
import PrimeFactorOscillations.Assembly.CarmichaelZetaMultiplicityCarrier

/-!
# Actual zeta multiplicity support and triple-zero certificates

Every finite height cutoff and every complete compensation reference is
retained. No RH or simplicity assumption is made. The fixed strip is supplied
by the existing unconditional 7/8 result; no improvement of that boundary
is asserted.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations.CarmichaelDyadicSharpness

open DirichletCompensatedProbe CarmichaelWeightedSignal CarmichaelStripCarrier

def zetaUnitMassAt (rho : Complex) : Real :=
  1 / rho.im ^ 2

def zetaRepeatedUnitAt (rho : Complex) : Real :=
  if 2 <= analyticOrderNatAt riemannZeta rho then zetaUnitMassAt rho else 0

def zetaTripleExcessAt (rho : Complex) : Real :=
  ((analyticOrderNatAt riemannZeta rho - 2 : Nat) : Real) / rho.im ^ 2

theorem zetaSpectrum_weakUnitMass (T : Real) :
    (zetaSpectrum T).weakUnitMass = (jointWeakSupport 2 4 T).sum zetaUnitMassAt := by
  classical
  unfold ReflectedSpectrum.weakUnitMass ReflectedSpectrum.weakIndices
  simp_rw [zetaSpectrum_rowOrder T 2 (by norm_num),
    zetaSpectrum_rowOrder T 4 (by norm_num)]
  exact sum_zetaIndex_filter T
    (fun rho => (analyticOrderNatAt riemannZeta rho : Real) <=
        2 * (analyticOrderNatAt riemannZeta (powerMap 2 rho) : Real) /\
      (analyticOrderNatAt riemannZeta rho : Real) <=
        4 * (analyticOrderNatAt riemannZeta (powerMap 4 rho) : Real)) zetaUnitMassAt

theorem zetaSpectrum_weakRepeatedUnitMass (T : Real) :
    (zetaSpectrum T).weakRepeatedUnitMass =
      (jointWeakSupport 2 4 T).sum zetaRepeatedUnitAt := by
  classical
  unfold ReflectedSpectrum.weakRepeatedUnitMass ReflectedSpectrum.weakIndices
  simp_rw [zetaSpectrum_rowOrder T 2 (by norm_num),
    zetaSpectrum_rowOrder T 4 (by norm_num)]
  exact sum_zetaIndex_filter T
    (fun rho => (analyticOrderNatAt riemannZeta rho : Real) <=
        2 * (analyticOrderNatAt riemannZeta (powerMap 2 rho) : Real) /\
      (analyticOrderNatAt riemannZeta rho : Real) <=
        4 * (analyticOrderNatAt riemannZeta (powerMap 4 rho) : Real)) zetaRepeatedUnitAt

theorem zetaSpectrum_weakTripleExcessMass (T : Real) :
    (zetaSpectrum T).weakTripleExcessMass =
      (jointWeakSupport 2 4 T).sum zetaTripleExcessAt := by
  classical
  unfold ReflectedSpectrum.weakTripleExcessMass ReflectedSpectrum.weakIndices
  simp_rw [zetaSpectrum_rowOrder T 2 (by norm_num),
    zetaSpectrum_rowOrder T 4 (by norm_num)]
  exact sum_zetaIndex_filter T
    (fun rho => (analyticOrderNatAt riemannZeta rho : Real) <=
        2 * (analyticOrderNatAt riemannZeta (powerMap 2 rho) : Real) /\
      (analyticOrderNatAt riemannZeta rho : Real) <=
        4 * (analyticOrderNatAt riemannZeta (powerMap 4 rho) : Real)) zetaTripleExcessAt

theorem zeta_carrier_multiplicity_support_bound (T : Real) :
    39 * (jointWeakSupport 2 4 T).sum zetaUnitMassAt +
        (jointWeakSupport 2 4 T).sum zetaRepeatedUnitAt <=
      (jointCarrierSupport 2 4 T).sum zetaSquareMass := by
  have h := (zetaSpectrum T).carrier_multiplicity_support_bound
  rw [zetaSpectrum_carrierMass, zetaSpectrum_weakUnitMass,
    zetaSpectrum_weakRepeatedUnitMass] at h
  exact h

theorem zeta_carrier_triple_excess_bound (T : Real) :
    (20 / 21 : Real) * (upperZeroValues T).sum zetaSquareMass <=
      (jointCarrierSupport 2 4 T).sum zetaSquareMass +
        (20 / 21 : Real) * (jointWeakSupport 2 4 T).sum zetaTripleExcessAt := by
  have h := (zetaSpectrum T).carrier_triple_excess_bound
  rw [zetaSpectrum_totalMass, zetaSpectrum_carrierMass,
    zetaSpectrum_weakTripleExcessMass] at h
  exact h

theorem zeta_triple_weak_zero_of_deficit (T : Real)
    (hDeficit : (jointCarrierSupport 2 4 T).sum zetaSquareMass <
      (20 / 21 : Real) * (upperZeroValues T).sum zetaSquareMass) :
    exists rho : Complex, Membership.mem (jointWeakSupport 2 4 T) rho /\
      3 <= analyticOrderNatAt riemannZeta rho := by
  classical
  have hd : (zetaSpectrum T).carrierMass < (20 / 21 : Real) * (zetaSpectrum T).totalMass := by
    rw [zetaSpectrum_carrierMass, zetaSpectrum_totalMass]
    exact hDeficit
  choose i hi hm using (zetaSpectrum T).triple_weak_atom_of_deficit hd
  have hw := (Finset.mem_filter.mp hi).2
  rw [zetaSpectrum_rowOrder T 2 (by norm_num),
    zetaSpectrum_rowOrder T 4 (by norm_num)] at hw
  exact Exists.intro i.val
    (And.intro (Finset.mem_filter.mpr (And.intro i.property hw)) hm)

theorem zeta_readout_carrier_triple_bound (G : Complex -> Complex)
    (hG : AnalyticOnNhd Complex G {s : Complex | 0 < s.re /\ s.re < 1})
    (T : Real) (r2 r4 : Complex -> Complex)
    (h2 : forall rho, Membership.mem (upperZeroValues T) rho -> Filter.Tendsto
      (fun s => (s - rho) * affinePowerReadout (zetaMultiplicityReadout G) 2 s)
      (nhdsWithin rho (Set.compl {rho})) (nhds (r2 rho)))
    (h4 : forall rho, Membership.mem (upperZeroValues T) rho -> Filter.Tendsto
      (fun s => (s - rho) * affinePowerReadout (zetaMultiplicityReadout G) 4 s)
      (nhdsWithin rho (Set.compl {rho})) (nhds (r4 rho))) :
    (20 / 21 : Real) * (upperZeroValues T).sum zetaSquareMass <=
      ((upperZeroValues T).filter (fun rho =>
        (r2 rho * (rho + (2 : Complex) - 1)).im < 0 \/
          (r4 rho * (rho + (4 : Complex) - 1)).im < 0)).sum zetaSquareMass +
        (20 / 21 : Real) * (jointWeakSupport 2 4 T).sum zetaTripleExcessAt := by
  have h := zeta_carrier_triple_excess_bound T
  rw [joint_readout_carrier_eq G hG 2 4 T (by norm_num) (by norm_num) r2 r4 h2 h4] at h
  simpa using h

end PrimeFactorOscillations.CarmichaelDyadicSharpness

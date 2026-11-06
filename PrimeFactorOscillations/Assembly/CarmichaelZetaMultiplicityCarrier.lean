/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.CarmichaelDyadicSharpness
import PrimeFactorOscillations.Assembly.CarmichaelZetaFiniteSpectrum

/-!
# Unconditional multiplicity certificates from actual zeta carriers

The exact quadratic-quartic compensated carrier retains at least 39/40 of
the total inverse-square-height mass after charging the full common-weak
excess multiplicity. A strict carrier deficit certifies a repeated weak zero.
All finite windows and reference orders are actual zeta data; RH is not assumed.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations.CarmichaelDyadicSharpness

open DirichletCompensatedProbe CarmichaelWeightedSignal CarmichaelStripCarrier

def zetaExcessAt (rho : Complex) : Real :=
  ((analyticOrderNatAt riemannZeta rho : Real) - 1) / rho.im ^ 2

theorem sum_zetaIndex_filter (T : Real) (p : Complex -> Prop) [DecidablePred p]
    (f : Complex -> Real) :
    ((Finset.univ : Finset (ZetaIndex T)).filter (fun i => p i.val)).sum
        (fun i => f i.val) =
      ((upperZeroValues T).filter p).sum f := by
  classical
  rw [Finset.sum_filter, Finset.sum_filter]
  exact sum_zetaIndex T (fun rho => if p rho then f rho else 0)

theorem zetaSpectrum_carrierMass (T : Real) :
    (zetaSpectrum T).carrierMass = (jointCarrierSupport 2 4 T).sum zetaSquareMass := by
  classical
  have hmass : forall i : ZetaIndex T, (zetaSpectrum T).mass i = zetaSquareMass i.val := by
    intro i
    change (analyticOrderNatAt riemannZeta i.val : Real) / i.val.im ^ 2 =
      (analyticOrderNatAt riemannZeta i.val : Real) * (1 / i.val.im ^ 2)
    ring
  unfold ReflectedSpectrum.carrierMass ReflectedSpectrum.carrierIndices
  simp_rw [zetaSpectrum_rowOrder T 2 (by norm_num),
    zetaSpectrum_rowOrder T 4 (by norm_num), hmass]
  exact sum_zetaIndex_filter T
    (fun rho => 2 * (analyticOrderNatAt riemannZeta (powerMap 2 rho) : Real) <
        (analyticOrderNatAt riemannZeta rho : Real) \/
      4 * (analyticOrderNatAt riemannZeta (powerMap 4 rho) : Real) <
        (analyticOrderNatAt riemannZeta rho : Real)) zetaSquareMass

theorem zetaSpectrum_weakExcessMass (T : Real) :
    (zetaSpectrum T).weakExcessMass = (jointWeakSupport 2 4 T).sum zetaExcessAt := by
  classical
  unfold ReflectedSpectrum.weakExcessMass ReflectedSpectrum.weakIndices
  simp_rw [zetaSpectrum_rowOrder T 2 (by norm_num),
    zetaSpectrum_rowOrder T 4 (by norm_num)]
  exact sum_zetaIndex_filter T
    (fun rho => (analyticOrderNatAt riemannZeta rho : Real) <=
        2 * (analyticOrderNatAt riemannZeta (powerMap 2 rho) : Real) /\
      (analyticOrderNatAt riemannZeta rho : Real) <=
        4 * (analyticOrderNatAt riemannZeta (powerMap 4 rho) : Real)) zetaExcessAt

theorem zeta_carrier_excess_bound (T : Real) :
    (39 / 40 : Real) * (upperZeroValues T).sum zetaSquareMass <=
      (jointCarrierSupport 2 4 T).sum zetaSquareMass +
        (jointWeakSupport 2 4 T).sum zetaExcessAt := by
  have h := (zetaSpectrum T).carrier_excess_bound
  rw [zetaSpectrum_totalMass, zetaSpectrum_carrierMass, zetaSpectrum_weakExcessMass] at h
  exact h

theorem zeta_carrier_max_bound (T : Real) :
    max ((11 / 12 : Real) * (upperZeroValues T).sum zetaSquareMass)
      ((39 / 40 : Real) * (upperZeroValues T).sum zetaSquareMass -
        (jointWeakSupport 2 4 T).sum zetaExcessAt) <=
      (jointCarrierSupport 2 4 T).sum zetaSquareMass := by
  have h := (zetaSpectrum T).carrier_max_bound
  rw [zetaSpectrum_totalMass, zetaSpectrum_carrierMass, zetaSpectrum_weakExcessMass] at h
  exact h

theorem zeta_simple_window_carrier_bound (T : Real)
    (hSimple : forall rho, Membership.mem (upperZeroValues T) rho ->
      analyticOrderNatAt riemannZeta rho = 1) :
    (39 / 40 : Real) * (upperZeroValues T).sum zetaSquareMass <=
      (jointCarrierSupport 2 4 T).sum zetaSquareMass := by
  have h := (zetaSpectrum T).simple_carrier_bound (fun i => hSimple i.val i.property)
  rw [zetaSpectrum_totalMass, zetaSpectrum_carrierMass] at h
  exact h

theorem zeta_repeated_weak_zero_of_deficit (T : Real)
    (hDeficit : (jointCarrierSupport 2 4 T).sum zetaSquareMass <
      (39 / 40 : Real) * (upperZeroValues T).sum zetaSquareMass) :
    exists rho : Complex, Membership.mem (jointWeakSupport 2 4 T) rho /\
      2 <= analyticOrderNatAt riemannZeta rho := by
  classical
  have hd : (zetaSpectrum T).carrierMass < (39 / 40 : Real) * (zetaSpectrum T).totalMass := by
    rw [zetaSpectrum_carrierMass, zetaSpectrum_totalMass]
    exact hDeficit
  choose i hi hm using (zetaSpectrum T).repeated_weak_atom_of_deficit hd
  have hw := (Finset.mem_filter.mp hi).2
  rw [zetaSpectrum_rowOrder T 2 (by norm_num),
    zetaSpectrum_rowOrder T 4 (by norm_num)] at hw
  exact Exists.intro i.val
    (And.intro (Finset.mem_filter.mpr (And.intro i.property hw)) hm)

theorem zeta_readout_carrier_max_bound (G : Complex -> Complex)
    (hG : AnalyticOnNhd Complex G {s : Complex | 0 < s.re /\ s.re < 1})
    (T : Real) (r2 r4 : Complex -> Complex)
    (h2 : forall rho, Membership.mem (upperZeroValues T) rho -> Filter.Tendsto
      (fun s => (s - rho) * affinePowerReadout (zetaMultiplicityReadout G) 2 s)
      (nhdsWithin rho (Set.compl {rho})) (nhds (r2 rho)))
    (h4 : forall rho, Membership.mem (upperZeroValues T) rho -> Filter.Tendsto
      (fun s => (s - rho) * affinePowerReadout (zetaMultiplicityReadout G) 4 s)
      (nhdsWithin rho (Set.compl {rho})) (nhds (r4 rho))) :
    max ((11 / 12 : Real) * (upperZeroValues T).sum zetaSquareMass)
      ((39 / 40 : Real) * (upperZeroValues T).sum zetaSquareMass -
        (jointWeakSupport 2 4 T).sum zetaExcessAt) <=
      ((upperZeroValues T).filter (fun rho =>
        (r2 rho * (rho + (2 : Complex) - 1)).im < 0 \/
          (r4 rho * (rho + (4 : Complex) - 1)).im < 0)).sum zetaSquareMass := by
  have h := zeta_carrier_max_bound T
  rw [joint_readout_carrier_eq G hG 2 4 T (by norm_num) (by norm_num) r2 r4 h2 h4] at h
  simpa using h

end PrimeFactorOscillations.CarmichaelDyadicSharpness

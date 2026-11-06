/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.CarmichaelTwoTailBound
import PrimeFactorOscillations.Assembly.CarmichaelZetaFifthMultiplicity

/-!
# Actual zeta spatial multiplicity-tail inequalities

The offcritical triple tail and fifth tail obey both signed carrier budgets.
A deficit below the factor-sixteen bound certifies an offcritical weak triple.
Every height window and both full compensated readouts are retained; no RH
hypothesis is used.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations.CarmichaelDyadicSharpness

open DirichletCompensatedProbe CarmichaelWeightedSignal CarmichaelStripCarrier

namespace ReflectedSpectrum

theorem weakOffTripleUnitMass_eq_sum {I : Type*} [Fintype I] {sigma : Real}
    (S : ReflectedSpectrum I sigma) :
    S.weakOffTripleUnitMass = S.weakIndices.sum (fun i =>
      if (S.point i).re < 1 / 2 /\ 3 <= S.mult i then S.unitMass i else 0) := by
  classical
  unfold weakOffTripleUnitMass
  calc
    _ = S.weakIndices.sum S.offTripleUnitAt := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro i _ hn
      simp [offTripleUnitAt, hn]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i hi
      simp only [offTripleUnitAt, hi, true_and]

end ReflectedSpectrum

def zetaOffTripleUnitAt (rho : Complex) : Real :=
  if rho.re < 1 / 2 /\ 3 <= analyticOrderNatAt riemannZeta rho then
    zetaUnitMassAt rho else 0

theorem zetaSpectrum_weakOffTripleUnitMass (T : Real) :
    (zetaSpectrum T).weakOffTripleUnitMass =
      (jointWeakSupport 2 4 T).sum zetaOffTripleUnitAt := by
  classical
  rw [ReflectedSpectrum.weakOffTripleUnitMass_eq_sum]
  unfold ReflectedSpectrum.weakIndices
  simp_rw [zetaSpectrum_rowOrder T 2 (by norm_num),
    zetaSpectrum_rowOrder T 4 (by norm_num)]
  exact sum_zetaIndex_filter T
    (fun rho => (analyticOrderNatAt riemannZeta rho : Real) <=
        2 * (analyticOrderNatAt riemannZeta (powerMap 2 rho) : Real) /\
      (analyticOrderNatAt riemannZeta rho : Real) <=
        4 * (analyticOrderNatAt riemannZeta (powerMap 4 rho) : Real)) zetaOffTripleUnitAt

theorem zeta_carrier_offTriple_bound (T : Real) :
    39 * (jointWeakSupport 2 4 T).sum zetaUnitMassAt +
        (jointWeakSupport 2 4 T).sum zetaRepeatedUnitAt +
        (jointWeakSupport 2 4 T).sum zetaOffTripleUnitAt <=
      (jointCarrierSupport 2 4 T).sum zetaSquareMass := by
  have h := (zetaSpectrum T).carrier_offTriple_bound
  rw [zetaSpectrum_carrierMass, zetaSpectrum_weakUnitMass,
    zetaSpectrum_weakRepeatedUnitMass, zetaSpectrum_weakOffTripleUnitMass] at h
  exact h

theorem zeta_carrier_fifth_offTriple_bound (T : Real) :
    39 * (jointWeakSupport 2 4 T).sum zetaUnitMassAt +
        (jointWeakSupport 2 4 T).sum zetaRepeatedUnitAt +
        16 * (jointWeakSupport 2 4 T).sum zetaFifthUnitAt <=
      (jointCarrierSupport 2 4 T).sum zetaSquareMass +
        3 * (jointWeakSupport 2 4 T).sum zetaOffTripleUnitAt := by
  have h := (zetaSpectrum T).carrier_fifth_offTriple_bound
  rw [zetaSpectrum_carrierMass, zetaSpectrum_weakUnitMass,
    zetaSpectrum_weakRepeatedUnitMass, zetaSpectrum_weakOffTripleUnitMass,
    zetaSpectrum_weakFifthUnitMass] at h
  exact h

theorem zeta_carrier_two_tail_bound (T a b : Real)
    (ha : a <= 16) (hb : b <= 1) (hab : a + 4 * b <= 4) :
    39 * (jointWeakSupport 2 4 T).sum zetaUnitMassAt +
        (jointWeakSupport 2 4 T).sum zetaRepeatedUnitAt +
        a * (jointWeakSupport 2 4 T).sum zetaFifthUnitAt +
        b * (jointWeakSupport 2 4 T).sum zetaOffTripleUnitAt <=
      (jointCarrierSupport 2 4 T).sum zetaSquareMass := by
  have h := (zetaSpectrum T).carrier_two_tail_bound a b ha hb hab
  rw [zetaSpectrum_carrierMass, zetaSpectrum_weakUnitMass,
    zetaSpectrum_weakRepeatedUnitMass, zetaSpectrum_weakOffTripleUnitMass,
    zetaSpectrum_weakFifthUnitMass] at h
  exact h

theorem zeta_fifth_tail_bound_of_no_offTriple (T : Real)
    (hZero : (jointWeakSupport 2 4 T).sum zetaOffTripleUnitAt = 0) :
    (jointWeakSupport 2 4 T).sum zetaFifthUnitAt <=
      ((jointCarrierSupport 2 4 T).sum zetaSquareMass -
        39 * (jointWeakSupport 2 4 T).sum zetaUnitMassAt -
          (jointWeakSupport 2 4 T).sum zetaRepeatedUnitAt) / 16 := by
  have h := zeta_carrier_fifth_offTriple_bound T
  rw [hZero] at h
  linarith

theorem zeta_offTriple_eq_four_fifth_of_fifth_equality (T : Real)
    (hEq : (jointCarrierSupport 2 4 T).sum zetaSquareMass =
      39 * (jointWeakSupport 2 4 T).sum zetaUnitMassAt +
        (jointWeakSupport 2 4 T).sum zetaRepeatedUnitAt +
          4 * (jointWeakSupport 2 4 T).sum zetaFifthUnitAt) :
    (jointWeakSupport 2 4 T).sum zetaOffTripleUnitAt =
      4 * (jointWeakSupport 2 4 T).sum zetaFifthUnitAt := by
  have h1 := zeta_carrier_offTriple_bound T
  have h2 := zeta_carrier_fifth_offTriple_bound T
  linarith

theorem zeta_offcritical_triple_of_sixteen_deficit (T : Real)
    (hDeficit : (jointCarrierSupport 2 4 T).sum zetaSquareMass <
      39 * (jointWeakSupport 2 4 T).sum zetaUnitMassAt +
        (jointWeakSupport 2 4 T).sum zetaRepeatedUnitAt +
          16 * (jointWeakSupport 2 4 T).sum zetaFifthUnitAt) :
    exists rho : Complex, Membership.mem (jointWeakSupport 2 4 T) rho /\
      rho.re < 1 / 2 /\ 3 <= analyticOrderNatAt riemannZeta rho := by
  classical
  by_contra hNone
  have hZero : (jointWeakSupport 2 4 T).sum zetaOffTripleUnitAt = 0 := by
    apply Finset.sum_eq_zero
    intro rho hrho
    unfold zetaOffTripleUnitAt
    apply if_neg
    intro hMarker
    exact hNone (Exists.intro rho (And.intro hrho hMarker))
  have h := zeta_carrier_fifth_offTriple_bound T
  rw [hZero] at h
  linarith

theorem zeta_readout_two_tail_bound (G : Complex -> Complex)
    (hG : AnalyticOnNhd Complex G {s : Complex | 0 < s.re /\ s.re < 1})
    (T a b : Real) (ha : a <= 16) (hb : b <= 1) (hab : a + 4 * b <= 4)
    (r2 r4 : Complex -> Complex)
    (h2 : forall rho, Membership.mem (upperZeroValues T) rho -> Filter.Tendsto
      (fun s => (s - rho) * affinePowerReadout (zetaMultiplicityReadout G) 2 s)
      (nhdsWithin rho (Set.compl {rho})) (nhds (r2 rho)))
    (h4 : forall rho, Membership.mem (upperZeroValues T) rho -> Filter.Tendsto
      (fun s => (s - rho) * affinePowerReadout (zetaMultiplicityReadout G) 4 s)
      (nhdsWithin rho (Set.compl {rho})) (nhds (r4 rho))) :
    39 * (jointWeakSupport 2 4 T).sum zetaUnitMassAt +
        (jointWeakSupport 2 4 T).sum zetaRepeatedUnitAt +
        a * (jointWeakSupport 2 4 T).sum zetaFifthUnitAt +
        b * (jointWeakSupport 2 4 T).sum zetaOffTripleUnitAt <=
      ((upperZeroValues T).filter (fun rho =>
        (r2 rho * (rho + (2 : Complex) - 1)).im < 0 \/
          (r4 rho * (rho + (4 : Complex) - 1)).im < 0)).sum zetaSquareMass := by
  have h := zeta_carrier_two_tail_bound T a b ha hb hab
  rw [joint_readout_carrier_eq G hG 2 4 T (by norm_num) (by norm_num) r2 r4 h2 h4] at h
  exact h

end PrimeFactorOscillations.CarmichaelDyadicSharpness

/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.CarmichaelMinimalCarrier
import PrimeFactorOscillations.Assembly.CarmichaelNinthMass
import PrimeFactorOscillations.Assembly.CarmichaelSeventhWitness
import PrimeFactorOscillations.Assembly.CarmichaelZetaGlobalExcess

/-!
# The sharp global multiplicity-profile coefficient vector

The vector (4,16,1) is valid and Pareto optimal. Three exact finite spectra
suffice for necessity; validity holds on every finite reflected spectrum.
This does not claim a classification of all other coefficient triples.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations.CarmichaelDyadicSharpness

def GlobalExcessCoefficientBound (a b c : Real) : Prop :=
  forall n : Nat, forall S : ReflectedSpectrum (Fin n) (7 / 8),
    39 * S.weakUnitMass + S.weakRepeatedUnitMass +
      a * S.weakFifthUnitMass + b * S.weakNinthUnitMass +
        c * S.globalOffcriticalExcess <= S.carrierMass

theorem global_excess_coefficients_valid : GlobalExcessCoefficientBound 4 16 1 := by
  intro n S
  simpa only [one_mul] using S.carrier_global_excess_bound

theorem global_excess_coefficient_constraints (a b c : Real)
    (hAll : GlobalExcessCoefficientBound a b c) :
    a <= 4 /\ a + 4 * c <= 8 /\ 5 * a + b + 8 * c <= 44 := by
  have h5 := hAll 17 (seventeenSpectrum 1 (by norm_num))
  rw [seventeenSpectrum_carrierMass, seventeenSpectrum_weakUnitMass,
    seventeenSpectrum_weakRepeatedUnitMass, seventeenSpectrum_weakFifthUnitMass,
    seventeenSpectrum_weakNinthUnitMass, seventeenSpectrum_globalOffcriticalExcess] at h5
  norm_num at h5
  have h7 := hAll 17 (seventhSpectrum 1 (by norm_num))
  rw [seventhSpectrum_carrierMass, seventhSpectrum_weakUnitMass,
    seventhSpectrum_weakRepeatedUnitMass, seventhSpectrum_weakFifthUnitMass,
    seventhSpectrum_weakNinthUnitMass, seventhSpectrum_globalOffcriticalExcess] at h7
  norm_num at h7
  have h9 := hAll 29 (ninthSpectrum 1 (by norm_num))
  rw [ninthSpectrum_carrierMass, ninthSpectrum_weakUnitMass,
    ninthSpectrum_weakRepeatedUnitMass, ninthSpectrum_weakFifthUnitMass,
    ninthSpectrum_weakNinthUnitMass, ninthSpectrum_globalOffcriticalExcess] at h9
  norm_num at h9
  exact And.intro (by linarith) (And.intro (by linarith) (by linarith))

theorem global_excess_coefficients_pareto_optimal (a b c : Real)
    (ha : 4 <= a) (hb : 16 <= b) (hc : 1 <= c)
    (hAll : GlobalExcessCoefficientBound a b c) :
    a = 4 /\ b = 16 /\ c = 1 := by
  have h := global_excess_coefficient_constraints a b c hAll
  have haEq : a = 4 := by linarith [h.1]
  have hcEq : c = 1 := by linarith [h.2.1]
  have hbEq : b = 16 := by linarith [h.2.2]
  exact And.intro haEq (And.intro hbEq hcEq)

end PrimeFactorOscillations.CarmichaelDyadicSharpness


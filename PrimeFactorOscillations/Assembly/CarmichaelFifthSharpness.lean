/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.CarmichaelMultiplicitySupportSharpness
import PrimeFactorOscillations.Assembly.CarmichaelSeventeenMass
import PrimeFactorOscillations.Assembly.CarmichaelZetaFifthMultiplicity

/-!
# Optimal fifth-multiplicity stability coefficient

The universal coefficient in C>=39P+Q+cR5 is exactly four.
The seventeen-point model attains equality for every positive height,
with the full nonzero complex readout and all reference orders retained.
Previous sharp support and zeta consumers remain imported.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations.CarmichaelDyadicSharpness

theorem universal_fifth_support_coefficient_iff (c : Real) :
    (forall (I : Type) [Fintype I] (S : ReflectedSpectrum I (7 / 8)),
      39 * S.weakUnitMass + S.weakRepeatedUnitMass +
        c * S.weakFifthUnitMass <= S.carrierMass) <-> c <= 4 := by
  constructor
  . intro h
    have hWitness := h (Fin 17) (seventeenSpectrum 1 (by norm_num : (0 : Real) < 1))
    rw [seventeenSpectrum_weakUnitMass, seventeenSpectrum_weakRepeatedUnitMass,
      seventeenSpectrum_weakFifthUnitMass, seventeenSpectrum_carrierMass] at hWitness
    norm_num at hWitness
    linarith
  . intro hc I inst S
    have h := S.carrier_fifth_support_bound
    have hCoeff := mul_le_mul_of_nonneg_right hc S.weakFifthUnitMass_nonneg
    linarith

theorem seventeenSpectrum_joint_readout_carrier (H : Real) (hH : 0 < H) :
    (seventeenSpectrum H hH).carrierIndices = Finset.univ.filter (fun i : Fin 17 =>
      (CarmichaelTraceSharpness.atomicPowerResidue (seventeenSpectrum H hH).point
          (seventeenSpectrum H hH).mult 2 ((seventeenSpectrum H hH).point i) *
        ((seventeenSpectrum H hH).point i + ((2 : Real) : Complex) - 1)).im < 0 \/
      (CarmichaelTraceSharpness.atomicPowerResidue (seventeenSpectrum H hH).point
          (seventeenSpectrum H hH).mult 4 ((seventeenSpectrum H hH).point i) *
        ((seventeenSpectrum H hH).point i + ((4 : Real) : Complex) - 1)).im < 0) := by
  classical
  apply Finset.ext
  intro i
  simp only [ReflectedSpectrum.carrierIndices, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [seventeenSpectrum_projection_negative_iff H hH 2 i,
    seventeenSpectrum_projection_negative_iff H hH 4 i]

end PrimeFactorOscillations.CarmichaelDyadicSharpness

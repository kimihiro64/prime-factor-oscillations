/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import OAI.NumberTheory.DirichletL.Detector.SourcePrimeFactor
import OAI.NumberTheory.DirichletL.Detector.SpectralWeights

/-!
# PowerSampleNormalization

Maintained extraction of completed detector/packet proof components.
All original theorem hypotheses and retained proof bodies are preserved.
This module alone asserts no improved zero-free boundary.
-/

set_option autoImplicit false
set_option Elab.async false

namespace OAI.SevenEighths.ProbePowerGauss
noncomputable section
open ActualEisensteinCubic ConcretePrimeRowBridge ProbePrimePower
open ProbePhysical ProbeEuler CubicEisenstein CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O
local notation "Res" p => HasQuotient.Quotient O (Ideal.span {p})

theorem corrected_diagonal_raw (p : O) (hp : Prime p)
    [(Ideal.span {p} : Ideal O).IsMaximal]
    (hg : Not (Membership.mem (Ideal.span {p}) goodLambda))
    (hchar : Not (ringChar (Res p) = 2))
    (hprimary : Dvd.dvd (goodLambda ^ 2) (p - 1))
    (hs : Supported (Ideal.span {p})) :
    (localGamma p hp.ne_zero hg 2 * star (FiniteGaussPhase.angularFactor p) *
      star (ProbePhase.G p) /
      (Real.sqrt (Ideal.absNorm (Ideal.span {p}) : Real) : Complex)) *
        primeGauss p hp.ne_zero (CompletedGauss.actualSextic (Ideal.span {p}) hg) 1 = -1 := by
  have hQ : 0 < (Ideal.absNorm (Ideal.span {p}) : Real) := by
    exact_mod_cast Nat.pos_of_ne_zero
      (Ideal.absNorm_eq_zero_iff.not.mpr (Ideal.span_singleton_eq_bot.not.mpr hp.ne_zero))
  have hroot : Not ((Real.sqrt (Ideal.absNorm (Ideal.span {p}) : Real) : Complex) = 0) := by
    exact_mod_cast (Real.sqrt_pos.mpr hQ).ne'
  have hgamma : Not (localGamma p hp.ne_zero hg 1 = 0) := by
    have hn := localGamma_norm_one p hp.ne_zero hg hchar 1 (by decide) (by decide)
    intro he
    rw [he, norm_zero] at hn
    exact zero_ne_one hn
  rw [corrected_prime_cubic_signal p hp.ne_zero hg hchar hprimary hs,
    firstGauss_eq_gamma_sqrt p hp hg]
  field_simp [hroot, hgamma]

theorem diagonal_mellin_exponent (Q : Real) (hQ : 0 < Q) (t w z : Complex) :
    (Q : Complex) ^ (-t) * (Q : Complex) ^ (z - w - 1) =
      (Q : Complex) ^ (-(t + w + 1 - z)) := by
  have hn : Not ((Q : Complex) = 0) := by exact_mod_cast hQ.ne'
  rw [<- Complex.cpow_add _ _ hn]
  congr 1
  ring

end
end OAI.SevenEighths.ProbePowerGauss

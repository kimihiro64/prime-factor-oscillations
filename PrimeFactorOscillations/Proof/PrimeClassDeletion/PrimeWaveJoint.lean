/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.DampedWaveBounds
import PrimeFactorOscillations.Helpers.FiniteJointWave
import PrimeFactorOscillations.Proof.PrimeClassDeletion.PrimeWaveCountBounds

/-!
# The complete joint-wave response on the actual greedy prime class

Every cutoff is real. All asymptotics use the same fixed class, including
the literal deleted-prime count. Arbitrary finite frequencies are covered
by a proved simultaneous recurrence, not an assumed common period.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.PrimeClassDeletion

open Filter
open PrimeFactorOscillations.PrimeClassSampling

theorem greedyPrime_almost_periodic_wave (b v0 : Real) (f : Real -> Real)
    (hb : 0 < b) (hbounded : exists A : Real, forall v : Real, abs (f v) <= A)
    (hc : UniformContinuous f) (hp : IsUniformAlmostPeriodicWave f)
    (hpos : 0 < f v0)
    (hsource : Tendsto (fun x : Real =>
      (primeClassThetaReal Set.univ x - x) / x ^ b - f (Real.log x))
      atTop (nhds 0)) :
    (And (UniformContinuous (dampedWaveEnvelope b f))
      (And (IsUniformAlmostPeriodicWave (dampedWaveEnvelope b f))
        (exists c : Real, And (0 < c)
          (And (forall v : Real, And (c <= dampedWaveEnvelope b f v)
            (dampedWaveEnvelope b f v <= waveSupNorm f))
            (And (Tendsto (fun x : Real => greedyPrimeRegulatorReal x / x ^ b -
                dampedWaveEnvelope b f (Real.log x)) atTop (nhds 0))
              (And (Tendsto (fun x : Real =>
                  primeClassThetaReal greedyDeletedPrimeClass x / x ^ b -
                    dampedWaveEnvelope b f (Real.log x)) atTop (nhds 0))
                (And (Tendsto (fun x : Real =>
                    ((primeClassPrefix greedyDeletedPrimeClass (Nat.floor x)).card : Real) /
                      (x ^ b / Real.log x) - dampedWaveEnvelope b f (Real.log x))
                    atTop (nhds 0))
                  (exists X : Real, And (2 <= X) (forall x : Real, X <= x ->
                    And ((c / 2) * (x ^ b / Real.log x) <=
                      ((primeClassPrefix greedyDeletedPrimeClass (Nat.floor x)).card : Real))
                      (((primeClassPrefix greedyDeletedPrimeClass (Nat.floor x)).card : Real) <=
                        (waveSupNorm f + 1) * (x ^ b / Real.log x))))))))))) := by
  choose A hA using hbounded
  choose c hlow using dampedWaveEnvelope_uniformAlmostPeriodic_lower b A v0 f
    hb.le hA hp hpos
  have hnorm := (waveSupNorm_bounds A f hA).2.1
  have hcounts := primeWaveCount_uniform_bounds b (waveSupNorm f) c f
    hb hnorm hlow.1 hlow.2 hsource
  refine And.intro (dampedWaveEnvelope_uniformContinuous b A f hb.le hA hc)
    (And.intro (dampedWaveEnvelope_uniformAlmostPeriodic b A f hb.le hA hp)
      (Exists.intro c (And.intro hlow.1 ?_)))
  exact And.intro (fun v => And.intro (hlow.2 v)
      (dampedWaveEnvelope_le_supNorm b A f hb.le hA v))
    (And.intro (primeWaveRecord_limit b A f hb hA hsource)
      (And.intro (primeWaveMass_limit b A f hb hA hsource)
        (And.intro (primeWaveCount_div_limit b A f hb hA hsource) hcounts)))

theorem greedyPrime_finite_joint_wave (b v0 : Real) (m : Nat)
    (A frequency phase : Fin m -> Real) (hb : 0 < b)
    (hpos : 0 < finiteJointWave m A frequency phase v0)
    (hsource : Tendsto (fun x : Real =>
      (primeClassThetaReal Set.univ x - x) / x ^ b -
        finiteJointWave m A frequency phase (Real.log x)) atTop (nhds 0)) :
    let f := finiteJointWave m A frequency phase
    (And (UniformContinuous (dampedWaveEnvelope b f))
      (And (IsUniformAlmostPeriodicWave (dampedWaveEnvelope b f))
        (exists c : Real, And (0 < c)
          (And (forall v : Real, And (c <= dampedWaveEnvelope b f v)
            (dampedWaveEnvelope b f v <= waveSupNorm f))
            (And (Tendsto (fun x : Real => greedyPrimeRegulatorReal x / x ^ b -
                dampedWaveEnvelope b f (Real.log x)) atTop (nhds 0))
              (And (Tendsto (fun x : Real =>
                  primeClassThetaReal greedyDeletedPrimeClass x / x ^ b -
                    dampedWaveEnvelope b f (Real.log x)) atTop (nhds 0))
                (And (Tendsto (fun x : Real =>
                    ((primeClassPrefix greedyDeletedPrimeClass (Nat.floor x)).card : Real) /
                      (x ^ b / Real.log x) - dampedWaveEnvelope b f (Real.log x))
                    atTop (nhds 0))
                  (exists X : Real, And (2 <= X) (forall x : Real, X <= x ->
                    And ((c / 2) * (x ^ b / Real.log x) <=
                      ((primeClassPrefix greedyDeletedPrimeClass (Nat.floor x)).card : Real))
                      (((primeClassPrefix greedyDeletedPrimeClass (Nat.floor x)).card : Real) <=
                        (waveSupNorm f + 1) * (x ^ b / Real.log x))))))))))) := by
  exact greedyPrime_almost_periodic_wave b v0 (finiteJointWave m A frequency phase)
    hb (Exists.intro (finiteJointAmplitude m A)
      (finiteJointWave_abs_le m A frequency phase))
    (finiteJointWave_uniformContinuous m A frequency phase)
    (finiteJointWave_uniformAlmostPeriodic m A frequency phase) hpos hsource

end PrimeFactorOscillations.PrimeClassDeletion

/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.DampedWaveBounds
import PrimeFactorOscillations.Helpers.DampedWavePeriodic
import PrimeFactorOscillations.Proof.PrimeClassDeletion.PrimeWaveCountBounds

/-!
# The full periodic-wave theorem for the actual fixed greedy prime class

All three limits use real cutoffs and the same retained and deleted classes.
The conclusion includes the literal count, its power-over-log scale, the
sup norm, the positive lower envelope and every sufficiently large cutoff.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.PrimeClassDeletion

open Filter
open PrimeFactorOscillations.PrimeClassSampling

theorem greedyPrime_periodic_wave (b T v0 : Real) (f : Real -> Real)
    (hb : 0 < b) (hT : 0 < T) (hc : Continuous f) (hp : Function.Periodic f T)
    (hpos : 0 < f v0)
    (hsource : Tendsto (fun x : Real =>
      (primeClassThetaReal Set.univ x - x) / x ^ b - f (Real.log x))
      atTop (nhds 0)) :
    And (0 < f v0 * Real.exp (-(b * T)))
      (And (Continuous (dampedWaveEnvelope b f))
        (And (Function.Periodic (dampedWaveEnvelope b f) T)
          (And (forall v : Real,
            And (f v0 * Real.exp (-(b * T)) <= dampedWaveEnvelope b f v)
              (dampedWaveEnvelope b f v <= waveSupNorm f))
            (And (Tendsto (fun x : Real => greedyPrimeRegulatorReal x / x ^ b -
                dampedWaveEnvelope b f (Real.log x)) atTop (nhds 0))
              (And (Tendsto (fun x : Real => primeClassThetaReal greedyDeletedPrimeClass x / x ^ b -
                  dampedWaveEnvelope b f (Real.log x)) atTop (nhds 0))
                (Tendsto (fun x : Real =>
                  ((primeClassPrefix greedyDeletedPrimeClass (Nat.floor x)).card : Real) /
                    (x ^ b / Real.log x) - dampedWaveEnvelope b f (Real.log x))
                  atTop (nhds 0))))))) := by
  choose A hA using periodic_real_exists_abs_bound T f hT hp hc
  have hregular := dampedWaveEnvelope_periodic_continuous b T f hb.le hT hp hc
  exact And.intro (mul_pos hpos (Real.exp_pos _)) (And.intro hregular.1
    (And.intro hregular.2 (And.intro (fun v => And.intro
      (dampedWaveEnvelope_periodic_lower b A T v0 f hb.le hA hT hp hpos v)
      (dampedWaveEnvelope_le_supNorm b A f hb.le hA v))
      (And.intro (primeWaveRecord_limit b A f hb hA hsource)
        (And.intro (primeWaveMass_limit b A f hb hA hsource)
          (primeWaveCount_div_limit b A f hb hA hsource))))))

theorem greedyPrime_periodic_wave_count_bounds (b T v0 : Real) (f : Real -> Real)
    (hb : 0 < b) (hT : 0 < T) (hc : Continuous f) (hp : Function.Periodic f T)
    (hpos : 0 < f v0)
    (hsource : Tendsto (fun x : Real =>
      (primeClassThetaReal Set.univ x - x) / x ^ b - f (Real.log x))
      atTop (nhds 0)) :
    exists X : Real, And (2 <= X) (forall x : Real, X <= x ->
      And (((f v0 * Real.exp (-(b * T))) / 2) * (x ^ b / Real.log x) <=
        ((primeClassPrefix greedyDeletedPrimeClass (Nat.floor x)).card : Real))
        (((primeClassPrefix greedyDeletedPrimeClass (Nat.floor x)).card : Real) <=
          (waveSupNorm f + 1) * (x ^ b / Real.log x))) := by
  choose A hA using periodic_real_exists_abs_bound T f hT hp hc
  have hnorm := (waveSupNorm_bounds A f hA).2.1
  exact primeWaveCount_uniform_bounds b (waveSupNorm f) (f v0 * Real.exp (-(b * T))) f
    hb hnorm (mul_pos hpos (Real.exp_pos _))
    (dampedWaveEnvelope_periodic_lower b (waveSupNorm f) T v0 f hb.le hnorm hT hp hpos)
    hsource

end PrimeFactorOscillations.PrimeClassDeletion

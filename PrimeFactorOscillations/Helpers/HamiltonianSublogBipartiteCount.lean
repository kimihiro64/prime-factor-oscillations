/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianCountDensity

/-! # Relative bipartite counts on a uniform positive logarithmic density range

This consumes the full signed first-correction estimate. The admissible
density depends only on the fixed gap, never on the matrix or its order.
-/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations

def hamiltonianSublogCountDensity (rho : Real) : Real :=
  1 / (1 + abs (hamiltonianSpectralKappa rho))

theorem hamiltonian_sublog_density_positive (rho : Real) :
    0 < hamiltonianSublogCountDensity rho := by
  unfold hamiltonianSublogCountDensity
  positivity

theorem hamiltonian_sublog_density_amplification_exponent (rho : Real) :
    hamiltonianSpectralKappa rho * hamiltonianSublogCountDensity rho <= 1 := by
  let K := hamiltonianSpectralKappa rho
  have hDen : 0 < 1 + abs K := by positivity
  have hUpper : K <= 1 + abs K := by linarith only [le_abs_self K]
  have h := mul_le_mul_of_nonneg_right hUpper (one_div_nonneg.mpr hDen.le)
  have hId : (1 + abs K) * (1 / (1 + abs K)) = 1 := by field_simp [ne_of_gt hDen]
  rw [hId] at h
  exact h

universe u

theorem stochastic_bipartite_sublog_count_uniform
    (rho : Real) (hRho0 : 0 <= rho) (hRho1 : rho < 1) :
    exists N0 : Nat, 256 <= N0 /\
      forall (J : Type u) [Fintype J] [DecidableEq J] [Nonempty J],
        N0 <= Fintype.card J ->
        forall (T : Matrix J J Real) (q a : Real),
          (Fintype.card J : Real) * q = 1 -> 1 <= a ->
          a <= hamiltonianSublogCountDensity rho * Real.log (Fintype.card J : Real) ->
          (forall i, Finset.univ.sum (fun j => T i j) = 1) ->
          (forall j, Finset.univ.sum (fun i => T i j) = 1) ->
          (forall i j, 0 <= T i j) -> (forall i j, T i j <= a * q) ->
          norm (centeredKernel T q) <= rho ->
          abs (hamiltonianBipartiteCountRatio T - 1) <=
            (Fintype.card J : Real) ^ (-1 / 2 : Real) := by
  let b := hamiltonianSublogCountDensity rho
  have hb : 0 < b := hamiltonian_sublog_density_positive rho
  choose N0 hN0 hCount using stochastic_weighted_cycle_power_decay_uniform.{u}
    (1 - rho) b 1 (1 / 2) (by linarith only [hRho1]) (by linarith only [hRho0])
    hb.le (by norm_num) (by norm_num) (by norm_num)
  refine Exists.intro N0 (And.intro hN0 ?_)
  intro J instF instD instN hn T q a hq ha hA hRow hCol hNonneg hUpper hNorm
  have hn256 : (256 : Real) <= (Fintype.card J : Real) := by exact_mod_cast hN0.trans hn
  have hn0 : 0 < (Fintype.card J : Real) := by linarith only [hn256]
  have hn1 : (1 : Real) <= (Fintype.card J : Real) := by linarith only [hn256]
  have hLog : Real.log (Fintype.card J : Real) <=
      Real.log (2 * (Fintype.card J : Real)) :=
    Real.log_le_log hn0 (by linarith only [hn0])
  have hCap : a <= b * Real.log (2 * (Fintype.card J : Real)) :=
    hA.trans (mul_le_mul_of_nonneg_left hLog hb.le)
  have hMinus : a - 1 <= b * Real.log (Fintype.card J : Real) := by linarith only [hA]
  have hAmp := stochastic_gram_amplification_power_bound T q a rho
    (Fintype.card J : Real) b hq hRow hNonneg hUpper hRho0 hRho1 hNorm hn0 hMinus
  have hAmpOne : hamiltonianGramAmplification T q <= (Fintype.card J : Real) ^ (1 : Real) :=
    hAmp.trans (Real.rpow_le_rpow_of_exponent_le hn1
      (hamiltonian_sublog_density_amplification_exponent rho))
  have hNormDelta : norm (centeredKernel T q) <= 1 - (1 - rho) := by
    have hId : 1 - (1 - rho) = rho := by ring
    rwa [hId]
  simpa only [neg_div] using
    hCount J hn T q a hq ha hCap hRow hCol hNonneg hUpper hNormDelta hAmpOne

theorem stochastic_unoriented_bipartite_sublog_uniform
    (rho : Real) (hRho0 : 0 <= rho) (hRho1 : rho < 1) :
    exists N0 : Nat, 256 <= N0 /\
      forall (J : Type u) [Fintype J] [DecidableEq J] [Nonempty J],
        N0 <= Fintype.card J ->
        forall (T : Matrix J J Real) (q a : Real),
          (Fintype.card J : Real) * q = 1 -> 1 <= a ->
          a <= hamiltonianSublogCountDensity rho * Real.log (Fintype.card J : Real) ->
          (forall i, Finset.univ.sum (fun j => T i j) = 1) ->
          (forall j, Finset.univ.sum (fun i => T i j) = 1) ->
          (forall i j, 0 <= T i j) -> (forall i j, T i j <= a * q) ->
          norm (centeredKernel T q) <= rho ->
          abs ((2 * (Fintype.card J : Real) *
            (Fintype.card J : Real) ^ (2 * Fintype.card J) /
            ((Fintype.card J).factorial : Real) ^ 2) *
              (hamiltonianCycleSum (bipartiteLift T) / 2) - 1) <=
            (Fintype.card J : Real) ^ (-1 / 2 : Real) := by
  choose N0 hN0 hCount using stochastic_bipartite_sublog_count_uniform.{u} rho hRho0 hRho1
  refine Exists.intro N0 (And.intro hN0 ?_)
  intro J instF instD instN hn T q a hq ha hA hRow hCol hNonneg hUpper hNorm
  have h := hCount J hn T q a hq ha hA hRow hCol hNonneg hUpper hNorm
  rwa [hamiltonian_unoriented_cycle_ratio_identity] at h

end PrimeFactorOscillations

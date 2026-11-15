/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianCountPowerDecay

/-! # The sharp density consumer of the actual weighted count

Every positive amplification slack yields power decay. The exact
condition b*kappa_rho<2 is consumed with all original hypotheses.
-/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations

universe u

theorem stochastic_amplification_slack_count_uniform
    (delta c eps : Real) (hDelta : 0 < delta) (hDelta1 : delta <= 1)
    (hc : 0 <= c) (hEps : 0 < eps) :
    exists t : Real, 0 < t /\
      exists N0 : Nat, 256 <= N0 /\
        forall (J : Type u) [Fintype J] [DecidableEq J] [Nonempty J],
          N0 <= Fintype.card J ->
          forall (T : Matrix J J Real) (q a : Real),
            (Fintype.card J : Real) * q = 1 -> 1 <= a ->
            a <= c * Real.log (2 * (Fintype.card J : Real)) ->
            (forall i, Finset.univ.sum (fun j => T i j) = 1) ->
            (forall j, Finset.univ.sum (fun i => T i j) = 1) ->
            (forall i j, 0 <= T i j) -> (forall i j, T i j <= a * q) ->
            norm (centeredKernel T q) <= 1 - delta ->
            hamiltonianGramAmplification T q <= (Fintype.card J : Real) ^ (2 - eps) ->
            abs (hamiltonianBipartiteCountRatio T - 1) <=
              (Fintype.card J : Real) ^ (-t) := by
  let t := min 1 eps / 2
  have hMin : 0 < min 1 eps := lt_min (by norm_num) hEps
  have ht : 0 < t := div_pos hMin (by norm_num)
  have ht1 : t < 1 := by
    have h := min_le_left (1 : Real) eps
    dsimp only [t]
    linarith only [h]
  have htEps : t < eps := by
    have h := min_le_right (1 : Real) eps
    dsimp only [t]
    linarith only [h, hMin]
  refine Exists.intro t (And.intro ht ?_)
  exact stochastic_weighted_cycle_power_decay_uniform.{u} delta c (2 - eps) t
    hDelta hDelta1 hc ht ht1 (by linarith only [htEps])

theorem stochastic_sharp_density_count_uniform
    (rho b : Real) (hRho0 : 0 <= rho) (hRho1 : rho < 1)
    (hb : 0 <= b) (hDensity : hamiltonianSpectralKappa rho * b < 2) :
    exists t : Real, 0 < t /\
      exists N0 : Nat, 256 <= N0 /\
        forall (J : Type u) [Fintype J] [DecidableEq J] [Nonempty J],
          N0 <= Fintype.card J ->
          forall (T : Matrix J J Real) (q a : Real),
            (Fintype.card J : Real) * q = 1 -> 1 <= a ->
            a <= b * Real.log (Fintype.card J : Real) ->
            (forall i, Finset.univ.sum (fun j => T i j) = 1) ->
            (forall j, Finset.univ.sum (fun i => T i j) = 1) ->
            (forall i j, 0 <= T i j) -> (forall i j, T i j <= a * q) ->
            norm (centeredKernel T q) <= rho ->
            abs (hamiltonianBipartiteCountRatio T - 1) <=
              (Fintype.card J : Real) ^ (-t) := by
  have hDelta : 0 < 1 - rho := sub_pos.mpr hRho1
  have hDelta1 : 1 - rho <= 1 := by linarith only [hRho0]
  have hEps : 0 < 2 - hamiltonianSpectralKappa rho * b := sub_pos.mpr hDensity
  have hRange := stochastic_amplification_slack_count_uniform.{u}
    (1 - rho) b (2 - hamiltonianSpectralKappa rho * b) hDelta hDelta1 hb hEps
  refine hRange.elim ?_
  intro t ht
  refine Exists.intro t (And.intro ht.1 ?_)
  refine ht.2.elim ?_
  intro N0 hN0
  refine Exists.intro N0 (And.intro hN0.1 ?_)
  intro J instF instD instN hn T q a hq ha hCap hRow hCol hNonneg hUpper hNorm
  have hN256 : (256 : Real) <= Fintype.card J := by exact_mod_cast le_trans hN0.1 hn
  have hN : 0 < (Fintype.card J : Real) := by linarith only [hN256]
  have hLog2 : 0 <= Real.log 2 := Real.log_nonneg (by norm_num)
  have hSplit : Real.log (2 * (Fintype.card J : Real)) =
      Real.log 2 + Real.log (Fintype.card J : Real) :=
    Real.log_mul (by norm_num) (ne_of_gt hN)
  have hLog : Real.log (Fintype.card J : Real) <=
      Real.log (2 * (Fintype.card J : Real)) := by linarith only [hLog2, hSplit]
  have hCapLog : a <= b * Real.log (2 * (Fintype.card J : Real)) :=
    le_trans hCap (mul_le_mul_of_nonneg_left hLog hb)
  have hMinus : a - 1 <= b * Real.log (Fintype.card J : Real) := by linarith only [hCap]
  have hAmp := stochastic_gram_amplification_power_bound T q a rho
    (Fintype.card J : Real) b hq hRow hNonneg hUpper hRho0 hRho1 hNorm hN hMinus
  have hExponent : 2 - (2 - hamiltonianSpectralKappa rho * b) =
      hamiltonianSpectralKappa rho * b := by ring
  have hAmpCap : hamiltonianGramAmplification T q <=
      (Fintype.card J : Real) ^ (2 - (2 - hamiltonianSpectralKappa rho * b)) := by
    rw [hExponent]
    exact hAmp
  have hGap : 1 - (1 - rho) = rho := by ring
  have hNormDelta : norm (centeredKernel T q) <= 1 - (1 - rho) := by rw [hGap]; exact hNorm
  exact hN0.2 J hn T q a hq ha hCapLog hRow hCol hNonneg hUpper hNormDelta hAmpCap

end PrimeFactorOscillations

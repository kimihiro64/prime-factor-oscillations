/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianPermanentCoreAverage
import PrimeFactorOscillations.Helpers.HamiltonianRookGammaRegions

/-! # Complete quantitative original-permanent Gamma expansion

The original signed rook core, annulus and far tail are assembled before
transport through the exact normalized permanent identity. Every remainder
has an explicit bound; the signed first correction remains in the main term.
The eventual polylogarithmic range and rate simplification are subsequent.
-/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations

def hamiltonianRookGammaTailBudget (n : Nat) (a delta eps : Real) : Real :=
  2 * Real.exp (6 * a * Real.sqrt (n : Real) / delta -
      ((n : Real) + 1) * eps ^ 2 / 36) +
    3 * Real.exp (-(n : Real) * delta ^ 2 / 36864 +
      40 / (3 * delta) * Real.sqrt ((n : Real) * (a - 1)))

def stochasticPermanentGammaErrorBound {n : Nat}
    (T : Matrix (Fin n) (Fin n) Real) (q a delta eps : Real) : Real :=
  stochasticPermanentCoreRemainderBound T q a delta eps +
    hamiltonianRookGammaTailBudget n a delta eps

theorem stochastic_permanent_gamma_first_correction {n : Nat}
    (T : Matrix (Fin n) (Fin n) Real) (q a delta eps : Real)
    (hn : 16 <= n) (hq : (n : Real) * q = 1) (ha : 1 <= a)
    (hRow : forall i, Finset.sum Finset.univ (fun j => T i j) = 1)
    (hCol : forall j, Finset.sum Finset.univ (fun i => T i j) = 1)
    (hNonneg : forall i j, 0 <= T i j) (hUpper : forall i j, T i j <= a * q)
    (hDelta0 : 0 < delta) (hDelta1 : delta <= 1)
    (hNorm : norm (centeredKernel T q) <= 1 - delta)
    (hEps0 : 0 < eps) (hEps1 : eps <= delta / 64)
    (hLarge : 4 <= (n : Real) * eps) (hOuter : 32 <= (n : Real) * delta)
    (hSmall : 2 * (a - 1) * eps <= delta)
    (hSize : hamiltonianPermanentCutoffThreshold delta a <= Real.sqrt (n : Real)) :
    abs (gammaInverseAverage n (hamiltonianRookPolynomial (centeredKernel T q)) -
      realGramDeterminantFactor (centeredKernel T q) 1 *
        (1 + stochasticPermanentFirstCorrection T q)) <=
      stochasticPermanentGammaErrorBound T q a delta eps := by
  let x := gammaInverseAverage n (hamiltonianRookPolynomial (centeredKernel T q))
  let y := gammaInverseAverage n
    (Set.indicator {s : Real | abs (s - 1) <= eps}
      (hamiltonianRookPolynomial (centeredKernel T q)))
  let m := realGramDeterminantFactor (centeredKernel T q) 1 *
    (1 + stochasticPermanentFirstCorrection T q)
  have hCore := stochastic_permanent_core_gamma_first_correction T q a delta eps
    hn hq ha hRow hCol hNonneg hUpper hDelta0 hDelta1 hNorm
    hEps0 hEps1 hLarge hSmall hSize
  have hTail := stochastic_rook_gamma_full_to_core T q a delta eps
    hq ha hRow hCol hNonneg hUpper hDelta0 hDelta1 hNorm
    hEps0 (by linarith only [hEps1, hDelta0]) hLarge hOuter
  change abs (x - m) <= _
  have hIdentity : x - m = (x - y) + (y - m) := by ring
  rw [hIdentity]
  have hTriangle := abs_add_le (x - y) (y - m)
  change abs (y - m) <= stochasticPermanentCoreRemainderBound T q a delta eps at hCore
  change abs (x - y) <= hamiltonianRookGammaTailBudget n a delta eps at hTail
  change _ <= stochasticPermanentCoreRemainderBound T q a delta eps +
    hamiltonianRookGammaTailBudget n a delta eps
  linarith only [hTriangle, hCore, hTail]

theorem stochastic_permanent_first_correction_explicit {n : Nat}
    (T : Matrix (Fin n) (Fin n) Real) (q a delta eps : Real)
    (hn : 16 <= n) (hq : (n : Real) * q = 1) (ha : 1 <= a)
    (hRow : forall i, Finset.sum Finset.univ (fun j => T i j) = 1)
    (hCol : forall j, Finset.sum Finset.univ (fun i => T i j) = 1)
    (hNonneg : forall i j, 0 <= T i j) (hUpper : forall i j, T i j <= a * q)
    (hDelta0 : 0 < delta) (hDelta1 : delta <= 1)
    (hNorm : norm (centeredKernel T q) <= 1 - delta)
    (hEps0 : 0 < eps) (hEps1 : eps <= delta / 64)
    (hLarge : 4 <= (n : Real) * eps) (hOuter : 32 <= (n : Real) * delta)
    (hSmall : 2 * (a - 1) * eps <= delta)
    (hSize : hamiltonianPermanentCutoffThreshold delta a <= Real.sqrt (n : Real)) :
    abs (((n : Real) ^ n / (n.factorial : Real)) * weightedPermutationSum T -
      realGramDeterminantFactor (centeredKernel T q) 1 *
        (1 + stochasticPermanentFirstCorrection T q)) <=
      stochasticPermanentGammaErrorBound T q a delta eps := by
  have hNPos : 0 < n := by omega
  have hNReal : 0 < (n : Real) := Nat.cast_pos.mpr hNPos
  have hqValue : q = 1 / (n : Real) := by
    calc
      _ = ((n : Real) * q) / (n : Real) := by
        field_simp [ne_of_gt hNReal]
      _ = _ := by rw [hq]
  have hKernel : (fun i j => 1 / (n : Real) + centeredKernel T q i j) = T := by
    funext i j
    change 1 / (n : Real) + (T i j - q) = T i j
    rw [hqValue]
    ring
  have hExact := hamiltonianRookPolynomial_gamma_normalized (centeredKernel T q)
    (by simpa only [Fintype.card_fin] using hNPos)
  simp only [Fintype.card_fin] at hExact
  rw [hKernel] at hExact
  rw [<- hExact]
  exact stochastic_permanent_gamma_first_correction T q a delta eps hn hq ha
    hRow hCol hNonneg hUpper hDelta0 hDelta1 hNorm hEps0 hEps1 hLarge hOuter hSmall hSize

end PrimeFactorOscillations

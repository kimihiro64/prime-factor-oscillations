/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianPermanentFirstCorrection
import PrimeFactorOscillations.Helpers.HamiltonianPermanentRealWindow
import PrimeFactorOscillations.Helpers.HamiltonianStochasticCorrectionBudget

/-! # The original rook Gamma core with its signed covariance correction

The actual rook integral is compared jointly with the actual determinant
and determinant-covariance integrals. All window integrability hypotheses
are discharged from the stochastic kernel and local bounds.
-/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations

theorem stochastic_rook_gamma_core_remainder {n : Nat}
    (T : Matrix (Fin n) (Fin n) Real) (q a delta eps : Real)
    (hn : 16 <= n) (hq : (n : Real) * q = 1) (ha : 1 <= a)
    (hRow : forall i, Finset.sum Finset.univ (fun j => T i j) = 1)
    (hCol : forall j, Finset.sum Finset.univ (fun i => T i j) = 1)
    (hNonneg : forall i j, 0 <= T i j) (hUpper : forall i j, T i j <= a * q)
    (hDelta0 : 0 < delta) (hDelta1 : delta <= 1)
    (hNorm : norm (centeredKernel T q) <= 1 - delta)
    (hEps0 : 0 <= eps) (hEps1 : eps <= delta / 64)
    (hSmall : 2 * (a - 1) * eps <= delta)
    (hSize : hamiltonianPermanentCutoffThreshold delta a <= Real.sqrt (n : Real)) :
    abs (gammaInverseAverage n
        (Set.indicator {s : Real | abs (s - 1) <= eps}
          (hamiltonianRookPolynomial (centeredKernel T q))) -
      (gammaInverseAverage n
        (Set.indicator {s : Real | abs (s - 1) <= eps}
          (realGramDeterminantFactor (centeredKernel T q))) +
        gammaInverseAverage n
          (Set.indicator {s : Real | abs (s - 1) <= eps}
            (fun s => realGramDeterminantFactor (centeredKernel T q) s *
              covarianceCorrection
                (resolventCovariance (HSMul.hSMul s (bipartiteLift (centeredKernel T q)))))))) <=
      Real.exp 1 * realGramDeterminantFactor (centeredKernel T q) 1 *
        (hamiltonianPermanentLocalCorrectionConstant delta * (1 + a) ^ 24 /
          (n : Real) ^ 2) := by
  classical
  let B := centeredKernel T q
  let lam := realGramEigenvalues B
  let W : Set Real := {s | abs (s - 1) <= eps}
  let R := hamiltonianRookPolynomial B
  let D := realGramDeterminantFactor B
  let P : Real -> Real := fun s =>
    covarianceCorrection (resolventCovariance (HSMul.hSMul s (bipartiteLift B)))
  let C := (1 + 16 * Real.exp 1 * hamiltonianPermanentWindowKappa delta a) ^ 3
  let E := Real.exp 1 * D 1 *
    (hamiltonianPermanentLocalCorrectionConstant delta * (1 + a) ^ 24 / (n : Real) ^ 2)
  have hn3 : 3 <= n := by omega
  have hN0 : 0 < (n : Real) := Nat.cast_pos.mpr (by omega)
  have hEps32 : eps <= delta / 32 := by linarith only [hEps1, hDelta0]
  have hEps4 : eps <= delta / 4 := by linarith only [hEps1, hDelta0]
  have hMap : Measurable (fun s : Real => abs (s - 1)) := by
    simpa only [Real.norm_eq_abs] using (measurable_sub_const (1 : Real)).norm
  have hW : MeasurableSet W := measurableSet_le hMap measurable_const
  have hData := stochasticGram_spectral_data T q a delta
    (by simpa only [Fintype.card_fin] using hq) hRow hNonneg hUpper hDelta1 hNorm
  have hOne : Membership.mem W (1 : Real) := by
    change abs ((1 : Real) - 1) <= eps
    simpa only [sub_self, abs_zero] using hEps0
  have hDet : forall s, Membership.mem W s ->
      D s = spectralFactors Finset.univ lam s := by
    intro s hs
    exact realGramDeterminantFactor_eq_spectral_on_strip B delta eps s
      hDelta0 hDelta1 hEps0 hEps4 hNorm hs
  have hDOne : 0 < D 1 := by rw [hDet 1 hOne]; exact Real.exp_pos _
  have hD0 : forall s, Membership.mem W s -> 0 < D s := by
    intro s hs
    rw [hDet s hs]
    exact Real.exp_pos _
  have hSmall' : 2 * (Finset.sum Finset.univ lam) * eps <= delta := by
    have h := mul_le_mul_of_nonneg_right hData.2.2 hEps0
    change Finset.sum Finset.univ lam * eps <= (a - 1) * eps at h
    linarith only [h, hSmall]
  have hRatio : forall s, Membership.mem W s -> D s <= Real.exp 1 * D 1 := by
    intro s hs
    rw [hDet s hs, hDet 1 hOne]
    exact spectralFactors_central_ratio Finset.univ lam delta eps s
      hDelta0 hDelta1 hEps0 hEps4
      (fun i hi => hData.1 i) (fun i hi => hData.2.1 i) hSmall' hs
  have hGap : 0 < 1 - hamiltonianWindowScale delta * (1 - delta / 2) := by
    have h := hamiltonian_window_coefficient_gap delta hDelta0
    linarith
  have hKappa0 : 0 <= hamiltonianPermanentWindowKappa delta a := by
    unfold hamiltonianPermanentWindowKappa
    positivity
  have hC0 : 0 <= C := by dsimp only [C]; positivity
  have hPBound : forall s, Membership.mem W s -> abs (P s) <= 20 * C / (n : Real) := by
    intro s hs
    exact stochastic_covarianceCorrection_window_bound T q a delta s
      hn3 hq ha hRow hCol hNonneg hUpper hDelta0 hDelta1 hNorm
      (le_trans hs hEps32)
  have hMeasD : Measurable (Set.indicator W D) := by
    change Measurable (Set.indicator {s : Real | abs (s - 1) <= eps}
      (realGramDeterminantFactor B))
    rw [realGramDeterminantFactor_window_eq B delta eps
      hDelta0 hDelta1 hEps0 hEps4 hNorm]
    exact (spectralFactors_measurable Finset.univ lam).indicator hW
  have hMeasDP : Measurable (Set.indicator W (fun s => D s * P s)) :=
    stochastic_covarianceCorrection_product_window_measurable T q a delta eps
      hn3 hq ha hRow hCol hNonneg hUpper hDelta0 hDelta1 hNorm hEps0 hEps32
  have hDInt : GammaInverseIntegrable n (Set.indicator W D) := by
    apply gammaInverseIntegrable_of_abs_le n _ (fun _ => Real.exp 1 * D 1) hMeasD
      (gammaInverseIntegrable_const n _)
    intro s hs0
    by_cases hs : Membership.mem W s
    case pos =>
      rw [Set.indicator_of_mem hs, abs_of_pos (hD0 s hs)]
      exact hRatio s hs
    case neg =>
      rw [Set.indicator_of_notMem hs, abs_zero]
      exact mul_nonneg (Real.exp_pos 1).le hDOne.le
  have hDPInt : GammaInverseIntegrable n (Set.indicator W (fun s => D s * P s)) := by
    apply gammaInverseIntegrable_of_abs_le n _
      (fun _ => (Real.exp 1 * D 1) * (20 * C / (n : Real))) hMeasDP
      (gammaInverseIntegrable_const n _)
    intro s hs0
    by_cases hs : Membership.mem W s
    case pos =>
      rw [Set.indicator_of_mem hs, abs_mul, abs_of_pos (hD0 s hs)]
      exact mul_le_mul (hRatio s hs) (hPBound s hs) (abs_nonneg _)
        (mul_nonneg (Real.exp_pos 1).le hDOne.le)
    case neg =>
      rw [Set.indicator_of_notMem hs, abs_zero]
      positivity
  have hRInt : GammaInverseIntegrable n R := by
    dsimp only [GammaInverseIntegrable, R]
    simpa only [Fintype.card_fin] using hamiltonianRookPolynomial_integrable B
  have hRCInt := gammaInverseIntegrable_indicator n R hRInt W hW
  have hMinusInt : GammaInverseIntegrable n
      (fun s => Set.indicator W R s - Set.indicator W D s) := by
    unfold GammaInverseIntegrable at hRCInt hDInt
    unfold GammaInverseIntegrable
    have h := hRCInt.sub hDInt
    change MeasureTheory.Integrable (fun t : Real =>
      Real.exp (-t) * t ^ n * Set.indicator W R ((n : Real) / t) -
        Real.exp (-t) * t ^ n * Set.indicator W D ((n : Real) / t)) gammaHalfLine at h
    simpa only [mul_sub] using h
  have hE0 : 0 <= E := by
    have h := stochastic_real_rook_local_covariance_remainder T q a delta eps 1
      (by omega) hq ha hRow hCol hNonneg hUpper hDelta0 hDelta1 hNorm
      hEps0 hEps1 hSmall hSize hOne
    exact le_trans (abs_nonneg _) h
  have hRemainder := gammaInverseAverage_abs_le n
    (Set.indicator W (fun s => R s - D s * (1 + P s))) (fun _ => E)
    (gammaInverseIntegrable_const n E) (by
      intro s hs0
      by_cases hs : Membership.mem W s
      case pos =>
        rw [Set.indicator_of_mem hs]
        exact stochastic_real_rook_local_covariance_remainder T q a delta eps s
          (by omega) hq ha hRow hCol hNonneg hUpper hDelta0 hDelta1 hNorm
          hEps0 hEps1 hSmall hSize hs
      case neg =>
        rw [Set.indicator_of_notMem hs, abs_zero]
        exact hE0)
  have hDiffFun : Set.indicator W (fun s => R s - D s * (1 + P s)) =
      (fun s => (Set.indicator W R s - Set.indicator W D s) -
        Set.indicator W (fun v => D v * P v) s) := by
    funext s
    by_cases hs : Membership.mem W s
    case pos => simp only [Set.indicator_of_mem hs]; ring
    case neg => simp only [Set.indicator_of_notMem hs]; ring
  rw [hDiffFun, gammaInverseAverage_sub n _ _ hMinusInt hDPInt,
    gammaInverseAverage_sub n _ _ hRCInt hDInt, gammaInverseAverage_const] at hRemainder
  change abs (gammaInverseAverage n (Set.indicator W R) -
    (gammaInverseAverage n (Set.indicator W D) +
      gammaInverseAverage n (Set.indicator W (fun s => D s * P s)))) <= E
  convert hRemainder using 1 <;> congr 1 <;> ring


def stochasticPermanentCoreRemainderBound {n : Nat}
    (T : Matrix (Fin n) (Fin n) Real) (q a delta eps : Real) : Real :=
  let B := centeredKernel T q
  let lam := realGramEigenvalues B
  let D1 := realGramDeterminantFactor B 1
  let P1 := covarianceCorrection
    (resolventCovariance (HSMul.hSMul (1 : Real) (bipartiteLift B)))
  let tail := Real.exp (-((n : Real) + 1) * eps ^ 2 / 72)
  Real.exp 1 * D1 *
      (hamiltonianPermanentLocalCorrectionConstant delta * (1 + a) ^ 24 / (n : Real) ^ 2) +
    (spectralTaylorRemainderBound Finset.univ lam delta *
      (3 * ((n : Real) + 6) /
        (((n : Real) - 1) * ((n : Real) - 2) * ((n : Real) - 3))) +
      tail * spectralTaylorTailCoefficient Finset.univ lam) +
    (hamiltonianCorrectionGammaBudget delta * D1 * (1 + a) ^ 7 / (n : Real) ^ 2 +
      tail * (4 * abs (D1 * P1) + 7 * abs (stochasticCorrectionGammaLinear T q))) +
    abs (4 * (spectralFactorJet3 Finset.univ lam 1 / 6) /
      (((n : Real) - 1) * ((n : Real) - 2)))

theorem stochastic_permanent_core_gamma_first_correction {n : Nat}
    (T : Matrix (Fin n) (Fin n) Real) (q a delta eps : Real)
    (hn : 16 <= n) (hq : (n : Real) * q = 1) (ha : 1 <= a)
    (hRow : forall i, Finset.sum Finset.univ (fun j => T i j) = 1)
    (hCol : forall j, Finset.sum Finset.univ (fun i => T i j) = 1)
    (hNonneg : forall i j, 0 <= T i j) (hUpper : forall i j, T i j <= a * q)
    (hDelta0 : 0 < delta) (hDelta1 : delta <= 1)
    (hNorm : norm (centeredKernel T q) <= 1 - delta)
    (hEps0 : 0 < eps) (hEps1 : eps <= delta / 64)
    (hLarge : 4 <= (n : Real) * eps)
    (hSmall : 2 * (a - 1) * eps <= delta)
    (hSize : hamiltonianPermanentCutoffThreshold delta a <= Real.sqrt (n : Real)) :
    abs (gammaInverseAverage n
      (Set.indicator {s : Real | abs (s - 1) <= eps}
        (hamiltonianRookPolynomial (centeredKernel T q))) -
      realGramDeterminantFactor (centeredKernel T q) 1 *
        (1 + stochasticPermanentFirstCorrection T q)) <=
      stochasticPermanentCoreRemainderBound T q a delta eps := by
  classical
  let B := centeredKernel T q
  let lam := realGramEigenvalues B
  let D1 := realGramDeterminantFactor B 1
  let P1 := covarianceCorrection
    (resolventCovariance (HSMul.hSMul (1 : Real) (bipartiteLift B)))
  let W : Set Real := {s | abs (s - 1) <= eps}
  let x := gammaInverseAverage n (Set.indicator W (hamiltonianRookPolynomial B))
  let y := gammaInverseAverage n (Set.indicator W (realGramDeterminantFactor B))
  let z := gammaInverseAverage n (Set.indicator W (fun s =>
    realGramDeterminantFactor B s *
      covarianceCorrection (resolventCovariance (HSMul.hSMul s (bipartiteLift B)))))
  let A := D1 + (spectralFactorJet2 Finset.univ lam 1 / 2) / ((n : Real) - 1)
  let c := 4 * (spectralFactorJet3 Finset.univ lam 1 / 6) /
    (((n : Real) - 1) * ((n : Real) - 2))
  let E0 := Real.exp 1 * D1 *
    (hamiltonianPermanentLocalCorrectionConstant delta * (1 + a) ^ 24 / (n : Real) ^ 2)
  let tail := Real.exp (-((n : Real) + 1) * eps ^ 2 / 72)
  let ED := spectralTaylorRemainderBound Finset.univ lam delta *
    (3 * ((n : Real) + 6) /
      (((n : Real) - 1) * ((n : Real) - 2) * ((n : Real) - 3))) +
    tail * spectralTaylorTailCoefficient Finset.univ lam
  let EP := hamiltonianCorrectionGammaBudget delta * D1 * (1 + a) ^ 7 / (n : Real) ^ 2 +
    tail * (4 * abs (D1 * P1) + 7 * abs (stochasticCorrectionGammaLinear T q))
  have hEps4 : eps <= delta / 4 := by linarith only [hEps1, hDelta0]
  have hEpsHalf : eps <= 1 / 2 := by linarith only [hEps1, hDelta1]
  have hEpsOne : eps <= 1 := by linarith only [hEpsHalf]
  have hAtOne : realGramDeterminantFactor B 1 = spectralFactors Finset.univ lam 1 :=
    realGramDeterminantFactor_eq_spectral_on_strip B delta 0 1 hDelta0 hDelta1
      (by norm_num) (by linarith only [hDelta0]) hNorm (by norm_num)
  have hD1 : 0 < D1 := by dsimp only [D1]; rw [hAtOne]; exact Real.exp_pos _
  have hRook := stochastic_rook_gamma_core_remainder T q a delta eps hn hq ha
    hRow hCol hNonneg hUpper hDelta0 hDelta1 hNorm hEps0.le hEps1 hSmall hSize
  change abs (x - (y + z)) <= E0 at hRook
  have hDet := stochasticGramDeterminantFactor_gamma_window T q a
    (by simpa only [Fintype.card_fin] using hq) hRow hNonneg hUpper n hn delta eps
    hDelta0 hDelta1 hEps0 hEpsHalf hEps4 hLarge hNorm hSmall
  rw [<- hAtOne] at hDet
  change abs (y - (A + c)) <= ED at hDet
  have hCov := stochastic_covarianceCorrection_gamma_window T q a delta eps hn hq ha
    hRow hCol hNonneg hUpper hDelta0 hDelta1 hNorm hEps0 hEps1 hLarge hSmall
  have hMoment := stochasticCorrectionGamma_second_moment_bound T q a delta eps
    (by omega) hq ha hRow hNonneg hUpper hDelta0 hDelta1 hNorm hEps0.le hEpsOne
  have hCovBound : abs (z - D1 * P1) <= EP := by
    exact le_trans hCov (add_le_add hMoment (le_refl _))
  have hP1 : P1 = covarianceCorrection (resolventCovariance (bipartiteLift B)) := by
    dsimp only [P1]
    rw [one_smul]
  have hMain : D1 * (1 + stochasticPermanentFirstCorrection T q) = A + D1 * P1 := by
    unfold stochasticPermanentFirstCorrection
    simp only [Fintype.card_fin]
    rw [realGramDeterminantFactor_second_derivative B delta hDelta0 hDelta1 hNorm]
    change D1 * (1 + (spectralFactorJet2 Finset.univ lam 1 /
      (2 * ((n : Real) - 1) * D1) +
        covarianceCorrection (resolventCovariance (bipartiteLift B)))) = A + D1 * P1
    rw [hP1]
    dsimp only [A]
    have hN : (16 : Real) <= (n : Real) := by exact_mod_cast hn
    have hNm1 : Not ((n : Real) - 1 = 0) := by linarith only [hN]
    field_simp [ne_of_gt hD1, hNm1] <;> ring
  change abs (x - D1 * (1 + stochasticPermanentFirstCorrection T q)) <= _
  rw [hMain]
  have hId : x - (A + D1 * P1) =
      ((x - (y + z)) + (y - (A + c))) + (z - D1 * P1) + c := by ring
  rw [hId]
  have hT1 := abs_add_le (x - (y + z)) (y - (A + c))
  have hT2 := abs_add_le ((x - (y + z)) + (y - (A + c))) (z - D1 * P1)
  have hT3 := abs_add_le (((x - (y + z)) + (y - (A + c))) + (z - D1 * P1)) c
  change _ <= E0 + ED + EP + abs c
  linarith only [hT1, hT2, hT3, hRook, hDet, hCovBound]

end PrimeFactorOscillations

/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianGammaTaylor

/-! # Signed affine Gamma averaging

The full affine term has mean equal to its constant coefficient. The local
quadratic remainder and both affine truncation tails are retained explicitly.
This is used to average the actual covariance correction with its determinant
factor, whose first variation must cancel only after averaging.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

theorem gammaInverseAverage_local_affine (n : Nat) (hn : 16 <= n)
    (eps : Real) (hEps0 : 0 < eps) (hEps1 : eps <= 1 / 2)
    (hLarge : 4 <= (n : Real) * eps) (f : Real -> Real)
    (a b M : Real) (hM : 0 <= M)
    (hf : GammaInverseIntegrable n
      (Set.indicator {s : Real | abs (s - 1) <= eps} f))
    (hApprox : forall s : Real, abs (s - 1) <= eps ->
      abs (f s - gammaCubic a b 0 0 s) <= M * (s - 1) ^ 2) :
    abs (gammaInverseAverage n
        (Set.indicator {s : Real | abs (s - 1) <= eps} f) -
      a) <=
      M * (1 / ((n : Real) - 1)) +
      Real.exp (-((n : Real) + 1) * eps ^ 2 / 72) *
        (4 * abs a + 7 * abs b) := by
  let C : Set Real := {s | abs (s - 1) <= eps}
  let E : Set Real := {s | eps < abs (s - 1)}
  let p : Real -> Real := gammaCubic a b 0 0
  have hMap : Measurable (fun s : Real => abs (s - 1)) := by
    simpa only [Real.norm_eq_abs] using (measurable_sub_const (1 : Real)).norm
  have hC : MeasurableSet C := measurableSet_le hMap measurable_const
  have hE : MeasurableSet E := measurableSet_lt measurable_const hMap
  have hp := gammaCubic_integrable n (by omega) a b 0 0
  have hpC := gammaInverseIntegrable_indicator n p hp C hC
  have hpE := gammaInverseIntegrable_indicator n p hp E hE
  have hSecond := gammaInverseIntegrable_centered n 2 (by omega)
  have hRemainder := gammaInverseAverage_abs_le n
    (Set.indicator C (fun s : Real => f s - p s))
    (fun s : Real => M * (s - 1) ^ 2)
    (gammaInverseIntegrable_smul n M _ hSecond)
    (by
      intro s hs
      by_cases hsC : Membership.mem C s
      case pos =>
        simp only [Set.indicator_of_mem hsC]
        exact hApprox s hsC
      case neg =>
        simp only [Set.indicator_of_notMem hsC, abs_zero]
        have hPow : 0 <= (s - 1) ^ 2 := by
          exact sq_nonneg (s - 1)
        exact mul_nonneg hM hPow)
  have hDiffFun : Set.indicator C (fun s : Real => f s - p s) =
      (fun s : Real => Set.indicator C f s - Set.indicator C p s) := by
    funext s
    by_cases hsC : Membership.mem C s
    case pos => simp only [Set.indicator_of_mem hsC]
    case neg => simp only [Set.indicator_of_notMem hsC, sub_self]
  rw [hDiffFun, gammaInverseAverage_sub n (Set.indicator C f)
    (Set.indicator C p) hf hpC, gammaInverseAverage_smul,
    gammaInverseAverage_second_uniform n (by omega)] at hRemainder
  have hSplitFun : p = (fun s : Real =>
      Set.indicator C p s + Set.indicator E p s) := by
    funext s
    by_cases hsE : eps < abs (s - 1)
    case pos =>
      have hsC : Not (abs (s - 1) <= eps) := not_le_of_gt hsE
      simp [C, E, Set.indicator, hsC, hsE]
    case neg =>
      have hsC : abs (s - 1) <= eps := le_of_not_gt hsE
      simp [C, E, Set.indicator, hsC, hsE]
  have hSplit := congrArg (gammaInverseAverage n) hSplitFun
  rw [gammaInverseAverage_add n (Set.indicator C p) (Set.indicator E p) hpC hpE]
    at hSplit
  have hMean := gammaInverseAverage_cubic n (by omega) a b 0 0
  have hTail := gammaInverseAverage_cubic_tail n (by omega)
    eps hEps0 hEps1 hLarge a b 0 0
  simp only [abs_zero, mul_zero, add_zero] at hTail
  have hAlgebra :
      gammaInverseAverage n (Set.indicator C f) -
        a =
      (gammaInverseAverage n (Set.indicator C f) -
        gammaInverseAverage n (Set.indicator C p)) -
        gammaInverseAverage n (Set.indicator E p) := by
    simp only [zero_div, mul_zero, add_zero] at hMean
    change gammaInverseAverage n p = _ at hMean
    linarith only [hSplit, hMean]
  change abs (gammaInverseAverage n (Set.indicator C f) -
    a) <= _
  rw [hAlgebra]
  have hTriangle := abs_add_le
    (gammaInverseAverage n (Set.indicator C f) -
      gammaInverseAverage n (Set.indicator C p))
    (-gammaInverseAverage n (Set.indicator E p))
  rw [abs_neg] at hTriangle
  change abs ((gammaInverseAverage n (Set.indicator C f) -
    gammaInverseAverage n (Set.indicator C p)) -
      gammaInverseAverage n (Set.indicator E p)) <= _ at hTriangle
  linarith only [hTriangle, hRemainder, hTail]


theorem gammaAffine_window_integrable (n : Nat) (hn : 2 <= n)
    (eps : Real) (f : Real -> Real)
    (hf : Measurable
      (Set.indicator {s : Real | abs (s - 1) <= eps} f))
    (a b M : Real) (hM : 0 <= M)
    (hApprox : forall s : Real, abs (s - 1) <= eps ->
      abs (f s - gammaCubic a b 0 0 s) <= M * (s - 1) ^ 2) :
    GammaInverseIntegrable n
      (Set.indicator {s : Real | abs (s - 1) <= eps} f) := by
  let C : Set Real := {s | abs (s - 1) <= eps}
  let p : Real -> Real := gammaCubic a b 0 0
  have hMap : Measurable (fun s : Real => abs (s - 1)) := by
    simpa only [Real.norm_eq_abs] using (measurable_sub_const (1 : Real)).norm
  have hC : MeasurableSet C := measurableSet_le hMap measurable_const
  have hpMeas := (gammaCubic_measurable a b 0 0).indicator hC
  have hMeas : Measurable (Set.indicator C (fun s : Real => f s - p s)) := by
    have hEq : Set.indicator C (fun s : Real => f s - p s) =
        (fun s : Real => Set.indicator C f s - Set.indicator C p s) := by
      funext s
      by_cases hs : Membership.mem C s
      case pos => simp only [Set.indicator_of_mem hs]
      case neg => simp only [Set.indicator_of_notMem hs, sub_self]
    rw [hEq]
    exact hf.sub hpMeas
  have hRem : GammaInverseIntegrable n
      (Set.indicator C (fun s : Real => f s - p s)) :=
    gammaInverseIntegrable_of_abs_le n _ _ hMeas
      (gammaInverseIntegrable_smul n M _ (gammaInverseIntegrable_centered n 2 hn))
      (by
        intro s hs
        by_cases hsC : Membership.mem C s
        case pos =>
          simp only [Set.indicator_of_mem hsC]
          exact hApprox s hsC
        case neg =>
          simp only [Set.indicator_of_notMem hsC, abs_zero]
          exact mul_nonneg hM (sq_nonneg _))
  have hp : GammaInverseIntegrable n p := by
    have h0 := gammaInverseIntegrable_const n a
    have h1 := gammaInverseIntegrable_smul n b (fun s : Real => (s - 1) ^ 1)
      (gammaInverseIntegrable_centered n 1 (by omega))
    have h := gammaInverseIntegrable_add n _ _ h0 h1
    change GammaInverseIntegrable n (fun s : Real => gammaCubic a b 0 0 s)
    simpa only [gammaCubic, pow_one, zero_mul, add_zero] using h
  have hpC := gammaInverseIntegrable_indicator n p hp C hC
  have hSum := gammaInverseIntegrable_add n _ _ hRem hpC
  have hFun : (fun s : Real =>
      Set.indicator C (fun z : Real => f z - p z) s +
        Set.indicator C p s) = Set.indicator C f := by
    funext s
    by_cases hsC : Membership.mem C s
    case pos => simp only [Set.indicator_of_mem hsC]; ring
    case neg => simp only [Set.indicator_of_notMem hsC, add_zero]
  rw [hFun] at hSum
  exact hSum

theorem gammaInverseAverage_local_affine_of_window_measurable
    (n : Nat) (hn : 16 <= n)
    (eps : Real) (hEps0 : 0 < eps) (hEps1 : eps <= 1 / 2)
    (hLarge : 4 <= (n : Real) * eps) (f : Real -> Real)
    (hf : Measurable
      (Set.indicator {s : Real | abs (s - 1) <= eps} f))
    (a b M : Real) (hM : 0 <= M)
    (hApprox : forall s : Real, abs (s - 1) <= eps ->
      abs (f s - gammaCubic a b 0 0 s) <= M * (s - 1) ^ 2) :
    abs (gammaInverseAverage n
        (Set.indicator {s : Real | abs (s - 1) <= eps} f) - a) <=
      M * (1 / ((n : Real) - 1)) +
      Real.exp (-((n : Real) + 1) * eps ^ 2 / 72) *
        (4 * abs a + 7 * abs b) :=
  gammaInverseAverage_local_affine n hn eps hEps0 hEps1 hLarge f a b M hM
    (gammaAffine_window_integrable n (by omega) eps f hf a b M hM hApprox)
    hApprox

end PrimeFactorOscillations

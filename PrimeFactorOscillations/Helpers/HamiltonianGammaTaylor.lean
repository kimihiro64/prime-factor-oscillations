/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import PrimeFactorOscillations.Helpers.HamiltonianGammaCentralMoments
import PrimeFactorOscillations.Helpers.HamiltonianGammaSignedTruncation

/-! # Signed central-window Taylor averaging

The actual inverse-Gamma average of a cubic retains the signed third
moment. Local fourth-order errors and the explicit truncation bounds are
kept separate. This is the analytic averaging consumer of the Gamma
moments, not a hypothesis asserting the permanent comparison itself.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

theorem gammaInverseAverage_second_uniform (n : Nat) (hn : 2 <= n) :
    gammaInverseAverage n (fun s : Real => (s - 1) ^ 2) =
      1 / ((n : Real) - 1) := by
  have h := gammaInverseAverage_centered_second (n - 2)
  have hNat : n - 2 + 2 = n := Nat.sub_add_cancel hn
  rw [hNat, Nat.cast_sub hn] at h
  norm_num only [Nat.cast_ofNat] at h
  have hDen : (n : Real) - 2 + 1 = (n : Real) - 1 := by ring
  rw [hDen] at h
  exact h

theorem gammaInverseAverage_third_uniform (n : Nat) (hn : 3 <= n) :
    gammaInverseAverage n (fun s : Real => (s - 1) ^ 3) =
      4 / (((n : Real) - 1) * ((n : Real) - 2)) := by
  have h := gammaInverseAverage_centered_third (n - 3)
  have hNat : n - 3 + 3 = n := Nat.sub_add_cancel hn
  rw [hNat, Nat.cast_sub hn] at h
  norm_num only [Nat.cast_ofNat] at h
  have hDen1 : (n : Real) - 3 + 2 = (n : Real) - 1 := by ring
  have hDen2 : (n : Real) - 3 + 1 = (n : Real) - 2 := by ring
  rw [hDen1, hDen2] at h
  exact h

theorem gammaInverseAverage_fourth_uniform (n : Nat) (hn : 4 <= n) :
    gammaInverseAverage n (fun s : Real => (s - 1) ^ 4) =
      3 * ((n : Real) + 6) /
        (((n : Real) - 1) * ((n : Real) - 2) * ((n : Real) - 3)) := by
  have h := gammaInverseAverage_centered_fourth (n - 4)
  have hNat : n - 4 + 4 = n := Nat.sub_add_cancel hn
  rw [hNat, Nat.cast_sub hn] at h
  norm_num only [Nat.cast_ofNat] at h
  have hNum : (n : Real) - 4 + 10 = (n : Real) + 6 := by ring
  have hDen1 : (n : Real) - 4 + 3 = (n : Real) - 1 := by ring
  have hDen2 : (n : Real) - 4 + 2 = (n : Real) - 2 := by ring
  have hDen3 : (n : Real) - 4 + 1 = (n : Real) - 3 := by ring
  rw [hNum, hDen1, hDen2, hDen3] at h
  exact h

def gammaCubic (a b c d s : Real) : Real :=
  a + b * (s - 1) + c * (s - 1) ^ 2 + d * (s - 1) ^ 3

private theorem gammaCubic_as_powers (a b c d : Real) :
    gammaCubic a b c d = (fun s : Real =>
      a + b * (s - 1) ^ 1 + c * (s - 1) ^ 2 + d * (s - 1) ^ 3) := by
  funext s
  unfold gammaCubic
  rw [pow_one]

theorem gammaCubic_integrable (n : Nat) (hn : 3 <= n) (a b c d : Real) :
    GammaInverseIntegrable n (gammaCubic a b c d) := by
  have h0 := gammaInverseIntegrable_const n a
  have h1 := gammaInverseIntegrable_smul n b (fun s : Real => (s - 1) ^ 1)
    (gammaInverseIntegrable_centered n 1 (by omega))
  have h2 := gammaInverseIntegrable_smul n c (fun s : Real => (s - 1) ^ 2)
    (gammaInverseIntegrable_centered n 2 (by omega))
  have h3 := gammaInverseIntegrable_smul n d (fun s : Real => (s - 1) ^ 3)
    (gammaInverseIntegrable_centered n 3 hn)
  rw [gammaCubic_as_powers]
  exact gammaInverseIntegrable_add n _ _
    (gammaInverseIntegrable_add n _ _
      (gammaInverseIntegrable_add n _ _ h0 h1) h2) h3

theorem gammaInverseAverage_cubic (n : Nat) (hn : 3 <= n) (a b c d : Real) :
    gammaInverseAverage n (gammaCubic a b c d) =
      a + c / ((n : Real) - 1) +
        4 * d / (((n : Real) - 1) * ((n : Real) - 2)) := by
  have h0 := gammaInverseIntegrable_const n a
  have h1 := gammaInverseIntegrable_smul n b (fun s : Real => (s - 1) ^ 1)
    (gammaInverseIntegrable_centered n 1 (by omega))
  have h2 := gammaInverseIntegrable_smul n c (fun s : Real => (s - 1) ^ 2)
    (gammaInverseIntegrable_centered n 2 (by omega))
  have h3 := gammaInverseIntegrable_smul n d (fun s : Real => (s - 1) ^ 3)
    (gammaInverseIntegrable_centered n 3 hn)
  rw [gammaCubic_as_powers]
  rw [gammaInverseAverage_add n
    (fun s : Real => (a + b * (s - 1) ^ 1) + c * (s - 1) ^ 2)
    (fun s : Real => d * (s - 1) ^ 3)
    (gammaInverseIntegrable_add n _ _ (gammaInverseIntegrable_add n _ _ h0 h1) h2) h3,
    gammaInverseAverage_add n (fun s : Real => a + b * (s - 1) ^ 1)
      (fun s : Real => c * (s - 1) ^ 2)
      (gammaInverseIntegrable_add n _ _ h0 h1) h2,
    gammaInverseAverage_add n (fun _ : Real => a)
      (fun s : Real => b * (s - 1) ^ 1) h0 h1,
    gammaInverseAverage_const, gammaInverseAverage_smul,
    gammaInverseAverage_smul, gammaInverseAverage_smul,
    gammaInverseAverage_second_uniform n (by omega),
    gammaInverseAverage_third_uniform n hn]
  simp only [pow_one, gammaInverseAverage_centered_first n (by omega)]
  ring

theorem gammaInverseAverage_cubic_tail (n : Nat) (hn : 12 <= n)
    (eps : Real) (hEps0 : 0 < eps) (hEps1 : eps <= 1 / 2)
    (hLarge : 4 <= (n : Real) * eps) (a b c d : Real) :
    abs (gammaInverseAverage n
      (Set.indicator {s : Real | eps < abs (s - 1)} (gammaCubic a b c d))) <=
      Real.exp (-((n : Real) + 1) * eps ^ 2 / 72) *
        (4 * abs a + 7 * abs b + 19 * abs c + 67 * abs d) := by
  let E : Set Real := {s | eps < abs (s - 1)}
  let g : Nat -> Real -> Real := fun j =>
    Set.indicator E (fun s : Real => abs (s - 1) ^ j)
  let G : Real -> Real := fun s =>
    abs a * g 0 s + abs b * g 1 s + abs c * g 2 s + abs d * g 3 s
  let e : Real := Real.exp (-((n : Real) + 1) * eps ^ 2 / 72)
  have hMap : Measurable (fun s : Real => abs (s - 1)) := by
    simpa only [Real.norm_eq_abs] using (measurable_sub_const (1 : Real)).norm
  have hE : MeasurableSet E := measurableSet_lt measurable_const hMap
  have hI : forall j : Nat, j <= 3 -> GammaInverseIntegrable n (g j) := by
    intro j hj
    exact gammaInverseIntegrable_indicator n _
      (gammaInverseIntegrable_abs_centered n j (by omega)) E hE
  have hA0 := gammaInverseIntegrable_smul n (abs a) (g 0) (hI 0 (by omega))
  have hA1 := gammaInverseIntegrable_smul n (abs b) (g 1) (hI 1 (by omega))
  have hA2 := gammaInverseIntegrable_smul n (abs c) (g 2) (hI 2 (by omega))
  have hA3 := gammaInverseIntegrable_smul n (abs d) (g 3) (hI 3 (by omega))
  have h01 := gammaInverseIntegrable_add n _ _ hA0 hA1
  have h012 := gammaInverseIntegrable_add n _ _ h01 hA2
  have hG : GammaInverseIntegrable n G :=
    gammaInverseIntegrable_add n _ _ h012 hA3
  have hPoint : forall s : Real, 0 <= s ->
      abs (Set.indicator E (gammaCubic a b c d) s) <= G s := by
    intro s hs
    by_cases hsE : Membership.mem E s
    case pos =>
      dsimp only [G, g]
      simp only [Set.indicator_of_mem hsE, gammaCubic, pow_zero, pow_one]
      have hA := abs_add_le (a + b * (s - 1) + c * (s - 1) ^ 2)
        (d * (s - 1) ^ 3)
      have hB := abs_add_le (a + b * (s - 1)) (c * (s - 1) ^ 2)
      have hC := abs_add_le a (b * (s - 1))
      simp only [abs_mul, abs_pow] at hA hB hC
      linarith only [hA, hB, hC]
    case neg =>
      dsimp only [G, g]
      simp only [Set.indicator_of_notMem hsE, abs_zero, mul_zero, add_zero]
      exact le_rfl
  have hBound := gammaInverseAverage_abs_le n
    (Set.indicator E (gammaCubic a b c d)) G hG hPoint
  change abs (gammaInverseAverage n (Set.indicator E (gammaCubic a b c d))) <=
    gammaInverseAverage n (fun s : Real =>
      (abs a * g 0 s + abs b * g 1 s + abs c * g 2 s) + abs d * g 3 s)
    at hBound
  rw [gammaInverseAverage_add n _ _ h012 hA3,
    gammaInverseAverage_add n _ _ h01 hA2,
    gammaInverseAverage_add n _ _ hA0 hA1,
    gammaInverseAverage_smul, gammaInverseAverage_smul,
    gammaInverseAverage_smul, gammaInverseAverage_smul] at hBound
  have hTail : forall j : Nat, j <= 3 ->
      gammaInverseAverage n (g j) <= e * ((2 : Real) ^ (2 * j) + 3) := by
    intro j hj
    exact gammaInverseAverage_abs_centered_tail n j (by omega)
      eps hEps0 hEps1 hLarge
  have hT0 := mul_le_mul_of_nonneg_left (hTail 0 (by omega)) (abs_nonneg a)
  have hT1 := mul_le_mul_of_nonneg_left (hTail 1 (by omega)) (abs_nonneg b)
  have hT2 := mul_le_mul_of_nonneg_left (hTail 2 (by omega)) (abs_nonneg c)
  have hT3 := mul_le_mul_of_nonneg_left (hTail 3 (by omega)) (abs_nonneg d)
  norm_num at hT0 hT1 hT2 hT3
  change abs (gammaInverseAverage n (Set.indicator E (gammaCubic a b c d))) <=
    e * (4 * abs a + 7 * abs b + 19 * abs c + 67 * abs d)
  nlinarith only [hBound, hT0, hT1, hT2, hT3]

theorem gammaInverseAverage_sub (n : Nat) (f g : Real -> Real)
    (hf : GammaInverseIntegrable n f) (hg : GammaInverseIntegrable n g) :
    gammaInverseAverage n (fun s : Real => f s - g s) =
      gammaInverseAverage n f - gammaInverseAverage n g := by
  have hFun : (fun t : Real => Real.exp (-t) * t ^ n *
      (f ((n : Real) / t) - g ((n : Real) / t))) =
      (fun t : Real => Real.exp (-t) * t ^ n * f ((n : Real) / t) -
        Real.exp (-t) * t ^ n * g ((n : Real) / t)) := by
    funext t
    ring
  unfold gammaInverseAverage
  rw [hFun, MeasureTheory.integral_sub hf hg]
  ring

theorem gammaInverseAverage_local_cubic (n : Nat) (hn : 16 <= n)
    (eps : Real) (hEps0 : 0 < eps) (hEps1 : eps <= 1 / 2)
    (hLarge : 4 <= (n : Real) * eps) (f : Real -> Real)
    (a b c d M : Real) (hM : 0 <= M)
    (hf : GammaInverseIntegrable n
      (Set.indicator {s : Real | abs (s - 1) <= eps} f))
    (hApprox : forall s : Real, abs (s - 1) <= eps ->
      abs (f s - gammaCubic a b c d s) <= M * (s - 1) ^ 4) :
    abs (gammaInverseAverage n
        (Set.indicator {s : Real | abs (s - 1) <= eps} f) -
      (a + c / ((n : Real) - 1) +
        4 * d / (((n : Real) - 1) * ((n : Real) - 2)))) <=
      M * (3 * ((n : Real) + 6) /
        (((n : Real) - 1) * ((n : Real) - 2) * ((n : Real) - 3))) +
      Real.exp (-((n : Real) + 1) * eps ^ 2 / 72) *
        (4 * abs a + 7 * abs b + 19 * abs c + 67 * abs d) := by
  let C : Set Real := {s | abs (s - 1) <= eps}
  let E : Set Real := {s | eps < abs (s - 1)}
  let p : Real -> Real := gammaCubic a b c d
  have hMap : Measurable (fun s : Real => abs (s - 1)) := by
    simpa only [Real.norm_eq_abs] using (measurable_sub_const (1 : Real)).norm
  have hC : MeasurableSet C := measurableSet_le hMap measurable_const
  have hE : MeasurableSet E := measurableSet_lt measurable_const hMap
  have hp := gammaCubic_integrable n (by omega) a b c d
  have hpC := gammaInverseIntegrable_indicator n p hp C hC
  have hpE := gammaInverseIntegrable_indicator n p hp E hE
  have hFourth := gammaInverseIntegrable_centered n 4 (by omega)
  have hRemainder := gammaInverseAverage_abs_le n
    (Set.indicator C (fun s : Real => f s - p s))
    (fun s : Real => M * (s - 1) ^ 4)
    (gammaInverseIntegrable_smul n M _ hFourth)
    (by
      intro s hs
      by_cases hsC : Membership.mem C s
      case pos =>
        simp only [Set.indicator_of_mem hsC]
        exact hApprox s hsC
      case neg =>
        simp only [Set.indicator_of_notMem hsC, abs_zero]
        have hPow : 0 <= (s - 1) ^ 4 := by
          nlinarith only [sq_nonneg ((s - 1) ^ 2)]
        exact mul_nonneg hM hPow)
  have hDiffFun : Set.indicator C (fun s : Real => f s - p s) =
      (fun s : Real => Set.indicator C f s - Set.indicator C p s) := by
    funext s
    by_cases hsC : Membership.mem C s
    case pos => simp only [Set.indicator_of_mem hsC]
    case neg => simp only [Set.indicator_of_notMem hsC, sub_self]
  rw [hDiffFun, gammaInverseAverage_sub n (Set.indicator C f)
    (Set.indicator C p) hf hpC, gammaInverseAverage_smul,
    gammaInverseAverage_fourth_uniform n (by omega)] at hRemainder
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
  have hMean := gammaInverseAverage_cubic n (by omega) a b c d
  have hTail := gammaInverseAverage_cubic_tail n (by omega)
    eps hEps0 hEps1 hLarge a b c d
  have hAlgebra :
      gammaInverseAverage n (Set.indicator C f) -
        (a + c / ((n : Real) - 1) +
          4 * d / (((n : Real) - 1) * ((n : Real) - 2))) =
      (gammaInverseAverage n (Set.indicator C f) -
        gammaInverseAverage n (Set.indicator C p)) -
        gammaInverseAverage n (Set.indicator E p) := by
    change gammaInverseAverage n p = _ at hMean
    linarith only [hSplit, hMean]
  change abs (gammaInverseAverage n (Set.indicator C f) -
    (a + c / ((n : Real) - 1) +
      4 * d / (((n : Real) - 1) * ((n : Real) - 2)))) <= _
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

theorem gammaInverseIntegrable_of_abs_le (n : Nat) (f g : Real -> Real)
    (hf : Measurable f) (hg : GammaInverseIntegrable n g)
    (hBound : forall s : Real, 0 <= s -> abs (f s) <= g s) :
    GammaInverseIntegrable n f := by
  have hm : Measurable (fun t : Real =>
      Real.exp (-t) * t ^ n * f ((n : Real) / t)) :=
    ((Real.continuous_exp.measurable.comp measurable_id.neg).mul
      (measurable_id.pow_const n)).mul
        (hf.comp (measurable_const.div measurable_id))
  apply hg.mono' hm.aestronglyMeasurable
  apply (MeasureTheory.ae_restrict_mem measurableSet_Ioi).mono
  intro t ht
  have hw : 0 <= Real.exp (-t) * t ^ n :=
    mul_nonneg (le_of_lt (Real.exp_pos _)) (pow_nonneg (le_of_lt ht) n)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hw]
  exact mul_le_mul_of_nonneg_left
    (hBound _ (div_nonneg (Nat.cast_nonneg n) (le_of_lt ht))) hw

theorem gammaCubic_measurable (a b c d : Real) :
    Measurable (gammaCubic a b c d) := by
  rw [gammaCubic_as_powers]
  have hBase : Measurable (fun s : Real => s - 1) :=
    measurable_sub_const (1 : Real)
  exact ((measurable_const.add (measurable_const.mul (hBase.pow_const 1))).add
    (measurable_const.mul (hBase.pow_const 2))).add
      (measurable_const.mul (hBase.pow_const 3))

theorem gammaCubic_window_integrable (n : Nat) (hn : 4 <= n)
    (eps : Real) (f : Real -> Real) (hf : Measurable f)
    (a b c d M : Real) (hM : 0 <= M)
    (hApprox : forall s : Real, abs (s - 1) <= eps ->
      abs (f s - gammaCubic a b c d s) <= M * (s - 1) ^ 4) :
    GammaInverseIntegrable n
      (Set.indicator {s : Real | abs (s - 1) <= eps} f) := by
  let C : Set Real := {s | abs (s - 1) <= eps}
  let p : Real -> Real := gammaCubic a b c d
  have hMap : Measurable (fun s : Real => abs (s - 1)) := by
    simpa only [Real.norm_eq_abs] using (measurable_sub_const (1 : Real)).norm
  have hC : MeasurableSet C := measurableSet_le hMap measurable_const
  have hMeas : Measurable (Set.indicator C (fun s : Real => f s - p s)) :=
    (hf.sub (gammaCubic_measurable a b c d)).indicator hC
  have hRem : GammaInverseIntegrable n
      (Set.indicator C (fun s : Real => f s - p s)) :=
    gammaInverseIntegrable_of_abs_le n _ _ hMeas
      (gammaInverseIntegrable_smul n M _ (gammaInverseIntegrable_centered n 4 hn))
      (by
        intro s hs
        by_cases hsC : Membership.mem C s
        case pos =>
          simp only [Set.indicator_of_mem hsC]
          exact hApprox s hsC
        case neg =>
          simp only [Set.indicator_of_notMem hsC, abs_zero]
          have hPow : 0 <= (s - 1) ^ 4 := by
            nlinarith only [sq_nonneg ((s - 1) ^ 2)]
          exact mul_nonneg hM hPow)
  have hpC := gammaInverseIntegrable_indicator n p
    (gammaCubic_integrable n (by omega) a b c d) C hC
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

theorem gammaInverseAverage_local_cubic_of_measurable (n : Nat) (hn : 16 <= n)
    (eps : Real) (hEps0 : 0 < eps) (hEps1 : eps <= 1 / 2)
    (hLarge : 4 <= (n : Real) * eps) (f : Real -> Real) (hf : Measurable f)
    (a b c d M : Real) (hM : 0 <= M)
    (hApprox : forall s : Real, abs (s - 1) <= eps ->
      abs (f s - gammaCubic a b c d s) <= M * (s - 1) ^ 4) :
    abs (gammaInverseAverage n
        (Set.indicator {s : Real | abs (s - 1) <= eps} f) -
      (a + c / ((n : Real) - 1) +
        4 * d / (((n : Real) - 1) * ((n : Real) - 2)))) <=
      M * (3 * ((n : Real) + 6) /
        (((n : Real) - 1) * ((n : Real) - 2) * ((n : Real) - 3))) +
      Real.exp (-((n : Real) + 1) * eps ^ 2 / 72) *
        (4 * abs a + 7 * abs b + 19 * abs c + 67 * abs d) :=
  gammaInverseAverage_local_cubic n hn eps hEps0 hEps1 hLarge f a b c d M hM
    (gammaCubic_window_integrable n (by omega) eps f hf a b c d M hM hApprox)
    hApprox

end PrimeFactorOscillations

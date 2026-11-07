/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Analysis.Real.Sqrt
import PrimeFactorOscillations.Helpers.FiniteWeightedRounding

/-! # Exact moment compensation removes the total-mass rounding loss -/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace PrimeFactorOscillations

def momentRoundThreshold : Real := 1 - Real.sqrt 2 / 2

def momentRoundIndicator (d y : Real) : Real := by
  classical
  exact if d <= y then 1 else 0

theorem momentRoundThreshold_bounds :
    And (0 < momentRoundThreshold) (momentRoundThreshold < 1 / 2) := by
  have hs := Real.sq_sqrt (show (0 : Real) <= 2 by norm_num)
  have hn := Real.sqrt_nonneg (2 : Real)
  dsimp [momentRoundThreshold]
  constructor <;> nlinarith

theorem momentRoundThreshold_equation :
    2 * momentRoundThreshold ^ 2 - 4 * momentRoundThreshold + 1 = 0 := by
  have hs := Real.sq_sqrt (show (0 : Real) <= 2 by norm_num)
  dsimp [momentRoundThreshold]
  nlinarith only [hs]

theorem momentRoundThreshold_gt_quarter :
    1 / 4 < momentRoundThreshold := by
  have hs := Real.sq_sqrt (show (0 : Real) <= 2 by norm_num)
  have hn := Real.sqrt_nonneg (2 : Real)
  dsimp [momentRoundThreshold]
  nlinarith

theorem momentRoundThreshold_admissible_iff (d : Real)
    (hd : 0 <= d) (hh : d <= 1 / 2) :
    0 <= 2 * d ^ 2 - 4 * d + 1 <-> d <= momentRoundThreshold := by
  have hBounds := momentRoundThreshold_bounds
  have hRoot := momentRoundThreshold_equation
  constructor
  case mp =>
    intro hQuad
    by_contra hNot
    have hStrict : momentRoundThreshold < d := lt_of_not_ge hNot
    have hProduct : 0 < (d - momentRoundThreshold) * (2 - d - momentRoundThreshold) :=
      mul_pos (sub_pos.mpr hStrict) (by linarith)
    nlinarith only [hQuad, hRoot, hProduct]
  case mpr =>
    intro hUpper
    have hProduct : 0 <= (momentRoundThreshold - d) * (2 - d - momentRoundThreshold) :=
      mul_nonneg (sub_nonneg.mpr hUpper) (by linarith)
    nlinarith only [hRoot, hProduct]

theorem momentRound_compensated_bounds (d y : Real)
    (hd : 0 <= d) (hh : d <= 1 / 2)
    (hQuad : 0 <= 2 * d ^ 2 - 4 * d + 1) (hy : 0 <= y) :
    And (-y * (y - 1) ^ 2 <= d * (2 * y - y ^ 2 - momentRoundIndicator d y))
      (d * (2 * y - y ^ 2 - momentRoundIndicator d y) <= y * (y - 1) ^ 2) := by
  classical
  unfold momentRoundIndicator
  by_cases hCut : d <= y
  case pos =>
    rw [ite_eq_left hCut]
    have hProduct := mul_nonneg (sub_nonneg.mpr hCut) (sq_nonneg (y - 1))
    have hD := mul_nonneg hd (sq_nonneg (y - 1))
    have hY := mul_nonneg hy (sq_nonneg (y - 1))
    constructor <;> nlinarith only [hProduct, hD, hY]
  case neg =>
    rw [ite_eq_right hCut]
    have hSmall : y < d := lt_of_not_ge hCut
    have hFactor : 0 <= (d - y) * (2 - 2 * d - y) :=
      mul_nonneg (by linarith) (by linarith)
    have hPolynomial : 0 <= (y - 1) ^ 2 - d * (2 - y) := by
      nlinarith only [hQuad, hFactor]
    have hUpper := mul_nonneg hy hPolynomial
    have hComp := mul_nonneg hd (mul_nonneg hy (show 0 <= 2 - y by linarith))
    have hEnergy := mul_nonneg hy (sq_nonneg (y - 1))
    constructor <;> nlinarith only [hUpper, hComp, hEnergy]

theorem momentRound_compensated_threshold_bounds (y : Real) (hy : 0 <= y) :
    And (-y * (y - 1) ^ 2 <=
      momentRoundThreshold * (2 * y - y ^ 2 - momentRoundIndicator momentRoundThreshold y))
      (momentRoundThreshold * (2 * y - y ^ 2 - momentRoundIndicator momentRoundThreshold y) <=
        y * (y - 1) ^ 2) := by
  exact momentRound_compensated_bounds momentRoundThreshold y
    (le_of_lt momentRoundThreshold_bounds.1) (le_of_lt momentRoundThreshold_bounds.2)
    (le_of_eq momentRoundThreshold_equation.symm) hy

theorem finiteWeightedCompensatedRound_ledger {Iota : Type*} (S : Finset Iota)
    (a y : Iota -> Real) (d : Real)
    (hMoment : Finset.sum S (fun i => a i * (y i) ^ 2) =
      Finset.sum S (fun i => a i * y i)) :
    Finset.sum S (fun i => a i * (2 * y i - (y i) ^ 2 - momentRoundIndicator d (y i))) =
      Finset.sum S (fun i => a i * y i) -
        Finset.sum S (fun i => a i * momentRoundIndicator d (y i)) := by
  calc
    _ = 2 * Finset.sum S (fun i => a i * y i) -
        Finset.sum S (fun i => a i * (y i) ^ 2) -
        Finset.sum S (fun i => a i * momentRoundIndicator d (y i)) := by
      calc
        _ = Finset.sum S (fun i =>
            2 * (a i * y i) - a i * (y i) ^ 2 -
              a i * momentRoundIndicator d (y i)) := by
          apply Finset.sum_congr rfl
          intro i _
          ring
        _ = _ := by
          rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, <- Finset.mul_sum]
    _ = _ := by
      rw [hMoment]
      ring

theorem finiteWeightedCompensatedRound_deviation {Iota : Type*} (S : Finset Iota)
    (a y : Iota -> Real)
    (ha : forall i, Membership.mem S i -> 0 <= a i)
    (hy : forall i, Membership.mem S i -> 0 <= y i)
    (hMoment : Finset.sum S (fun i => a i * (y i) ^ 2) =
      Finset.sum S (fun i => a i * y i)) :
    momentRoundThreshold * abs (Finset.sum S (fun i => a i * y i) -
      Finset.sum S (fun i => a i * momentRoundIndicator momentRoundThreshold (y i))) <=
        Finset.sum S (fun i => a i * y i * (y i - 1) ^ 2) := by
  have hLedger := finiteWeightedCompensatedRound_ledger S a y momentRoundThreshold hMoment
  have hLower : -Finset.sum S (fun i => a i * y i * (y i - 1) ^ 2) <=
      momentRoundThreshold * (Finset.sum S (fun i => a i * y i) -
        Finset.sum S (fun i => a i * momentRoundIndicator momentRoundThreshold (y i))) := by
    rw [<- hLedger, Finset.mul_sum, <- Finset.sum_neg_distrib]
    apply Finset.sum_le_sum
    intro i hi
    have h := _root_.mul_le_mul_of_nonneg_left
      (momentRound_compensated_threshold_bounds (y i) (hy i hi)).1 (ha i hi)
    nlinarith only [h]
  have hUpper : momentRoundThreshold * (Finset.sum S (fun i => a i * y i) -
      Finset.sum S (fun i => a i * momentRoundIndicator momentRoundThreshold (y i))) <=
        Finset.sum S (fun i => a i * y i * (y i - 1) ^ 2) := by
    rw [<- hLedger, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    have h := _root_.mul_le_mul_of_nonneg_left
      (momentRound_compensated_threshold_bounds (y i) (hy i hi)).2 (ha i hi)
    nlinarith only [h]
  have hAbs := abs_le.mpr (And.intro hLower hUpper)
  simpa only [abs_mul, abs_of_nonneg (le_of_lt momentRoundThreshold_bounds.1)] using hAbs

theorem finiteWeightedCompensatedRound_scaled {Iota : Type*} (S : Finset Iota)
    (a x : Iota -> Real) (t : Real) (ht : 0 < t)
    (ha : forall i, Membership.mem S i -> 0 <= a i)
    (hx : forall i, Membership.mem S i -> 0 <= x i)
    (hMoment : Finset.sum S (fun i => a i * (x i) ^ 2) =
      t * Finset.sum S (fun i => a i * x i)) :
    momentRoundThreshold * t ^ 3 * abs (Finset.sum S (fun i => a i * x i) / t -
      Finset.sum S (fun i => a i * momentRoundIndicator momentRoundThreshold (x i / t))) <=
        Finset.sum S (fun i => a i * x i * (x i - t) ^ 2) := by
  have hNormalized : Finset.sum S (fun i => a i * (x i / t) ^ 2) =
      Finset.sum S (fun i => a i * (x i / t)) := by
    calc
      _ = Finset.sum S (fun i => a i * (x i) ^ 2) / t ^ 2 := by
        simp only [div_pow]
        exact finiteWeighted_div_sum S a (fun i => (x i) ^ 2) (t ^ 2)
      _ = Finset.sum S (fun i => a i * x i) / t := by
        rw [hMoment]
        field_simp [ht.ne']
      _ = _ := (finiteWeighted_div_sum S a x t).symm
  have hRound := finiteWeightedCompensatedRound_deviation S a (fun i => x i / t) ha
    (fun i hi => div_nonneg (hx i hi) (le_of_lt ht)) hNormalized
  rw [finiteWeighted_div_sum] at hRound
  have hScaled := _root_.mul_le_mul_of_nonneg_left hRound (pow_nonneg (le_of_lt ht) 3)
  have hEnergy : t ^ 3 * Finset.sum S (fun i => a i * (x i / t) * (x i / t - 1) ^ 2) =
      Finset.sum S (fun i => a i * x i * (x i - t) ^ 2) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    have h := congrArg (fun q : Real => a i * q) (finiteWeighted_rescale_energy (x i) t ht)
    nlinarith only [h]
  calc
    _ = t ^ 3 * (momentRoundThreshold * abs (Finset.sum S (fun i => a i * x i) / t -
        Finset.sum S (fun i => a i * momentRoundIndicator momentRoundThreshold (x i / t)))) := by
      ring
    _ <= t ^ 3 * Finset.sum S (fun i => a i * (x i / t) * (x i / t - 1) ^ 2) := hScaled
    _ = _ := hEnergy

theorem momentRoundThreshold_pointwise_optimal (c : Real)
    (hc : forall y : Real, 0 <= y ->
      -y * (y - 1) ^ 2 <=
        c * (2 * y - y ^ 2 - momentRoundIndicator momentRoundThreshold y)) :
    c <= momentRoundThreshold := by
  have h := hc momentRoundThreshold (le_of_lt momentRoundThreshold_bounds.1)
  unfold momentRoundIndicator at h
  rw [ite_eq_left (le_refl momentRoundThreshold)] at h
  have hSquare : 0 < (momentRoundThreshold - 1) ^ 2 := by
    have hNot : Not (momentRoundThreshold - 1 = 0) := by
      have hSmall := momentRoundThreshold_bounds.2
      linarith
    exact sq_pos_of_ne_zero hNot
  by_contra hNot
  have hStrict : momentRoundThreshold < c := lt_of_not_ge hNot
  have hProduct := mul_pos (sub_pos.mpr hStrict) hSquare
  nlinarith only [h, hProduct]

end PrimeFactorOscillations

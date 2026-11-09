/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Mathlib.Analysis.MeanInequalities.SeparatedGrid

/-! # Rational normalization from a centered weighted law to equal first and second moments -/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 5000000

noncomputable section
namespace Finset

theorem centered_moment_normalization {Iota : Type*} (S : Finset Iota)
    (w z : Iota -> Real) (K F p : Real) (hK : 0 < K) (hF : 0 < F)
    (hMass : Finset.sum S w = K)
    (hCenter : Finset.sum S (fun i => w i * z i) = 0)
    (hSecond : Finset.sum S (fun i => w i * (z i) ^ 2) = F) :
    let rho := F / K
    let D := 1 + rho * p ^ 2
    let y := fun i => (1 + p * z i) / D
    And (0 < D)
      (And (Finset.sum S (fun i => w i * y i) = K / D)
        (And (Finset.sum S (fun i => w i * (y i) ^ 2) = K / D)
          (Finset.sum S (fun i => w i * (y i - 1 / D) ^ 2) =
            (p / D) ^ 2 * F))) := by
  dsimp only
  let rho := F / K
  let D := 1 + rho * p ^ 2
  let y := fun i => (1 + p * z i) / D
  have hrho : 0 < rho := div_pos hF hK
  have hD : 0 < D := by
    dsimp only [D]
    nlinarith only [mul_nonneg hrho.le (sq_nonneg p)]
  have hRho : K * rho = F := by
    dsimp only [rho]
    field_simp [ne_of_gt hK]
  have hFirst : Finset.sum S (fun i => w i * (1 + p * z i)) = K := by
    calc
      _ = Finset.sum S w + p * Finset.sum S (fun i => w i * z i) := by
        rw [Finset.mul_sum, <- Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = _ := by rw [hMass, hCenter]; ring
  have hSquare : Finset.sum S (fun i => w i * (1 + p * z i) ^ 2) = K * D := by
    calc
      _ = Finset.sum S w + (2 * p) * Finset.sum S (fun i => w i * z i) +
          p ^ 2 * Finset.sum S (fun i => w i * (z i) ^ 2) := by
        rw [Finset.mul_sum, Finset.mul_sum, <- Finset.sum_add_distrib,
          <- Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = _ := by rw [hMass, hCenter, hSecond, <- hRho]; dsimp only [D]; ring
  refine And.intro hD (And.intro ?_ (And.intro ?_ ?_))
  case refine_1 =>
    calc
      _ = Finset.sum S (fun i => w i * (1 + p * z i)) * (1 / D) := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i _
        change w i * ((1 + p * z i) / D) = w i * (1 + p * z i) * (1 / D)
        ring
      _ = _ := by rw [hFirst]; ring
  case refine_2 =>
    calc
      _ = Finset.sum S (fun i => w i * (1 + p * z i) ^ 2) * (1 / D ^ 2) := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i _
        change w i * ((1 + p * z i) / D) ^ 2 = w i * (1 + p * z i) ^ 2 * (1 / D ^ 2)
        ring
      _ = K / D := by rw [hSquare]; field_simp [ne_of_gt hD]
  case refine_3 =>
    calc
      _ = (p / D) ^ 2 * Finset.sum S (fun i => w i * (z i) ^ 2) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        change w i * ((1 + p * z i) / D - 1 / D) ^ 2 =
          (p / D) ^ 2 * (w i * (z i) ^ 2)
        field_simp [ne_of_gt hD]
        ring
      _ = _ := by rw [hSecond]

theorem momentNormalization_small_parameter (A rho K d eta : Real)
    (hA : 0 <= A) (hrho : 0 < rho) (hK : 0 < K)
    (hd : And (0 < d) (d < 1)) (heta : 0 < eta) :
    exists p : Real, And (0 < p) (And (p <= 1)
      (And (0 < K - K / (1 + rho * p ^ 2))
        (And (K - K / (1 + rho * p ^ 2) < eta)
          (And (forall z : Real, abs z <= A ->
            d < (1 + p * z) / (1 + rho * p ^ 2)) (p < eta))))) := by
  let B := (1 - d) / (2 * (A + rho + 1))
  let E := min (eta / (2 * K * rho)) eta
  let m := min 1 (min B E)
  let p := m / 2
  have hCoeff : 0 < 2 * (A + rho + 1) := by linarith only [hA, hrho]
  have hB : 0 < B := div_pos (sub_pos.mpr hd.2) hCoeff
  have hE : 0 < E := lt_min
    (div_pos heta (mul_pos (mul_pos (by norm_num) hK) hrho)) heta
  have hm : 0 < m := lt_min (by norm_num) (lt_min hB hE)
  have hp : 0 < p := div_pos hm (by norm_num)
  have hmOne : m <= 1 := min_le_left _ _
  have hmB : m <= B := le_trans (min_le_right _ _) (min_le_left _ _)
  have hmE : m <= E := le_trans (min_le_right _ _) (min_le_right _ _)
  have hpOne : p <= 1 := by dsimp only [p]; linarith only [hmOne, hm]
  have hpB : p <= B := by dsimp only [p]; linarith only [hmB, hm]
  have hpE : p <= E := by dsimp only [p]; linarith only [hmE, hm]
  have hScale := _root_.mul_le_mul_of_nonneg_right hpB hCoeff.le
  have hBId : B * (2 * (A + rho + 1)) = 1 - d := by
    dsimp only [B]
    field_simp [ne_of_gt hCoeff]
  rw [hBId] at hScale
  have hden : 0 < 1 + rho * p ^ 2 := by
    nlinarith only [mul_nonneg hrho.le (sq_nonneg p)]
  let delta := K - K / (1 + rho * p ^ 2)
  have hId : delta * (1 + rho * p ^ 2) = K * rho * p ^ 2 := by
    dsimp only [delta]
    field_simp [ne_of_gt hden]
    ring
  have hNum : 0 < K * rho * p ^ 2 := mul_pos (mul_pos hK hrho) (sq_pos_of_pos hp)
  have hDelta : 0 < delta := by
    by_contra hn
    have hProd := mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hn) hden.le
    nlinarith only [hProd, hId, hNum]
  have hDeltaUpper : delta <= K * rho * p ^ 2 := by
    have hExtra := mul_nonneg hDelta.le (mul_nonneg hrho.le (sq_nonneg p))
    nlinarith only [hId, hExtra]
  have hSq : p ^ 2 <= p := by nlinarith only [hp, hpOne]
  have hSqBound := _root_.mul_le_mul_of_nonneg_left hSq (mul_pos hK hrho).le
  have hpRaw : p <= eta / (2 * K * rho) := le_trans hpE (min_le_left _ _)
  have hLast := _root_.mul_le_mul_of_nonneg_left hpRaw (mul_pos hK hrho).le
  have hEId : K * rho * (eta / (2 * K * rho)) = eta / 2 := by
    field_simp [ne_of_gt hK, ne_of_gt hrho]
  rw [hEId] at hLast
  have hDeltaEta : delta < eta := by
    linarith only [hDeltaUpper, hSqBound, hLast, heta]
  have hpEta : p < eta := by
    have hmEta : m <= eta := le_trans hmE (min_le_right _ _)
    dsimp only [p]
    linarith only [hmEta, hm, heta]
  refine Exists.intro p (And.intro hp (And.intro hpOne
    (And.intro hDelta (And.intro hDeltaEta (And.intro ?_ hpEta)))))
  intro z hz
  have hZ : -A <= z := (abs_le.mp hz).1
  have hPZ := _root_.mul_le_mul_of_nonneg_left hZ hp.le
  have hR := _root_.mul_le_mul_of_nonneg_left hSq hrho.le
  have hDR := _root_.mul_le_mul_of_nonneg_right hd.2.le
    (mul_nonneg hrho.le (sq_nonneg p))
  have hCut : d * (1 + rho * p ^ 2) < 1 + p * z := by
    nlinarith only [hScale, hPZ, hR, hDR, hd.2, hp]
  have hY : ((1 + p * z) / (1 + rho * p ^ 2)) * (1 + rho * p ^ 2) = 1 + p * z := by
    field_simp [ne_of_gt hden]
  by_contra hn
  have hMul := _root_.mul_le_mul_of_nonneg_right (le_of_not_gt hn) hden.le
  nlinarith only [hMul, hY, hCut]

end Finset

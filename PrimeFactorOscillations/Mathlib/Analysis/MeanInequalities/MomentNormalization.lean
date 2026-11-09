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

end Finset

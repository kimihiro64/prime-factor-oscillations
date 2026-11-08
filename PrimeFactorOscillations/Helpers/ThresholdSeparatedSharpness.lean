/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Tactic.FinCases
import PrimeFactorOscillations.Helpers.ThresholdSeparatedSpectrum

/-! # Exact sharp collision profiles at every even selected mass -/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 5000000

noncomputable section
namespace PrimeFactorOscillations

def thresholdCollisionOrder (k : Nat) : Fin 2 -> Nat := ![1, k - 1]

def thresholdCollisionCoord (k : Nat) (q : Real) : Fin 2 -> Real :=
  ![(1 + ((k - 1 : Nat) : Real) * q) / (1 + ((k - 1 : Nat) : Real) * q ^ 2),
    (1 - q) / (1 + ((k - 1 : Nat) : Real) * q ^ 2)]

def thresholdCollisionGap (k : Nat) (q : Real) : Real :=
  (((k - 1 : Nat) : Real) + 1) * q / (1 + ((k - 1 : Nat) : Real) * q ^ 2)

theorem thresholdCollision_sum (k : Nat) (q : Real) (phi : Real -> Real) :
    Finset.sum Finset.univ (fun i => 2 * (thresholdCollisionOrder k i : Real) *
      phi (thresholdCollisionCoord k q i)) =
      2 * phi ((1 + ((k - 1 : Nat) : Real) * q) /
        (1 + ((k - 1 : Nat) : Real) * q ^ 2)) +
      2 * ((k - 1 : Nat) : Real) * phi ((1 - q) /
        (1 + ((k - 1 : Nat) : Real) * q ^ 2)) := by
  norm_num [Fin.sum_univ_succ, thresholdCollisionOrder, thresholdCollisionCoord]

theorem thresholdCollision_scalar (rho q : Real) (hrho : 1 <= rho) :
    let den := 1 + rho * q ^ 2
    let x := (1 + rho * q) / den
    let z := (1 - q) / den
    And (0 < den)
      (And (2 * x + 2 * rho * z = 2 * (rho + 1) / den)
        (And (2 * x ^ 2 + 2 * rho * z ^ 2 = 2 * (rho + 1) / den)
          (And (x - z = (rho + 1) * q / den)
            (2 * (x - 1 / den) ^ 2 + 2 * rho * (z - 1 / den) ^ 2 =
              2 * (rho + 1) * rho * q ^ 2 / den ^ 2)))) := by
  dsimp only
  have hden : 0 < 1 + rho * q ^ 2 := by
    nlinarith only [mul_nonneg (show 0 <= rho by linarith only [hrho]) (sq_nonneg q)]
  refine And.intro hden (And.intro ?_ (And.intro ?_ (And.intro ?_ ?_)))
  all_goals
    field_simp [ne_of_gt hden]
    ring

theorem thresholdCollision_cutoff (rho d q : Real)
    (hrho : 1 <= rho) (hd : And (0 < d) (d < 1))
    (hq : And (0 < q) (And (q <= 1) (q <= (1 - d) / (2 * (rho + 1))))) :
    And (d < (1 - q) / (1 + rho * q ^ 2))
      ((1 - q) / (1 + rho * q ^ 2) <
        (1 + rho * q) / (1 + rho * q ^ 2)) := by
  have hden := (thresholdCollision_scalar rho q hrho).1
  have hCoeff : 0 < 2 * (rho + 1) := by linarith only [hrho]
  have hQScale := _root_.mul_le_mul_of_nonneg_right hq.2.2 hCoeff.le
  have hCancel : (1 - d) / (2 * (rho + 1)) * (2 * (rho + 1)) = 1 - d := by
    field_simp [ne_of_gt hCoeff]
  rw [hCancel] at hQScale
  have hSq : q ^ 2 <= q := by nlinarith only [hq.1, hq.2.1]
  have hR := _root_.mul_le_mul_of_nonneg_left hSq (show 0 <= rho by linarith only [hrho])
  have hD := mul_nonneg (show 0 <= 1 - d by linarith only [hd.2])
    (mul_nonneg (show 0 <= rho by linarith only [hrho]) (sq_nonneg q))
  have hNum : d * (1 + rho * q ^ 2) < 1 - q := by
    nlinarith only [hQScale, hR, hD, hd.2]
  have hIdZ : ((1 - q) / (1 + rho * q ^ 2)) * (1 + rho * q ^ 2) = 1 - q := by
    field_simp [ne_of_gt hden]
  have hIdX : ((1 + rho * q) / (1 + rho * q ^ 2)) * (1 + rho * q ^ 2) = 1 + rho * q := by
    field_simp [ne_of_gt hden]
  have hFirst : d < (1 - q) / (1 + rho * q ^ 2) := by
    by_contra hn
    have hMul := _root_.mul_le_mul_of_nonneg_right (le_of_not_gt hn) hden.le
    nlinarith only [hMul, hIdZ, hNum]
  refine And.intro hFirst ?_
  by_contra hn
  have hMul := _root_.mul_le_mul_of_nonneg_right (le_of_not_gt hn) hden.le
  have hPos := mul_pos (show 0 < rho + 1 by linarith only [hrho]) hq.1
  nlinarith only [hMul, hIdX, hIdZ, hPos]

theorem thresholdCollision_sharpness (k : Nat) (d q : Real) (hk : 2 <= k)
    (hd : And (0 < d) (d < 1))
    (hq : And (0 < q) (And (q <= 1)
      (q <= (1 - d) / (2 * (((k - 1 : Nat) : Real) + 1))))) :
    let a := thresholdCollisionOrder k
    let y := thresholdCollisionCoord k q
    let w := fun i => 2 * (a i : Real)
    let K := 2 * (k : Real)
    let M := K / (1 + ((k - 1 : Nat) : Real) * q ^ 2)
    let delta := K - M
    let g := thresholdCollisionGap k q
    And (thresholdEvenAdmissible d M K a y)
      (And (Finset.sum Finset.univ w = K)
        (And (0 < g)
          (And (thresholdSelectedSeparated d Finset.univ a y g)
            (And (thresholdSelectedVariance d Finset.univ w y =
              thresholdVarianceBudget d 1 K delta)
              (thresholdSelectedVariance d Finset.univ w y =
                2 * (K - 2) * g ^ 2 / K))))) := by
  dsimp only
  let rho : Real := ((k - 1 : Nat) : Real)
  let den := 1 + rho * q ^ 2
  let x := (1 + rho * q) / den
  let z := (1 - q) / den
  let K := 2 * (k : Real)
  have hkOne : 1 <= k := by omega
  have hRho : rho = (k : Real) - 1 := by
    dsimp only [rho]
    rw [Nat.cast_sub hkOne]
    norm_num
  have hrho : 1 <= rho := by
    have hKR : (2 : Real) <= (k : Real) := by exact_mod_cast hk
    linarith only [hRho, hKR]
  have hScalar := thresholdCollision_scalar rho q hrho
  have hCut := thresholdCollision_cutoff rho d q hrho hd hq
  have hden : 0 < den := hScalar.1
  have hK : 0 < K := by dsimp only [K]; nlinarith only [hRho, hrho]
  have hKK : K = 2 * (rho + 1) := by dsimp only [K]; linarith only [hRho]
  have hZX : z < x := hCut.2
  have hDZ : d < z := hCut.1
  have hDX : d <= x := le_trans hDZ.le hZX.le
  have hCoordinates : forall i : Fin 2, d <= thresholdCollisionCoord k q i := by
    intro i
    fin_cases i
    next =>
      exact hDX
    next =>
      exact hDZ.le
  have hI : forall i : Fin 2, momentRoundIndicator d (thresholdCollisionCoord k q i) = 1 := by
    intro i
    simp only [momentRoundIndicator, ite_eq_left (hCoordinates i)]
  have hFirst : Finset.sum Finset.univ (fun i =>
      2 * (thresholdCollisionOrder k i : Real) * thresholdCollisionCoord k q i) = K / den := by
    rw [thresholdCollision_sum k q (fun u => u)]
    change 2 * x + 2 * rho * z = K / den
    have hKK : K = 2 * (rho + 1) := by dsimp only [K]; linarith only [hRho]
    rw [hKK]
    exact hScalar.2.1
  have hSecond : Finset.sum Finset.univ (fun i =>
      2 * (thresholdCollisionOrder k i : Real) * (thresholdCollisionCoord k q i) ^ 2) = K / den := by
    rw [thresholdCollision_sum k q (fun u => u ^ 2)]
    change 2 * x ^ 2 + 2 * rho * z ^ 2 = K / den
    have hKK : K = 2 * (rho + 1) := by dsimp only [K]; linarith only [hRho]
    rw [hKK]
    exact hScalar.2.2.1
  have hTotal : Finset.sum Finset.univ (fun i => 2 * (thresholdCollisionOrder k i : Real)) = K := by
    have h := thresholdCollision_sum k q (fun _ => (1 : Real))
    simp only [mul_one] at h
    change _ = K
    rw [h]
    change 2 + 2 * rho = K
    dsimp only [K]
    linarith only [hRho]
  have hSelected : thresholdSelectedMass d Finset.univ
      (fun i => 2 * (thresholdCollisionOrder k i : Real)) (thresholdCollisionCoord k q) = K := by
    unfold thresholdSelectedMass
    simp only [hI, mul_one]
    exact hTotal
  have hMu : thresholdSelectedMean d Finset.univ
      (fun i => 2 * (thresholdCollisionOrder k i : Real)) (thresholdCollisionCoord k q) = 1 / den := by
    unfold thresholdSelectedMean
    simp only [hI, mul_one]
    rw [hFirst, hSelected]
    field_simp [ne_of_gt hK]
  have hVar : thresholdSelectedVariance d Finset.univ
      (fun i => 2 * (thresholdCollisionOrder k i : Real)) (thresholdCollisionCoord k q) =
        K * rho * q ^ 2 / den ^ 2 := by
    unfold thresholdSelectedVariance
    simp only [hI, mul_one, hMu]
    rw [thresholdCollision_sum k q (fun u => (u - 1 / den) ^ 2)]
    change 2 * (x - 1 / den) ^ 2 + 2 * rho * (z - 1 / den) ^ 2 = K * rho * q ^ 2 / den ^ 2
    rw [hScalar.2.2.2.2]
    change 2 * (rho + 1) * rho * q ^ 2 / den ^ 2 = K * rho * q ^ 2 / den ^ 2
    rw [hKK]
  have hBudget : thresholdVarianceBudget d 1 K (K - K / den) =
      K * rho * q ^ 2 / den ^ 2 := by
    have hMeanLower : d <= 1 / den := by
      have hId : 1 / den - z = q / den := by
        dsimp only [z]
        ring
      have hQPos := div_nonneg hq.1.le hden.le
      linarith only [hId, hQPos, hDZ]
    have hProduct0 := _root_.mul_le_mul_of_nonneg_left hMeanLower hK.le
    have hProduct : K * d <= K / den := by
      simpa only [div_eq_mul_inv, one_mul] using hProduct0
    have hNeg : K - K / den - K * (1 - d) <= 0 := by
      nlinarith only [hProduct]
    unfold thresholdVarianceBudget
    rw [max_eq_right hNeg]
    dsimp only [den]
    field_simp [ne_of_gt hK, ne_of_gt hden]
    ring
  have hGap : 0 < thresholdCollisionGap k q := by
    exact div_pos (mul_pos (by linarith only [hrho]) hq.1) hden
  refine And.intro ?_ (And.intro hTotal (And.intro hGap (And.intro ?_
    (And.intro ?_ ?_))))
  next =>
    refine And.intro ?_ (And.intro hFirst (And.intro hSecond hSelected))
    intro i
    exact le_trans hd.1.le (hCoordinates i)
  next =>
    intro i j _ _ _ _ _ _ hNe
    fin_cases i <;> fin_cases j
    next =>
      exact False.elim (hNe rfl)
    next =>
      change thresholdCollisionGap k q <= abs (x - z)
      rw [abs_of_pos (sub_pos.mpr hZX), hScalar.2.2.2.1]
      rfl
    next =>
      change thresholdCollisionGap k q <= abs (z - x)
      rw [abs_sub_comm z x, abs_of_pos (sub_pos.mpr hZX), hScalar.2.2.2.1]
      rfl
    next =>
      exact False.elim (hNe rfl)
  next =>
    rw [hVar]
    exact hBudget.symm
  next =>
    rw [hVar]
    dsimp only [thresholdCollisionGap]
    change K * rho * q ^ 2 / den ^ 2 =
      2 * (K - 2) * ((rho + 1) * q / den) ^ 2 / K
    rw [hKK]
    have hRhoOne : Not (rho + 1 = 0) := by linarith only [hrho]
    field_simp [ne_of_gt hden, hRhoOne]
    ring

theorem thresholdCollision_small_parameter (rho K d eta : Real)
    (hrho : 1 <= rho) (hK : 0 < K) (hd : And (0 < d) (d < 1)) (heta : 0 < eta) :
    exists q : Real, And (0 < q) (And (q <= 1)
      (And (q <= (1 - d) / (2 * (rho + 1)))
        (And (0 < K - K / (1 + rho * q ^ 2))
          (K - K / (1 + rho * q ^ 2) < eta)))) := by
  let A := (1 - d) / (2 * (rho + 1))
  let E := eta / (2 * K * rho)
  let m := min 1 (min A E)
  let q := m / 2
  have hRho : 0 < rho := by linarith only [hrho]
  have hA : 0 < A := div_pos (sub_pos.mpr hd.2) (by linarith only [hrho])
  have hE : 0 < E := div_pos heta (mul_pos (mul_pos (by norm_num) hK) hRho)
  have hm : 0 < m := lt_min (by norm_num) (lt_min hA hE)
  have hq : 0 < q := div_pos hm (by norm_num)
  have hmOne : m <= 1 := min_le_left _ _
  have hmA : m <= A := le_trans (min_le_right _ _) (min_le_left _ _)
  have hmE : m <= E := le_trans (min_le_right _ _) (min_le_right _ _)
  have hqOne : q <= 1 := by dsimp only [q]; linarith only [hmOne, hm]
  have hqA : q <= A := by dsimp only [q]; linarith only [hmA, hm]
  have hqE : q <= E := by dsimp only [q]; linarith only [hmE, hm]
  let delta := K - K / (1 + rho * q ^ 2)
  have hden : 0 < 1 + rho * q ^ 2 := by
    nlinarith only [mul_nonneg hRho.le (sq_nonneg q)]
  have hId : delta * (1 + rho * q ^ 2) = K * rho * q ^ 2 := by
    dsimp only [delta]
    field_simp [ne_of_gt hden]
    ring
  have hNum : 0 < K * rho * q ^ 2 := mul_pos (mul_pos hK hRho) (sq_pos_of_pos hq)
  have hDelta : 0 < delta := by
    by_contra hn
    have hProd := mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hn) hden.le
    nlinarith only [hProd, hId, hNum]
  have hDeltaUpper : delta <= K * rho * q ^ 2 := by
    have hExtra := mul_nonneg hDelta.le (mul_nonneg hRho.le (sq_nonneg q))
    nlinarith only [hId, hExtra]
  have hSquare : q ^ 2 <= q := by nlinarith only [hq, hqOne]
  have hSqBound := _root_.mul_le_mul_of_nonneg_left hSquare (mul_pos hK hRho).le
  have hLast := _root_.mul_le_mul_of_nonneg_left hqE (mul_pos hK hRho).le
  have hEId : K * rho * E = eta / 2 := by
    dsimp only [E]
    field_simp [ne_of_gt hK, ne_of_gt hRho]
  rw [hEId] at hLast
  refine Exists.intro q (And.intro hq (And.intro hqOne (And.intro hqA
    (And.intro hDelta ?_))))
  change delta < eta
  linarith only [hDeltaUpper, hSqBound, hLast, heta]

end PrimeFactorOscillations

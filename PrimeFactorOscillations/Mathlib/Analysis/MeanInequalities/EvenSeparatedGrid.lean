/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Mathlib.Analysis.MeanInequalities.SeparatedGrid

/-! # Centered consecutive grids with positive natural orders and prescribed even mass -/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 5000000

noncomputable section
namespace Finset

def separatedGridOrder (r k : Nat) (j i : Fin r) : Nat :=
  1 + if i = j then k - r else 0

theorem even_separatedGrid_centered (r k : Nat) (hr : 2 <= r) (hkr : r <= k) :
    let K := 2 * (k : Real)
    let F := separatedVarianceFloor r 2 K
    exists a : Fin r -> Nat, exists z : Fin r -> Real,
      And (forall i, 0 < a i)
        (And (Finset.sum Finset.univ (fun i => 2 * (a i : Real)) = K)
          (And (Finset.sum Finset.univ (fun i => 2 * (a i : Real) * z i) = 0)
            (And (Finset.sum Finset.univ (fun i => 2 * (a i : Real) * (z i) ^ 2) = F)
              (And (0 < F)
                (forall i j, z j - z i = (j.val : Real) - (i.val : Real)))))) := by
  classical
  dsimp only
  let K : Real := 2 * (k : Real)
  let F := separatedVarianceFloor r 2 K
  have hr0 : 0 < r := by omega
  have hrR : (2 : Real) <= (r : Real) := by exact_mod_cast hr
  have hkrR : (r : Real) <= (k : Real) := by exact_mod_cast hkr
  have hKbound : 2 * (r : Real) <= K := by dsimp only [K]; linarith only [hkrR]
  have hK : 0 < K := by linarith only [hKbound, hrR]
  choose j hj using separatedGridParity_attained r hr0
  let a := separatedGridOrder r k j
  let w := fun i => 2 * (a i : Real)
  let u := separatedGridCoord r
  let H := Finset.sum Finset.univ (fun i => w i * u i)
  let z := fun i => u i - H / K
  have hWeight : w = separatedGridWeights r 2 K j := by
    funext i
    by_cases hi : i = j
    case pos =>
      simp only [w, a, separatedGridOrder, separatedGridWeights, ite_eq_left hi,
        Nat.cast_add, Nat.cast_one, Nat.cast_sub hkr]
      dsimp only [K]
      ring
    case neg =>
      simp [w, a, separatedGridOrder, separatedGridWeights, hi]
  have hProps := separatedGridWeights_properties r 2 K j hKbound
  have hMass : Finset.sum Finset.univ w = K := by rw [hWeight]; exact hProps.2
  have hNum : weightedVarianceNumerator Finset.univ w u = K * F := by
    have hFormula := separatedGridWeights_numerator r 2 K j hKbound hj
    have hFloor : K * F =
        2 * K * ((r : Real) * ((r : Real) ^ 2 - 1) / 12) +
          2 * (r : Real) * (K - 2 * (r : Real)) * separatedGridParity r := by
      dsimp only [F, separatedVarianceFloor]
      field_simp [ne_of_gt hK]
    rw [hWeight]
    exact hFormula.trans hFloor.symm
  have hCenter : Finset.sum Finset.univ (fun i => w i * z i) = 0 := by
    calc
      _ = H - (H / K) * K := by
        calc
          _ = Finset.sum Finset.univ (fun i => w i * u i - (H / K) * w i) := by
            apply Finset.sum_congr rfl
            intro i _
            dsimp only [z]
            ring
          _ = _ := by rw [Finset.sum_sub_distrib, <- Finset.mul_sum, hMass]
      _ = 0 := by field_simp [ne_of_gt hK]; ring
  have hSecond : Finset.sum Finset.univ (fun i => w i * (z i) ^ 2) = F := by
    have h := weightedVarianceNumerator_centered Finset.univ w u
      (by rw [hMass]; exact ne_of_gt hK)
    rw [hMass] at h
    change K * Finset.sum Finset.univ (fun i => w i * (z i) ^ 2) =
      weightedVarianceNumerator Finset.univ w u at h
    rw [hNum] at h
    have hInv : (1 / K) * K = 1 := by field_simp [ne_of_gt hK]
    have hCancel := congrArg (fun v : Real => (1 / K) * v) h
    simpa only [<- mul_assoc, hInv, one_mul] using hCancel
  have hF : 0 < F := by
    have hSq : 0 < (r : Real) ^ 2 - 1 := by
      nlinarith only [hrR, sq_nonneg ((r : Real) - 2)]
    have hBase : 0 < 2 * (r : Real) * ((r : Real) ^ 2 - 1) / 12 :=
      div_pos (mul_pos (mul_pos (by norm_num) (by linarith only [hrR])) hSq) (by norm_num)
    have hParity : 0 <= separatedGridParity r := by
      unfold separatedGridParity
      split_ifs <;> norm_num
    have hCorr : 0 <=
        2 * (r : Real) * (K - 2 * (r : Real)) * separatedGridParity r / K :=
      div_nonneg (mul_nonneg
        (mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg r))
          (sub_nonneg.mpr hKbound)) hParity) hK.le
    exact add_pos_of_pos_of_nonneg hBase hCorr
  have hPos : forall i, 0 < a i := by
    intro i
    dsimp only [a, separatedGridOrder]
    omega
  have hGap : forall i j, z j - z i = (j.val : Real) - (i.val : Real) := by
    intro i j
    dsimp only [z, u, separatedGridCoord]
    ring
  exact Exists.intro a (Exists.intro z
    (And.intro hPos (And.intro hMass (And.intro hCenter
      (And.intro hSecond (And.intro hF hGap))))))

end Finset

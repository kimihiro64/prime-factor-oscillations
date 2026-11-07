/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.ThresholdTotalModels

/-! # The signed order threshold at an arithmetic energy boundary -/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 5000000

noncomputable section
namespace PrimeFactorOscillations

theorem thresholdThree_total (m k : Nat) :
    Finset.sum Finset.univ (fun i => 2 * (thresholdThreeWeights m k i : Real)) =
      2 * ((k : Real) + (m : Real) + 1) := by
  have h := thresholdThree_sum m k 0 0 0 (fun _ => (1 : Real))
  simp only [mul_one] at h
  rw [h]
  ring

theorem thresholdEvenEnergy_pad {r : Nat} (a : Fin r -> Nat)
    (y : Fin r -> Real) (q : Nat) :
    thresholdEvenEnergy (thresholdPadWeights q a) (thresholdPadCoords y) =
      thresholdEvenEnergy a y := by
  simp [thresholdEvenEnergy, thresholdPadWeights, thresholdPadCoords, Fin.sum_univ_succ]

theorem thresholdTotal_lattice_ledger (d M N k m z : Real)
    (hMass : M = 2 * (k * z + m * d))
    (hMoment : k * z * (z - 1) = m * d * (1 - d)) :
    (1 - 2 * z) * M + z ^ 2 * N - (d - z) ^ 2 * (N - 2 * k) =
      d * (2 * z - d) * (N - 2 * (k + m)) := by
  rw [hMass]
  nlinarith only [hMoment]

theorem thresholdTotalAdmissible_lattice_order {r : Nat} (d M : Real)
    (n k m : Nat) (z : Real) (a : Fin r -> Nat) (y : Fin r -> Real)
    (hd : And (0 < d) (d < 1)) (hk : 0 < k) (hm : 0 < m) (hz : 1 <= z)
    (hMass : M = 2 * ((k : Real) * z + (m : Real) * d))
    (hMoment : (k : Real) * z * (z - 1) = (m : Real) * d * (1 - d))
    (hAd : thresholdTotalAdmissible d M (2 * (n : Real)) (2 * (k : Real)) a y) :
    k + m + 1 <= n := by
  have hkR : (0 : Real) < (k : Real) := by exact_mod_cast hk
  have hmR : (0 : Real) < (m : Real) := by exact_mod_cast hm
  have hKM : 2 * (k : Real) < M := by
    have hzK := mul_nonneg hkR.le (sub_nonneg.mpr hz)
    have hmD := mul_pos hmR hd.1
    nlinarith only [hMass, hzK, hmD]
  have hMN := thresholdEvenAdmissible_le_total d M (2 * (n : Real))
    (2 * (k : Real)) a y hAd.1 hAd.2
  have hKN : 2 * (k : Real) < 2 * (n : Real) := lt_of_lt_of_le hKM hMN
  have ha : forall i, Membership.mem Finset.univ i -> 0 <= 2 * (a i : Real) :=
    fun i _ => mul_nonneg (by norm_num : (0 : Real) <= 2) (Nat.cast_nonneg (a i))
  have hLow : thresholdSelectedMass d Finset.univ (fun i => 2 * (a i : Real)) y <
      Finset.sum Finset.univ (fun i => 2 * (a i : Real)) := by
    rw [hAd.2.2.2.2, hAd.1]
    exact hKN
  have hLed := finiteWeighted_total_packet_ledger Finset.univ
    (fun i => 2 * (a i : Real)) y d z (by rw [hAd.2.2.2.1, hAd.2.2.1])
  rw [hAd.2.2.1, hAd.1, hAd.2.2.2.2] at hLed
  have hPos := finiteWeighted_total_packet_pos Finset.univ
    (fun i => 2 * (a i : Real)) y d z (lt_of_lt_of_le hd.2 hz) ha hLow
  rw [hLed, thresholdTotal_lattice_ledger d M (2 * (n : Real))
    (k : Real) (m : Real) z hMass hMoment] at hPos
  have hCoef : 0 < d * (2 * z - d) :=
    mul_pos hd.1 (by linarith only [hz, hd.2])
  have hOrder : 2 * ((k : Real) + (m : Real)) < 2 * (n : Real) := by
    by_contra hn
    have hNonpos := mul_nonpos_of_nonneg_of_nonpos hCoef.le
      (sub_nonpos.mpr (le_of_not_gt hn))
    linarith only [hPos, hNonpos]
  have hCast : ((k + m : Nat) : Real) < (n : Real) := by
    rw [Nat.cast_add]
    linarith only [hOrder]
  have hNat : k + m < n := by exact_mod_cast hCast
  omega

theorem thresholdPositiveRoot_lattice_data (d M : Real) (k m : Nat)
    (hd : And (0 < d) (d < 1)) (hk : 0 < k) (hKM : 2 * (k : Real) <= M)
    (hLattice : M - 2 * (k : Real) * thresholdPositiveRoot d M (2 * (k : Real)) =
      2 * d * (m : Real)) :
    let z := thresholdPositiveRoot d M (2 * (k : Real))
    And (1 <= z) (And (M = 2 * ((k : Real) * z + (m : Real) * d))
      ((k : Real) * z * (z - 1) = (m : Real) * d * (1 - d))) := by
  dsimp only
  have hkR : (0 : Real) < (k : Real) := by exact_mod_cast hk
  have hK : 0 < 2 * (k : Real) := mul_pos (by norm_num) hkR
  have hM : 0 < M := lt_of_lt_of_le hK hKM
  have hz := (thresholdPositiveRoot_bounds d M (2 * (k : Real)) hd hM hK hKM).2
  have hMass : M = 2 * ((k : Real) * thresholdPositiveRoot d M (2 * (k : Real)) +
      (m : Real) * d) := by nlinarith only [hLattice]
  have hr := thresholdPositiveRoot_relation d M (2 * (k : Real)) hd hM hK
  have hMassScaled := congrArg (fun q : Real => (1 - d) * q) hMass
  exact And.intro hz (And.intro hMass (by nlinarith only [hr, hMassScaled]))

end PrimeFactorOscillations

/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.ThresholdTotalPackets

/-! # Exact fixed-total upper root and its strict cutoff face -/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 5000000

noncomputable section
namespace PrimeFactorOscillations

def thresholdTotalUpper (d N K : Real) : Real :=
  (N - K) * d + K * thresholdModelHigh (N - K) K d

theorem thresholdTotalUpper_formula (d N K : Real)
    (hd : And (0 < d) (d < 1)) (hK : 0 < K) (hKN : K <= N) :
    thresholdTotalUpper d N K = d * (N - K) + K / 2 +
      Real.sqrt (K ^ 2 / 4 + K * (N - K) * d * (1 - d)) := by
  let D := 1 + 4 * ((N - K) / K) * d * (1 - d)
  let E := K ^ 2 / 4 + K * (N - K) * d * (1 - d)
  have hJ : 0 <= N - K := sub_nonneg.mpr hKN
  have hp := mul_nonneg (mul_nonneg (div_nonneg hJ hK.le) hd.1.le)
    (sub_nonneg.mpr hd.2.le)
  have hD : 0 <= D := by dsimp [D]; nlinarith only [hp]
  have hSq : (K * Real.sqrt D / 2) ^ 2 = E := by
    calc
      _ = K ^ 2 / 4 * (Real.sqrt D) ^ 2 := by ring
      _ = E := by
        rw [Real.sq_sqrt hD]
        dsimp [D, E]
        field_simp [hK.ne']
        <;> ring
  have hQ : 0 <= K * Real.sqrt D / 2 :=
    div_nonneg (mul_nonneg hK.le (Real.sqrt_nonneg D)) (by norm_num)
  have hE : 0 <= E := by rw [<- hSq]; exact sq_nonneg _
  have hRad := Real.sq_sqrt hE
  have hRoot : K * Real.sqrt D / 2 = Real.sqrt E := by
    nlinarith only [hSq, hQ, hRad, Real.sqrt_nonneg E]
  unfold thresholdTotalUpper thresholdModelHigh
  change (N - K) * d + K * ((1 + Real.sqrt D) / 2) = d * (N - K) + K / 2 + Real.sqrt E
  nlinarith only [hRoot]

theorem thresholdTotalUpper_diagonal (d K : Real) : thresholdTotalUpper d K K = K := by
  simp [thresholdTotalUpper, thresholdModelHigh]

theorem thresholdTotalUpper_open_bounds (d N K : Real)
    (hd : And (0 < d) (d < 1)) (hK : 0 < K) (hKN : K < N) :
    And (K < thresholdTotalUpper d N K) (thresholdTotalUpper d N K < N) := by
  let J := N - K
  let v := thresholdModelHigh J K d
  have hJ : 0 < J := sub_pos.mpr hKN
  have hV : 1 <= v := thresholdModelHigh_bounds J K d hJ.le hK (And.intro hd.1.le hd.2.le)
  have hMoment := thresholdModelHigh_moment J K d hJ.le hK (And.intro hd.1.le hd.2.le)
  change J * d ^ 2 + K * v ^ 2 = J * d + K * v at hMoment
  have hUpper : thresholdTotalUpper d N K = J * d + K * v := rfl
  have hLow : K < thresholdTotalUpper d N K := by
    have hp := mul_nonneg hK.le (sub_nonneg.mpr hV)
    rw [hUpper]
    nlinarith only [hp, mul_pos hJ hd.1]
  have hVar : N - thresholdTotalUpper d N K = J * (d - 1) ^ 2 + K * (v - 1) ^ 2 := by
    rw [hUpper]
    have hN : N = J + K := by dsimp [J]; ring
    rw [hN]
    nlinarith only [hMoment]
  have hStrict := mul_pos hJ (sq_pos_of_ne_zero (sub_ne_zero.mpr (ne_of_lt hd.2)))
  have hOther := mul_nonneg hK.le (sq_nonneg (v - 1))
  exact And.intro hLow (by linarith only [hVar, hStrict, hOther])

theorem finiteWeighted_threshold_total_upper {Iota : Type*} (S : Finset Iota)
    (a y : Iota -> Real) (d : Real) (hd : And (0 < d) (d < 1))
    (ha : forall i, Membership.mem S i -> 0 <= a i)
    (hMoment : Finset.sum S (fun i => a i * (y i) ^ 2) = Finset.sum S (fun i => a i * y i))
    (hK : 0 < thresholdSelectedMass d S a y)
    (hLow : thresholdSelectedMass d S a y < Finset.sum S a) :
    Finset.sum S (fun i => a i * y i) <
      thresholdTotalUpper d (Finset.sum S a) (thresholdSelectedMass d S a y) := by
  let N := Finset.sum S a
  let K := thresholdSelectedMass d S a y
  let M := Finset.sum S (fun i => a i * y i)
  let J := N - K
  let v := thresholdModelHigh J K d
  have hJ : 0 < J := sub_pos.mpr hLow
  have hV : 1 <= v := thresholdModelHigh_bounds J K d hJ.le hK (And.intro hd.1.le hd.2.le)
  have hdv : d < v := lt_of_lt_of_le hd.2 hV
  have hMomentModel := thresholdModelHigh_moment J K d hJ.le hK (And.intro hd.1.le hd.2.le)
  change J * d ^ 2 + K * v ^ 2 = J * d + K * v at hMomentModel
  have hLedger := finiteWeighted_total_packet_ledger S a y d v hMoment
  have hPositive := finiteWeighted_total_packet_pos S a y d v hdv ha hLow
  have hIdentity : (1 - 2 * v) * M + v ^ 2 * N - (d - v) ^ 2 * (N - K) =
      (2 * v - 1) * (thresholdTotalUpper d N K - M) := by
    change (1 - 2 * v) * M + v ^ 2 * N - (d - v) ^ 2 * J =
      (2 * v - 1) * (J * d + K * v - M)
    have hN : N = J + K := by dsimp [J]; ring
    rw [hN]
    nlinarith only [hMomentModel]
  have hProduct : 0 < (2 * v - 1) * (thresholdTotalUpper d N K - M) := by
    rw [<- hIdentity, <- hLedger]
    exact hPositive
  change M < thresholdTotalUpper d N K
  nlinarith only [hProduct, hV]

theorem thresholdEvenAdmissible_total_upper {r : Nat} (d M N K : Real)
    (a : Fin r -> Nat) (y : Fin r -> Real)
    (hd : And (0 < d) (d < 1)) (hK : 0 < K) (hKN : K < N)
    (hTotal : Finset.sum Finset.univ (fun i => 2 * (a i : Real)) = N)
    (hAd : thresholdEvenAdmissible d M K a y) : M < thresholdTotalUpper d N K := by
  have h := finiteWeighted_threshold_total_upper Finset.univ (fun i => 2 * (a i : Real)) y d hd
    (fun i _ => mul_nonneg (by norm_num : (0 : Real) <= 2) (Nat.cast_nonneg (a i)))
    (by rw [hAd.2.2.1, hAd.2.1]) (by rw [hAd.2.2.2]; exact hK)
    (by rw [hAd.2.2.2, hTotal]; exact hKN)
  simpa only [hAd.2.1, hAd.2.2.2, hTotal] using h

theorem thresholdEvenAdmissible_le_total {r : Nat} (d M N K : Real)
    (a : Fin r -> Nat) (y : Fin r -> Real)
    (hTotal : Finset.sum Finset.univ (fun i => 2 * (a i : Real)) = N)
    (hAd : thresholdEvenAdmissible d M K a y) : M <= N := by
  have h := finiteWeighted_equal_moment_le_total Finset.univ (fun i => 2 * (a i : Real)) y
    (fun i _ => mul_nonneg (by norm_num : (0 : Real) <= 2) (Nat.cast_nonneg (a i)))
    (by rw [hAd.2.2.1, hAd.2.1])
  simpa only [hAd.2.1, hTotal] using h

end PrimeFactorOscillations

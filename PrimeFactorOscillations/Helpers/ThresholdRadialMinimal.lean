/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.ThresholdRadialCard

/-! # Exact minimum positive-weight radial support in the full feasible region -/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 5000000

noncomputable section
namespace PrimeFactorOscillations

def thresholdMinimumRadialCount (M N K : Real) : Nat := by
  classical
  exact if And (N = K) (M = K) then 1 else if And (M < K) (K < N) then 3 else 2

theorem finiteWeighted_minimum_radius_card {Iota : Type*} (S : Finset Iota)
    (a y : Iota -> Real) (d : Real) (hd : And (0 < d) (d < 1))
    (ha : forall i, Membership.mem S i -> 0 <= a i)
    (hy : forall i, Membership.mem S i -> 0 <= y i)
    (hMoment : Finset.sum S (fun i => a i * (y i) ^ 2) = Finset.sum S (fun i => a i * y i))
    (hMass : 0 < Finset.sum S (fun i => a i * y i)) :
    thresholdMinimumRadialCount (Finset.sum S (fun i => a i * y i)) (Finset.sum S a)
      (thresholdSelectedMass d S a y) <= (thresholdRadialSupport S a y).card := by
  classical
  let M := Finset.sum S (fun i => a i * y i)
  let N := Finset.sum S a
  let K := thresholdSelectedMass d S a y
  change thresholdMinimumRadialCount M N K <= (thresholdRadialSupport S a y).card
  by_cases hOne : And (N = K) (M = K)
  case pos =>
    simpa only [thresholdMinimumRadialCount, if_pos hOne] using
      finiteWeighted_radius_card_pos S a y ha hy hMoment hMass
  case neg =>
    by_cases hThree : And (M < K) (K < N)
    case pos =>
      simpa only [thresholdMinimumRadialCount, if_neg hOne, if_pos hThree] using
        finiteWeighted_three_radius_card S a y d hd ha hy hMoment hMass hThree.1 hThree.2
    case neg =>
      have hMin : thresholdMinimumRadialCount M N K = 2 := by
        simp only [thresholdMinimumRadialCount, if_neg hOne, if_neg hThree]
      rw [hMin]
      by_contra hn
      have hCard : (thresholdRadialSupport S a y).card <= 1 := by omega
      have hRigid := finiteWeighted_one_radius_rigid S a y d hd.2 ha hy hMoment hMass hCard
      exact hOne (And.intro hRigid.2.symm (hRigid.1.trans hRigid.2.symm))

theorem thresholdTotalAdmissible_minimum_card {r : Nat} (d M N K : Real)
    (a : Fin r -> Nat) (y : Fin r -> Real) (hd : And (0 < d) (d < 1)) (hK : 0 < K)
    (hAd : thresholdTotalAdmissible d M N K a y) :
    thresholdMinimumRadialCount M N K <=
      (thresholdRadialSupport Finset.univ (fun i => 2 * (a i : Real)) y).card := by
  have hA := hAd.2
  have hDomain := thresholdEvenAdmissible_domain d M K a y hd hK hA
  have h := finiteWeighted_minimum_radius_card Finset.univ (fun i => 2 * (a i : Real)) y d hd
    (fun i _ => mul_nonneg (by norm_num : (0 : Real) <= 2) (Nat.cast_nonneg (a i)))
    (fun i _ => hA.1 i) (by rw [hA.2.2.1, hA.2.1]) (by rw [hA.2.1]; exact hDomain.1)
  simpa only [hA.2.1, hAd.1, hA.2.2.2] using h

theorem thresholdTotal_one_site (d : Real) (k : Nat) (hd : d < 1) :
    thresholdTotalAdmissible d (2 * (k : Real)) (2 * (k : Real)) (2 * (k : Real))
      (fun _ : Fin 1 => k) (fun _ : Fin 1 => (1 : Real)) := by
  norm_num [thresholdTotalAdmissible, thresholdEvenAdmissible, thresholdSelectedMass,
    Fin.sum_univ_succ, momentRoundIndicator, hd.le]

theorem thresholdTotal_bounded_two_site (d M : Real) (k : Nat)
    (hd : And (0 < d) (d < 1)) (hk : 0 < k)
    (hLow : thresholdMinimumMass d (2 * (k : Real)) <= M) (hMK : M < 2 * (k : Real)) :
    exists a : Fin 2 -> Nat, exists y : Fin 2 -> Real,
      thresholdTotalAdmissible d M (2 * (k : Real)) (2 * (k : Real)) a y := by
  classical
  choose a y hA using (thresholdEven_two_atom_feasibility d M k hd hk).mpr hLow
  have hkR : (0 : Real) < (k : Real) := by exact_mod_cast hk
  have hK : 0 < 2 * (k : Real) := by linarith only [hkR]
  have hDomain := thresholdEvenAdmissible_domain d M (2 * (k : Real)) a y hd hK hA
  have ha : forall i : Fin 2, Membership.mem Finset.univ i -> 0 <= 2 * (a i : Real) :=
    fun i _ => mul_nonneg (by norm_num : (0 : Real) <= 2) (Nat.cast_nonneg (a i))
  have hLe := finiteWeighted_threshold_le_total Finset.univ (fun i => 2 * (a i : Real)) y d ha
  rw [hA.2.2.2] at hLe
  have hTotal : Finset.sum Finset.univ (fun i => 2 * (a i : Real)) = 2 * (k : Real) := by
    by_contra hn
    have hStrict : 2 * (k : Real) < Finset.sum Finset.univ (fun i => 2 * (a i : Real)) := by
      by_contra hNot
      exact hn (le_antisymm (le_of_not_gt hNot) hLe)
    have hThree := finiteWeighted_three_radius_card Finset.univ (fun i => 2 * (a i : Real)) y d hd ha
      (fun i _ => hA.1 i) (by rw [hA.2.2.1, hA.2.1]) (by rw [hA.2.1]; exact hDomain.1)
      (by rw [hA.2.1, hA.2.2.2]; exact hMK) (by rw [hA.2.2.2]; exact hStrict)
    have hUpper := thresholdRadialSupport_card_le_fin (fun i : Fin 2 => 2 * (a i : Real)) y
    omega
  exact Exists.intro a (Exists.intro y (And.intro hTotal hA))

theorem thresholdTotal_minimal_support_witness (d M : Real) (n k : Nat)
    (hd : And (0 < d) (d < 1)) (hk : 0 < k) (hkn : k <= n)
    (hRegion : And (thresholdMinimumMass d (2 * (k : Real)) <= M)
      (if n = k then M <= 2 * (k : Real)
       else M < thresholdTotalUpper d (2 * (n : Real)) (2 * (k : Real)))) :
    exists r : Nat, exists a : Fin r -> Nat, exists y : Fin r -> Real,
      And (thresholdTotalAdmissible d M (2 * (n : Real)) (2 * (k : Real)) a y)
        (r <= thresholdMinimumRadialCount M (2 * (n : Real)) (2 * (k : Real))) := by
  classical
  by_cases heq : n = k
  case pos =>
    by_cases hM : M = 2 * (k : Real)
    case pos =>
      have hMin : thresholdMinimumRadialCount M (2 * (n : Real)) (2 * (k : Real)) = 1 := by
        simp only [thresholdMinimumRadialCount, heq, hM, and_self, if_true]
      have hA := thresholdTotal_one_site d k hd.2
      have hAd : thresholdTotalAdmissible d M (2 * (n : Real)) (2 * (k : Real))
          (fun _ : Fin 1 => k) (fun _ : Fin 1 => (1 : Real)) := by simpa only [heq, hM] using hA
      exact Exists.intro 1 (Exists.intro _ (Exists.intro _ (And.intro hAd (by rw [hMin]))))
    case neg =>
      have hHigh := hRegion.2
      simp only [if_pos heq] at hHigh
      have hMK : M < 2 * (k : Real) := lt_of_le_of_ne hHigh hM
      choose a y hA using thresholdTotal_bounded_two_site d M k hd hk hRegion.1 hMK
      have hNotOne : Not (And (2 * (n : Real) = 2 * (k : Real)) (M = 2 * (k : Real))) := fun h => hM h.2
      have hNotThree : Not (And (M < 2 * (k : Real)) (2 * (k : Real) < 2 * (n : Real))) := by
        intro h
        have hh := h.2
        rw [heq] at hh
        exact (lt_irrefl _) hh
      have hMin : thresholdMinimumRadialCount M (2 * (n : Real)) (2 * (k : Real)) = 2 := by
        simp only [thresholdMinimumRadialCount, if_neg hNotOne, if_neg hNotThree]
      have hAd : thresholdTotalAdmissible d M (2 * (n : Real)) (2 * (k : Real)) a y := by
        simpa only [heq] using hA
      exact Exists.intro 2 (Exists.intro a (Exists.intro y (And.intro hAd (by rw [hMin]))))
  case neg =>
    have hknStrict : k < n := by omega
    have hknR : (k : Real) < (n : Real) := by exact_mod_cast hknStrict
    have hKN : 2 * (k : Real) < 2 * (n : Real) := by linarith only [hknR]
    have hNotOne : Not (And (2 * (n : Real) = 2 * (k : Real)) (M = 2 * (k : Real))) :=
      fun h => (ne_of_gt hKN) h.1
    by_cases hMK : M < 2 * (k : Real)
    case pos =>
      choose a y hA using thresholdTotal_exists_bounded d M n k hd hk hkn hRegion.1 hMK.le
      have hMin : thresholdMinimumRadialCount M (2 * (n : Real)) (2 * (k : Real)) = 3 := by
        simp only [thresholdMinimumRadialCount, if_neg hNotOne, if_pos (And.intro hMK hKN)]
      exact Exists.intro 3 (Exists.intro a (Exists.intro y (And.intro hA (by rw [hMin]))))
    case neg =>
      have hHigh := hRegion.2
      simp only [if_neg heq] at hHigh
      choose a y hA using thresholdTotal_exists_upper d M n k hd hk hkn (le_of_not_gt hMK) hHigh
      have hNotThree : Not (And (M < 2 * (k : Real)) (2 * (k : Real) < 2 * (n : Real))) := fun h => hMK h.1
      have hMin : thresholdMinimumRadialCount M (2 * (n : Real)) (2 * (k : Real)) = 2 := by
        simp only [thresholdMinimumRadialCount, if_neg hNotOne, if_neg hNotThree]
      exact Exists.intro 2 (Exists.intro a (Exists.intro y (And.intro hA (by rw [hMin]))))

theorem thresholdTotal_radius_count_feasibility (d M : Real) (n k L : Nat)
    (hd : And (0 < d) (d < 1)) (hk : 0 < k) (hkn : k <= n) :
    (exists r : Nat, exists a : Fin r -> Nat, exists y : Fin r -> Real,
      And (thresholdTotalAdmissible d M (2 * (n : Real)) (2 * (k : Real)) a y)
        ((thresholdRadialSupport Finset.univ (fun i => 2 * (a i : Real)) y).card <= L)) <->
    And (And (thresholdMinimumMass d (2 * (k : Real)) <= M)
      (if n = k then M <= 2 * (k : Real)
       else M < thresholdTotalUpper d (2 * (n : Real)) (2 * (k : Real))))
      (thresholdMinimumRadialCount M (2 * (n : Real)) (2 * (k : Real)) <= L) := by
  have hkR : (0 : Real) < (k : Real) := by exact_mod_cast hk
  have hK : 0 < 2 * (k : Real) := by linarith only [hkR]
  constructor
  case mp =>
    intro h
    choose r a y hA using h
    have hRegion := thresholdTotalAdmissible_region d M n k a y hd hk hkn hA.1
    have hMin := thresholdTotalAdmissible_minimum_card d M (2 * (n : Real)) (2 * (k : Real)) a y hd hK hA.1
    exact And.intro hRegion (le_trans hMin hA.2)
  case mpr =>
    intro h
    choose r a y hA using thresholdTotal_minimal_support_witness d M n k hd hk hkn h.1
    have hCard := thresholdRadialSupport_card_le_fin (fun i => 2 * (a i : Real)) y
    exact Exists.intro r (Exists.intro a (Exists.intro y
      (And.intro hA.1 (le_trans hCard (le_trans hA.2 h.2)))))

theorem thresholdTotal_minimum_card_attained (d M : Real) (n k : Nat)
    (hd : And (0 < d) (d < 1)) (hk : 0 < k) (hkn : k <= n)
    (hRegion : And (thresholdMinimumMass d (2 * (k : Real)) <= M)
      (if n = k then M <= 2 * (k : Real)
       else M < thresholdTotalUpper d (2 * (n : Real)) (2 * (k : Real)))) :
    exists r : Nat, exists a : Fin r -> Nat, exists y : Fin r -> Real,
      And (thresholdTotalAdmissible d M (2 * (n : Real)) (2 * (k : Real)) a y)
        ((thresholdRadialSupport Finset.univ (fun i => 2 * (a i : Real)) y).card =
          thresholdMinimumRadialCount M (2 * (n : Real)) (2 * (k : Real))) := by
  choose r a y hA using (thresholdTotal_radius_count_feasibility d M n k
    (thresholdMinimumRadialCount M (2 * (n : Real)) (2 * (k : Real))) hd hk hkn).mpr
      (And.intro hRegion le_rfl)
  have hkR : (0 : Real) < (k : Real) := by exact_mod_cast hk
  have hMin := thresholdTotalAdmissible_minimum_card d M (2 * (n : Real)) (2 * (k : Real)) a y hd
    (by linarith only [hkR]) hA.1
  exact Exists.intro r (Exists.intro a (Exists.intro y (And.intro hA.1 (le_antisymm hA.2 hMin))))

end PrimeFactorOscillations

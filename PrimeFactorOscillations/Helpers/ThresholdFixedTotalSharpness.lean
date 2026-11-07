/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.EvenDirectionalParityOptimality
import PrimeFactorOscillations.Helpers.ThresholdFixedTotalLattice
import PrimeFactorOscillations.Helpers.ThresholdNonlinearRigidity
import PrimeFactorOscillations.Helpers.ThresholdRadialMinimal

/-! # Exact fixed-total arithmetic sharpness of the positive threshold energy -/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 5000000

noncomputable section
namespace PrimeFactorOscillations

def thresholdTotalApproximable (d M N K : Real) : Prop :=
  forall eps : Real, 0 < eps -> exists r : Nat, exists a : Fin r -> Nat,
    exists y : Fin r -> Real, And (thresholdTotalAdmissible d M N K a y)
      (thresholdEvenEnergy a y < thresholdNonlinearCost d M K + eps)

theorem thresholdPositiveRoot_zero_lattice (d M : Real) (k : Nat)
    (hd : And (0 < d) (d < 1)) (hk : 0 < k) (hKM : 2 * (k : Real) <= M)
    (hLattice : M - 2 * (k : Real) * thresholdPositiveRoot d M (2 * (k : Real)) =
      2 * d * ((0 : Nat) : Real)) :
    And (M = 2 * (k : Real))
      (And (thresholdPositiveRoot d M (2 * (k : Real)) = 1)
        (thresholdNonlinearCost d M (2 * (k : Real)) = 0)) := by
  have hData := thresholdPositiveRoot_lattice_data d M k 0 hd hk hKM hLattice
  have hkR : (0 : Real) < (k : Real) := by exact_mod_cast hk
  have hzPos : 0 < thresholdPositiveRoot d M (2 * (k : Real)) := by
    linarith only [hData.1]
  have hProduct : (k : Real) * thresholdPositiveRoot d M (2 * (k : Real)) *
      (thresholdPositiveRoot d M (2 * (k : Real)) - 1) = 0 := by
    simpa only [Nat.cast_zero, zero_mul] using hData.2.2
  have hZ : thresholdPositiveRoot d M (2 * (k : Real)) = 1 := by
    have hDiff := (mul_eq_zero.mp hProduct).resolve_left (mul_ne_zero hkR.ne' hzPos.ne')
    linarith only [hDiff]
  have hMass : M = 2 * (k : Real) := by
    simpa only [hZ, Nat.cast_zero, zero_mul, add_zero, mul_one] using hData.2.1
  have hCost : thresholdNonlinearCost d M (2 * (k : Real)) = 0 := by
    simp only [thresholdNonlinearCost, if_pos hKM, thresholdPositiveCost, hZ, sub_self, mul_zero]
  exact And.intro hMass (And.intro hZ hCost)

theorem thresholdTotal_zero_lattice_exact (d M : Real) (n k : Nat)
    (hd : And (0 < d) (d < 1)) (hk : 0 < k) (hKM : 2 * (k : Real) <= M)
    (hLattice : M - 2 * (k : Real) * thresholdPositiveRoot d M (2 * (k : Real)) =
      2 * d * ((0 : Nat) : Real)) (hkn : k <= n) :
    exists a : Fin 2 -> Nat, exists y : Fin 2 -> Real,
      And (thresholdTotalAdmissible d M (2 * (n : Real)) (2 * (k : Real)) a y)
        (thresholdEvenEnergy a y = 0) := by
  have hData := thresholdPositiveRoot_zero_lattice d M k hd hk hKM hLattice
  have hBase := thresholdTotal_one_site d k hd.2
  have hPad := thresholdTotalAdmissible_pad d (2 * (k : Real)) (2 * (k : Real))
    (2 * (k : Real)) (fun _ : Fin 1 => k) (fun _ : Fin 1 => (1 : Real)) (n - k) hd.1 hBase
  have hN : 2 * ((n - k : Nat) : Real) + 2 * (k : Real) = 2 * (n : Real) := by
    rw [Nat.cast_sub hkn]
    ring
  rw [hN] at hPad
  have hPadM : thresholdTotalAdmissible d M (2 * (n : Real)) (2 * (k : Real))
      (thresholdPadWeights (n - k) (fun _ : Fin 1 => k))
      (thresholdPadCoords (fun _ : Fin 1 => (1 : Real))) := by
    rw [hData.1]
    exact hPad
  have hE : thresholdEvenEnergy (thresholdPadWeights (n - k) (fun _ : Fin 1 => k))
      (thresholdPadCoords (fun _ : Fin 1 => (1 : Real))) = 0 := by
    rw [thresholdEvenEnergy_pad]
    simp [thresholdEvenEnergy]
  exact Exists.intro _ (Exists.intro _ (And.intro hPadM hE))

theorem thresholdTotal_lattice_near_minimum (d M : Real) (n k m : Nat)
    (hd : And (0 < d) (d < 1)) (hk : 0 < k) (hKM : 2 * (k : Real) <= M)
    (hLattice : M - 2 * (k : Real) * thresholdPositiveRoot d M (2 * (k : Real)) =
      2 * d * (m : Real)) (hOrder : k + m + 1 <= n) (eps : Real) (heps : 0 < eps) :
    exists a : Fin 4 -> Nat, exists y : Fin 4 -> Real,
      And (thresholdTotalAdmissible d M (2 * (n : Real)) (2 * (k : Real)) a y)
        (thresholdEvenEnergy a y < thresholdNonlinearCost d M (2 * (k : Real)) + eps) := by
  have hkR : (0 : Real) < (k : Real) := by exact_mod_cast hk
  let z := thresholdPositiveRoot d M (2 * (k : Real))
  have hData := thresholdPositiveRoot_lattice_data d M k m hd hk hKM hLattice
  have hz : 1 <= z := hData.1
  have hMass : M = 2 * ((k : Real) * z + (m : Real) * d) := hData.2.1
  have hMoment : (k : Real) * z * (z - 1) = (m : Real) * d * (1 - d) := hData.2.2
  have hLimit : thresholdLatticeEnergy d (k : Real) (m : Real) z 0 =
      thresholdNonlinearCost d M (2 * (k : Real)) := by
    rw [thresholdLatticeEnergy_zero d (k : Real) (m : Real) z hkR (by linarith only [hz]) hMoment]
    simp only [thresholdNonlinearCost, if_pos hKM, thresholdPositiveCost]
    change 2 * ((k : Real) * z + (m : Real) * d) * (1 - d) * (z - 1) = M * (1 - d) * (z - 1)
    rw [hMass]
  choose e he using thresholdLattice_perturbation d (k : Real) (m : Real) z eps
    hd hkR (Nat.cast_nonneg _) hz heps
  let u := d - e
  let v := thresholdLatticeHigh d (k : Real) (m : Real) z e
  let w := thresholdLatticeResidual d (k : Real) (m : Real) z e
  have hu : And (0 <= u) (u < d) := by
    dsimp [u]
    constructor <;> linarith only [he.1.1, he.1.2]
  have hFirst := thresholdLattice_first_moment d (k : Real) (m : Real) z e hkR
  have hSecond := thresholdLattice_second_moment d (k : Real) (m : Real) z e hkR he.2.2.2.1.le hMoment
  rw [<- hMass] at hFirst hSecond
  have hAd := thresholdThree_admissible d M m k u v w hu he.2.2.1.le he.2.1 hd.1 hFirst hSecond
  have hTotal : Finset.sum Finset.univ (fun i => 2 * (thresholdThreeWeights m k i : Real)) =
      2 * ((k + m + 1 : Nat) : Real) := by
    rw [thresholdThree_total]
    simp only [Nat.cast_add, Nat.cast_one]
  have hBase : thresholdTotalAdmissible d M (2 * ((k + m + 1 : Nat) : Real))
      (2 * (k : Real)) (thresholdThreeWeights m k) (thresholdThreeCoords u v w) := And.intro hTotal hAd
  have hPad := thresholdTotalAdmissible_pad d M (2 * ((k + m + 1 : Nat) : Real))
    (2 * (k : Real)) (thresholdThreeWeights m k) (thresholdThreeCoords u v w)
    (n - (k + m + 1)) hd.1 hBase
  have hN : 2 * ((n - (k + m + 1) : Nat) : Real) + 2 * ((k + m + 1 : Nat) : Real) =
      2 * (n : Real) := by
    rw [Nat.cast_sub hOrder]
    ring
  rw [hN] at hPad
  have hE : thresholdEvenEnergy (thresholdThreeWeights m k) (thresholdThreeCoords u v w) <
      thresholdNonlinearCost d M (2 * (k : Real)) + eps := by
    rw [thresholdThree_energy]
    have he' := he.2.2.2.2
    rw [hLimit] at he'
    exact he'
  exact Exists.intro _ (Exists.intro _ (And.intro hPad (by rw [thresholdEvenEnergy_pad]; exact hE)))

theorem thresholdTotalAdmissible_lattice_budget {r : Nat} (d M : Real) (n k m : Nat)
    (a : Fin r -> Nat) (y : Fin r -> Real)
    (hd : And (0 < d) (d < 1)) (hk : 0 < k) (hKM : 2 * (k : Real) <= M)
    (hLattice : M - 2 * (k : Real) * thresholdPositiveRoot d M (2 * (k : Real)) =
      2 * d * (m : Real))
    (hAd : thresholdTotalAdmissible d M (2 * (n : Real)) (2 * (k : Real)) a y) :
    if m = 0 then k <= n else k + m + 1 <= n := by
  by_cases hm : m = 0
  case pos =>
    rw [if_pos hm]
    have hLe := finiteWeighted_threshold_le_total Finset.univ (fun i => 2 * (a i : Real)) y d
      (fun i _ => mul_nonneg (by norm_num : (0 : Real) <= 2) (Nat.cast_nonneg (a i)))
    rw [hAd.2.2.2.2, hAd.1] at hLe
    have hCast : (k : Real) <= (n : Real) := by linarith only [hLe]
    exact_mod_cast hCast
  case neg =>
    rw [if_neg hm]
    have hData := thresholdPositiveRoot_lattice_data d M k m hd hk hKM hLattice
    exact thresholdTotalAdmissible_lattice_order d M n k m _ a y hd hk
      (Nat.pos_of_ne_zero hm) hData.1 hData.2.1 hData.2.2 hAd

theorem thresholdTotalApproximable_iff_lattice_order (d M : Real) (n k : Nat)
    (hd : And (0 < d) (d < 1)) (hk : 0 < k) (hKM : 2 * (k : Real) <= M) :
    thresholdTotalApproximable d M (2 * (n : Real)) (2 * (k : Real)) <->
      exists m : Nat, And
        (M - 2 * (k : Real) * thresholdPositiveRoot d M (2 * (k : Real)) = 2 * d * (m : Real))
        (if m = 0 then k <= n else k + m + 1 <= n) := by
  constructor
  case mp =>
    intro hNear
    have hFree : thresholdEvenApproximable d M (2 * (k : Real)) := by
      intro eps heps
      choose r a y hA using hNear eps heps
      exact Exists.intro r (Exists.intro a (Exists.intro y (And.intro hA.1.2 hA.2)))
    choose m hm using thresholdEvenApproximable_lattice d M k hd hk hKM hFree
    choose r a y hA using hNear 1 (by norm_num)
    exact Exists.intro m (And.intro hm
      (thresholdTotalAdmissible_lattice_budget d M n k m a y hd hk hKM hm hA.1))
  case mpr =>
    intro h
    choose m hM using h
    intro eps heps
    by_cases hm : m = 0
    case pos =>
      subst m
      have hOrder : k <= n := by simpa using hM.2
      choose a y hA using thresholdTotal_zero_lattice_exact d M n k hd hk hKM hM.1 hOrder
      have hCost := (thresholdPositiveRoot_zero_lattice d M k hd hk hKM hM.1).2.2
      exact Exists.intro 2 (Exists.intro a (Exists.intro y (And.intro hA.1 (by rw [hA.2, hCost]; linarith only [heps]))))
    case neg =>
      have hOrder : k + m + 1 <= n := by simpa only [if_neg hm] using hM.2
      choose a y hA using thresholdTotal_lattice_near_minimum d M n k m hd hk hKM hM.1 hOrder eps heps
      exact Exists.intro 4 (Exists.intro a (Exists.intro y hA))

theorem thresholdTotal_lattice_feasibility_iff (d M : Real) (n k m : Nat)
    (hd : And (0 < d) (d < 1)) (hk : 0 < k) (hKM : 2 * (k : Real) <= M)
    (hLattice : M - 2 * (k : Real) * thresholdPositiveRoot d M (2 * (k : Real)) =
      2 * d * (m : Real)) :
    (exists r : Nat, exists a : Fin r -> Nat, exists y : Fin r -> Real,
      thresholdTotalAdmissible d M (2 * (n : Real)) (2 * (k : Real)) a y) <->
      (if m = 0 then k <= n else k + m + 1 <= n) := by
  constructor
  case mp =>
    intro h
    choose r a y hA using h
    exact thresholdTotalAdmissible_lattice_budget d M n k m a y hd hk hKM hLattice hA
  case mpr =>
    intro hOrder
    have hNear := (thresholdTotalApproximable_iff_lattice_order d M n k hd hk hKM).mpr
      (Exists.intro m (And.intro hLattice hOrder))
    choose r a y hA using hNear 1 (by norm_num)
    exact Exists.intro r (Exists.intro a (Exists.intro y hA.1))

theorem thresholdTotal_lattice_fixed_sharpness (d M : Real) (n k m : Nat)
    (hd : And (0 < d) (d < 1)) (hk : 0 < k) (hKM : 2 * (k : Real) <= M)
    (hLattice : M - 2 * (k : Real) * thresholdPositiveRoot d M (2 * (k : Real)) =
      2 * d * (m : Real)) :
    thresholdTotalApproximable d M (2 * (n : Real)) (2 * (k : Real)) <->
      (exists r : Nat, exists a : Fin r -> Nat, exists y : Fin r -> Real,
        thresholdTotalAdmissible d M (2 * (n : Real)) (2 * (k : Real)) a y) := by
  constructor
  case mp =>
    intro h
    choose r a y hA using h 1 (by norm_num)
    exact Exists.intro r (Exists.intro a (Exists.intro y hA.1))
  case mpr =>
    intro h
    have hOrder := (thresholdTotal_lattice_feasibility_iff d M n k m hd hk hKM hLattice).mp h
    exact (thresholdTotalApproximable_iff_lattice_order d M n k hd hk hKM).mpr
      (Exists.intro m (And.intro hLattice hOrder))

end PrimeFactorOscillations

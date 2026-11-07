/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.ThresholdLatticePerturbation

/-! # Exactly when even integral weights retain the continuous nonlinear infimum -/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 5000000

noncomputable section
namespace PrimeFactorOscillations

def thresholdEvenEnergy {n : Nat} (a : Fin n -> Nat) (y : Fin n -> Real) : Real :=
  Finset.sum Finset.univ (fun i => (2 * (a i : Real)) * y i * (y i - 1) ^ 2)

def thresholdEvenAdmissible {n : Nat} (d M K : Real) (a : Fin n -> Nat) (y : Fin n -> Real) : Prop :=
  And (forall i, 0 <= y i)
    (And (Finset.sum Finset.univ (fun i => (2 * (a i : Real)) * y i) = M)
      (And (Finset.sum Finset.univ (fun i => (2 * (a i : Real)) * (y i) ^ 2) = M)
        (thresholdSelectedMass d Finset.univ (fun i => 2 * (a i : Real)) y = K)))

def thresholdEvenApproximable (d M K : Real) : Prop :=
  forall eps : Real, 0 < eps -> exists n : Nat, exists a : Fin n -> Nat, exists y : Fin n -> Real,
    And (thresholdEvenAdmissible d M K a y)
      (thresholdEvenEnergy a y < thresholdNonlinearCost d M K + eps)

def thresholdThreeCoords (u v w : Real) (i : Fin 3) : Real :=
  if i.val = 0 then u else if i.val = 1 then v else w

def thresholdThreeWeights (m k : Nat) (i : Fin 3) : Nat :=
  if i.val = 0 then m else if i.val = 1 then k else 1

theorem thresholdBandMass_even_weights {Iota : Type*} (S : Finset Iota)
    (a : Iota -> Nat) (y : Iota -> Real) (d : Real) :
    exists m : Nat, thresholdBandMass d S (fun i => 2 * (a i : Real)) y = 2 * (m : Real) := by
  classical
  let q := fun i => if And (d / 2 <= y i) (y i < d) then a i else 0
  apply Exists.intro (Finset.sum S q)
  unfold thresholdBandMass
  rw [Nat.cast_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : And (d / 2 <= y i) (y i < d)
  case pos => simp [thresholdBandIndicator, q, h]
  case neg => simp [thresholdBandIndicator, q, h]

theorem thresholdEven_integer_lower {n : Nat} (d M K : Real) (a : Fin n -> Nat) (y : Fin n -> Real)
    (hd : And (0 < d) (d < 1)) (hM : 0 < M) (hAd : thresholdEvenAdmissible d M K a y) :
    thresholdNonlinearCost d M K + thresholdIntegerCorrection d M K <= thresholdEvenEnergy a y := by
  have hMoment : Finset.sum Finset.univ (fun i => 2 * (a i : Real) * (y i) ^ 2) =
      Finset.sum Finset.univ (fun i => 2 * (a i : Real) * y i) := hAd.2.2.1.trans hAd.2.1.symm
  have hMass : 0 < Finset.sum Finset.univ (fun i => 2 * (a i : Real) * y i) := by
    rw [hAd.2.1]
    exact hM
  have hBound := finiteWeightedThreshold_integer_cost Finset.univ (fun i => 2 * (a i : Real)) y d hd
    (fun i _ => mul_nonneg (by norm_num) (Nat.cast_nonneg _)) (fun i _ => hAd.1 i)
    hMoment hMass (thresholdBandMass_even_weights Finset.univ a y d)
  rw [hAd.2.1, hAd.2.2.2] at hBound
  exact hBound

theorem thresholdEvenApproximable_lattice (d M : Real) (k : Nat)
    (hd : And (0 < d) (d < 1)) (hk : 0 < k) (hKM : 2 * (k : Real) <= M)
    (hNear : thresholdEvenApproximable d M (2 * (k : Real))) :
    exists m : Nat, M - 2 * (k : Real) * thresholdPositiveRoot d M (2 * (k : Real)) = 2 * d * (m : Real) := by
  classical
  have hK : 0 < 2 * (k : Real) := by exact_mod_cast (show 0 < 2 * k by omega)
  have hM : 0 < M := lt_of_lt_of_le hK hKM
  by_contra hn
  have hp := (thresholdPositiveRoot_band_prediction d M (2 * (k : Real)) hd hM hK hKM).2
  have hGap := thresholdBandGap_pos d _ hd.1 hp (fun m hm => hn (Exists.intro m hm))
  have hJ := thresholdIntegerCorrection_pos d M (2 * (k : Real)) hd hM hK hKM hGap
  choose n a y had he using hNear (thresholdIntegerCorrection d M (2 * (k : Real)) / 2)
    (by linarith only [hJ])
  have hLower := thresholdEven_integer_lower d M (2 * (k : Real)) a y hd hM had
  linarith only [he, hLower, hJ]

theorem thresholdThree_sum (m k : Nat) (u v w : Real) (f : Real -> Real) :
    Finset.sum Finset.univ (fun i => (2 * (thresholdThreeWeights m k i : Real)) * f (thresholdThreeCoords u v w i)) =
      2 * (m : Real) * f u + 2 * (k : Real) * f v + 2 * f w := by
  norm_num [Fin.sum_univ_succ, thresholdThreeWeights, thresholdThreeCoords]
  <;> ring

theorem thresholdThree_energy (m k : Nat) (u v w : Real) :
    thresholdEvenEnergy (thresholdThreeWeights m k) (thresholdThreeCoords u v w) =
      2 * (m : Real) * u * (u - 1) ^ 2 + 2 * (k : Real) * v * (v - 1) ^ 2 + 2 * w * (w - 1) ^ 2 := by
  unfold thresholdEvenEnergy
  calc
    _ = Finset.sum Finset.univ (fun i => (2 * (thresholdThreeWeights m k i : Real)) *
        (thresholdThreeCoords u v w i * (thresholdThreeCoords u v w i - 1) ^ 2)) := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = _ := by rw [thresholdThree_sum m k u v w (fun q => q * (q - 1) ^ 2)]; ring

theorem thresholdThree_admissible (d M : Real) (m k : Nat) (u v w : Real)
    (hu : And (0 <= u) (u < d)) (hv : d <= v) (hw : And (0 <= w) (w < d)) (hd : 0 < d)
    (hFirst : 2 * (m : Real) * u + 2 * (k : Real) * v + 2 * w = M)
    (hSecond : 2 * (m : Real) * u ^ 2 + 2 * (k : Real) * v ^ 2 + 2 * w ^ 2 = M) :
    thresholdEvenAdmissible d M (2 * (k : Real)) (thresholdThreeWeights m k) (thresholdThreeCoords u v w) := by
  constructor
  case left =>
    intro i
    unfold thresholdThreeCoords
    split_ifs <;> linarith only [hu.1, hw.1, hv, hd]
  case right =>
    have hf : Finset.sum Finset.univ (fun i => (2 * (thresholdThreeWeights m k i : Real)) *
        thresholdThreeCoords u v w i) = M := by rw [thresholdThree_sum m k u v w (fun q => q)]; exact hFirst
    have hs : Finset.sum Finset.univ (fun i => (2 * (thresholdThreeWeights m k i : Real)) *
        (thresholdThreeCoords u v w i) ^ 2) = M := by rw [thresholdThree_sum m k u v w (fun q => q ^ 2)]; exact hSecond
    have hi : thresholdSelectedMass d Finset.univ (fun i => 2 * (thresholdThreeWeights m k i : Real))
        (thresholdThreeCoords u v w) = 2 * (k : Real) := by
      unfold thresholdSelectedMass
      rw [thresholdThree_sum m k u v w (fun q => momentRoundIndicator d q)]
      simp [momentRoundIndicator, not_le.mpr hu.2, hv, not_le.mpr hw.2]
    exact And.intro hf (And.intro hs hi)

theorem thresholdEvenApproximable_of_lattice (d M : Real) (k m : Nat)
    (hd : And (0 < d) (d < 1)) (hk : 0 < k) (hKM : 2 * (k : Real) <= M)
    (hLattice : M - 2 * (k : Real) * thresholdPositiveRoot d M (2 * (k : Real)) = 2 * d * (m : Real)) :
    thresholdEvenApproximable d M (2 * (k : Real)) := by
  have hkR : 0 < (k : Real) := by exact_mod_cast hk
  have hK : 0 < 2 * (k : Real) := mul_pos (by norm_num) hkR
  have hM : 0 < M := lt_of_lt_of_le hK hKM
  let z := thresholdPositiveRoot d M (2 * (k : Real))
  have hz := (thresholdPositiveRoot_bounds d M (2 * (k : Real)) hd hM hK hKM).2
  have hMass : M = 2 * ((k : Real) * z + (m : Real) * d) := by
    change M - 2 * (k : Real) * z = 2 * d * (m : Real) at hLattice
    nlinarith only [hLattice]
  have hr := thresholdPositiveRoot_relation d M (2 * (k : Real)) hd hM hK
  change 2 * (k : Real) * z * (z - d) = (1 - d) * M at hr
  rw [hMass] at hr
  have hMoment : (k : Real) * z * (z - 1) = (m : Real) * d * (1 - d) := by nlinarith only [hr]
  have hLimit : thresholdLatticeEnergy d (k : Real) (m : Real) z 0 = thresholdNonlinearCost d M (2 * (k : Real)) := by
    rw [thresholdLatticeEnergy_zero d (k : Real) (m : Real) z hkR (by linarith only [hz]) hMoment]
    simp only [thresholdNonlinearCost, if_pos hKM, thresholdPositiveCost]
    change 2 * ((k : Real) * z + (m : Real) * d) * (1 - d) * (z - 1) = M * (1 - d) * (z - 1)
    rw [hMass]
  intro eps heps
  choose e he using thresholdLattice_perturbation d (k : Real) (m : Real) z eps hd hkR (Nat.cast_nonneg _) hz heps
  let u := d - e
  let v := thresholdLatticeHigh d (k : Real) (m : Real) z e
  let w := thresholdLatticeResidual d (k : Real) (m : Real) z e
  have hu : And (0 <= u) (u < d) := by dsimp [u]; constructor <;> linarith only [he.1.1, he.1.2]
  have hFirst := thresholdLattice_first_moment d (k : Real) (m : Real) z e hkR
  have hSecond := thresholdLattice_second_moment d (k : Real) (m : Real) z e hkR he.2.2.2.1.le hMoment
  rw [<- hMass] at hFirst hSecond
  have hAd := thresholdThree_admissible d M m k u v w hu he.2.2.1.le he.2.1 hd.1 hFirst hSecond
  have hEnergy : thresholdEvenEnergy (thresholdThreeWeights m k) (thresholdThreeCoords u v w) <
      thresholdNonlinearCost d M (2 * (k : Real)) + eps := by
    rw [thresholdThree_energy]
    have he' := he.2.2.2.2
    rw [hLimit] at he'
    exact he'
  exact Exists.intro 3 (Exists.intro (thresholdThreeWeights m k)
    (Exists.intro (thresholdThreeCoords u v w) (And.intro hAd hEnergy)))

theorem thresholdEvenApproximable_iff_lattice (d M : Real) (k : Nat)
    (hd : And (0 < d) (d < 1)) (hk : 0 < k) (hKM : 2 * (k : Real) <= M) :
    thresholdEvenApproximable d M (2 * (k : Real)) <->
      exists m : Nat, M - 2 * (k : Real) * thresholdPositiveRoot d M (2 * (k : Real)) = 2 * d * (m : Real) := by
  constructor
  case mp => exact thresholdEvenApproximable_lattice d M k hd hk hKM
  case mpr =>
    intro h
    choose m hm using h
    exact thresholdEvenApproximable_of_lattice d M k m hd hk hKM hm

end PrimeFactorOscillations

/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.NegativeThresholdIntegerCost

/-! # Negative threshold approachability, exact attainment and the two-sided phase -/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 5000000

noncomputable section
namespace PrimeFactorOscillations

def thresholdEvenAttainable (d M K : Real) : Prop :=
  exists n : Nat, exists a : Fin n -> Nat, exists y : Fin n -> Real,
    And (thresholdEvenAdmissible d M K a y) (thresholdEvenEnergy a y = thresholdNonlinearCost d M K)

def thresholdPairCoords (u v : Real) (i : Fin 2) : Real := if i.val = 0 then u else v

def thresholdPairWeights (m n : Nat) (i : Fin 2) : Nat := if i.val = 0 then m else n

def negativeThresholdExceptionalMass (d : Real) (k l : Nat) : Real :=
  2 * ((k - l : Nat) : Real) * d + (l : Real) +
    Real.sqrt ((l : Real) ^ 2 + 4 * (l : Real) * ((k - l : Nat) : Real) * d * (1 - d))

theorem thresholdEvenAttainable_approximable (d M K : Real) (h : thresholdEvenAttainable d M K) :
    thresholdEvenApproximable d M K := by
  choose n a y ha he using h
  intro eps heps
  exact Exists.intro n (Exists.intro a (Exists.intro y (And.intro ha (by rw [he]; linarith only [heps]))))

theorem thresholdPair_sum (m n : Nat) (u v : Real) (f : Real -> Real) :
    Finset.sum Finset.univ (fun i => 2 * (thresholdPairWeights m n i : Real) * f (thresholdPairCoords u v i)) =
      2 * (m : Real) * f u + 2 * (n : Real) * f v := by
  norm_num [Fin.sum_univ_succ, thresholdPairWeights, thresholdPairCoords]

theorem thresholdEvenNegative_approximable_lattice (d M : Real) (k : Nat)
    (hd : And (0 < d) (d < 1)) (hk : 0 < k)
    (hDomain : d * (2 * (k : Real)) < M) (hMK : M < 2 * (k : Real))
    (hNear : thresholdEvenApproximable d M (2 * (k : Real))) :
    exists l : Nat, M - d * (2 * (k : Real)) =
      2 * (thresholdNegativeRoot d M (2 * (k : Real)) - d) * (l : Real) := by
  classical
  have hK : 0 < 2 * (k : Real) := by exact_mod_cast (show 0 < 2 * k by omega)
  have hM : 0 < M := lt_trans (mul_pos hd.1 hK) hDomain
  have hz := thresholdNegativeRoot_ge_one d M (2 * (k : Real)) hd.1 hDomain hMK.le
  have hg : 0 < thresholdNegativeRoot d M (2 * (k : Real)) - d := by linarith only [hz, hd.2]
  by_contra hn
  have hGap := thresholdBandGap_pos _ _ hg (sub_nonneg.mpr hDomain.le) (fun l hl => hn (Exists.intro l hl))
  have hJ := thresholdNegativeIntegerCorrection_pos d M (2 * (k : Real)) hd hK hDomain hMK hGap
  choose n a y had he using hNear (thresholdNegativeIntegerCorrection d M (2 * (k : Real)) / 2)
    (by linarith only [hJ])
  have hLower := thresholdEven_negative_lower d M (2 * (k : Real)) a y hd hM hMK had
  linarith only [he, hLower, hJ]

theorem thresholdEvenNegative_lattice_counts (d M : Real) (k l : Nat)
    (hd : And (0 < d) (d < 1)) (hk : 0 < k)
    (hDomain : d * (2 * (k : Real)) < M) (hMK : M < 2 * (k : Real))
    (hLattice : M - d * (2 * (k : Real)) =
      2 * (thresholdNegativeRoot d M (2 * (k : Real)) - d) * (l : Real)) :
    And (0 < l) (l < k) := by
  have hz := thresholdNegativeRoot_ge_one d M (2 * (k : Real)) hd.1 hDomain hMK.le
  have hg : 0 < thresholdNegativeRoot d M (2 * (k : Real)) - d := by linarith only [hz, hd.2]
  have hlR : 0 < (l : Real) := by
    by_contra h
    have hZero : (l : Real) = 0 := le_antisymm (le_of_not_gt h) (Nat.cast_nonneg l)
    rw [hZero, mul_zero] at hLattice
    linarith only [hLattice, hDomain]
  have hlK : (l : Real) < (k : Real) := by
    by_contra h
    have hKL : (k : Real) <= (l : Real) := le_of_not_gt h
    have hp := mul_nonneg (show 0 <= 2 * (thresholdNegativeRoot d M (2 * (k : Real)) - d) by linarith only [hg])
      (sub_nonneg.mpr hKL)
    have hZ := mul_nonneg (show 0 <= 2 * (k : Real) by positivity) (sub_nonneg.mpr hz)
    nlinarith only [hLattice, hp, hZ, hMK]
  exact And.intro (by exact_mod_cast hlR) (by exact_mod_cast hlK)

theorem thresholdEvenNegative_lattice_attainable (d M : Real) (k l : Nat)
    (hd : And (0 < d) (d < 1)) (hk : 0 < k)
    (hDomain : d * (2 * (k : Real)) < M) (hMK : M < 2 * (k : Real))
    (hLattice : M - d * (2 * (k : Real)) =
      2 * (thresholdNegativeRoot d M (2 * (k : Real)) - d) * (l : Real)) :
    thresholdEvenAttainable d M (2 * (k : Real)) := by
  let z := thresholdNegativeRoot d M (2 * (k : Real))
  have hz := thresholdNegativeRoot_ge_one d M (2 * (k : Real)) hd.1 hDomain hMK.le
  have hdz : d <= z := le_trans hd.2.le hz
  have hCounts := thresholdEvenNegative_lattice_counts d M k l hd hk hDomain hMK hLattice
  have hSub : ((k - l : Nat) : Real) = (k : Real) - (l : Real) := Nat.cast_sub hCounts.2.le
  have hWeights : 2 * ((k - l : Nat) : Real) + 2 * (l : Real) = 2 * (k : Real) := by rw [hSub]; ring
  have hFirst : 2 * ((k - l : Nat) : Real) * d + 2 * (l : Real) * z = M := by
    rw [hSub]
    change M - d * (2 * (k : Real)) = 2 * (z - d) * (l : Real) at hLattice
    nlinarith only [hLattice]
  have hr := thresholdNegativeRoot_relation d M (2 * (k : Real)) hDomain
  change d * z * (2 * (k : Real)) = M * (z - 1 + d) at hr
  have hFirstMul := congrArg (fun q : Real => q * (z + d)) hFirst
  have hWeightMul := congrArg (fun q : Real => q * d * z) hWeights
  have hSecond : 2 * ((k - l : Nat) : Real) * d ^ 2 + 2 * (l : Real) * z ^ 2 = M := by
    nlinarith only [hFirstMul, hWeightMul, hr]
  let a := thresholdPairWeights (k - l) l
  let y := thresholdPairCoords d z
  have hAd : thresholdEvenAdmissible d M (2 * (k : Real)) a y := by
    constructor
    case left =>
      intro i
      dsimp [y, thresholdPairCoords]
      split_ifs <;> linarith only [hd.1, hz]
    case right =>
      have hf : Finset.sum Finset.univ (fun i => 2 * (a i : Real) * y i) = M := by
        rw [thresholdPair_sum (k - l) l d z (fun q => q)]
        exact hFirst
      have hs : Finset.sum Finset.univ (fun i => 2 * (a i : Real) * (y i) ^ 2) = M := by
        rw [thresholdPair_sum (k - l) l d z (fun q => q ^ 2)]
        exact hSecond
      have hi : thresholdSelectedMass d Finset.univ (fun i => 2 * (a i : Real)) y = 2 * (k : Real) := by
        unfold thresholdSelectedMass
        rw [thresholdPair_sum (k - l) l d z (fun q => momentRoundIndicator d q)]
        simpa [momentRoundIndicator, hdz] using hWeights
      exact And.intro hf (And.intro hs hi)
  have hMoment : Finset.sum Finset.univ (fun i => 2 * (a i : Real) * (y i) ^ 2) =
      Finset.sum Finset.univ (fun i => 2 * (a i : Real) * y i) := hAd.2.2.1.trans hAd.2.1.symm
  have hFiniteDomain : d * thresholdSelectedMass d Finset.univ (fun i => 2 * (a i : Real)) y <
      Finset.sum Finset.univ (fun i => 2 * (a i : Real) * y i) := by
    rw [hAd.2.1, hAd.2.2.2]
    exact hDomain
  have hDefect := finiteWeightedThreshold_exact_negative_defect Finset.univ (fun i => 2 * (a i : Real)) y d hMoment hFiniteDomain
  rw [hAd.2.1, hAd.2.2.2] at hDefect
  have hQd : thresholdNegativePacket d z d = 0 := by
    rw [thresholdNegativePacket_selected d z d (le_refl d)]
    ring
  have hQz : thresholdNegativePacket d z z = 0 := by
    rw [thresholdNegativePacket_selected d z z hdz]
    ring
  have hSum : Finset.sum Finset.univ (fun i => 2 * (a i : Real) * thresholdNegativePacket d z (y i)) = 0 := by
    rw [thresholdPair_sum (k - l) l d z (fun q => thresholdNegativePacket d z q), hQd, hQz]
    ring
  rw [hSum] at hDefect
  have hEnergy : thresholdEvenEnergy a y = thresholdNonlinearCost d M (2 * (k : Real)) := by
    unfold thresholdNonlinearCost
    rw [if_neg (not_le.mpr hMK)]
    change 0 = thresholdEvenEnergy a y - thresholdNegativeCost d M (2 * (k : Real)) at hDefect
    linarith only [hDefect]
  exact Exists.intro 2 (Exists.intro a (Exists.intro y (And.intro hAd hEnergy)))

theorem thresholdEvenNegative_approximable_iff_lattice (d M : Real) (k : Nat)
    (hd : And (0 < d) (d < 1)) (hk : 0 < k)
    (hDomain : d * (2 * (k : Real)) < M) (hMK : M < 2 * (k : Real)) :
    thresholdEvenApproximable d M (2 * (k : Real)) <->
      exists l : Nat, M - d * (2 * (k : Real)) =
        2 * (thresholdNegativeRoot d M (2 * (k : Real)) - d) * (l : Real) := by
  constructor
  case mp => exact thresholdEvenNegative_approximable_lattice d M k hd hk hDomain hMK
  case mpr =>
    intro h
    choose l hl using h
    exact thresholdEvenAttainable_approximable d M _
      (thresholdEvenNegative_lattice_attainable d M k l hd hk hDomain hMK hl)

theorem thresholdEvenNegative_attainable_iff_lattice (d M : Real) (k : Nat)
    (hd : And (0 < d) (d < 1)) (hk : 0 < k)
    (hDomain : d * (2 * (k : Real)) < M) (hMK : M < 2 * (k : Real)) :
    thresholdEvenAttainable d M (2 * (k : Real)) <->
      exists l : Nat, M - d * (2 * (k : Real)) =
        2 * (thresholdNegativeRoot d M (2 * (k : Real)) - d) * (l : Real) := by
  constructor
  case mp =>
    intro h
    exact thresholdEvenNegative_approximable_lattice d M k hd hk hDomain hMK
      (thresholdEvenAttainable_approximable d M _ h)
  case mpr =>
    intro h
    choose l hl using h
    exact thresholdEvenNegative_lattice_attainable d M k l hd hk hDomain hMK hl

theorem thresholdEvenNegative_approximable_iff_attainable (d M : Real) (k : Nat)
    (hd : And (0 < d) (d < 1)) (hk : 0 < k)
    (hDomain : d * (2 * (k : Real)) < M) (hMK : M < 2 * (k : Real)) :
    thresholdEvenApproximable d M (2 * (k : Real)) <-> thresholdEvenAttainable d M (2 * (k : Real)) := by
  rw [thresholdEvenNegative_approximable_iff_lattice d M k hd hk hDomain hMK,
    thresholdEvenNegative_attainable_iff_lattice d M k hd hk hDomain hMK]

theorem thresholdEvenApproximable_phase (d M : Real) (k : Nat)
    (hd : And (0 < d) (d < 1)) (hk : 0 < k) (hDomain : d * (2 * (k : Real)) < M) :
    thresholdEvenApproximable d M (2 * (k : Real)) <->
      if 2 * (k : Real) <= M then
        exists m : Nat, M - 2 * (k : Real) * thresholdPositiveRoot d M (2 * (k : Real)) = 2 * d * (m : Real)
      else exists l : Nat, M - d * (2 * (k : Real)) =
        2 * (thresholdNegativeRoot d M (2 * (k : Real)) - d) * (l : Real) := by
  by_cases h : 2 * (k : Real) <= M
  case pos =>
    rw [if_pos h]
    exact thresholdEvenApproximable_iff_lattice d M k hd hk h
  case neg =>
    rw [if_neg h]
    exact thresholdEvenNegative_approximable_iff_lattice d M k hd hk hDomain (lt_of_not_ge h)

theorem thresholdEvenNegative_lattice_mass_iff (d M : Real) (k l : Nat)
    (hd : And (0 < d) (d < 1)) (hk : 0 < k)
    (hDomain : d * (2 * (k : Real)) < M) (hMK : M < 2 * (k : Real))
    (hl : And (0 < l) (l < k)) :
    (M - d * (2 * (k : Real)) = 2 * (thresholdNegativeRoot d M (2 * (k : Real)) - d) * (l : Real)) <->
      M = negativeThresholdExceptionalMass d k l := by
  let z := thresholdNegativeRoot d M (2 * (k : Real))
  have hz := thresholdNegativeRoot_ge_one d M (2 * (k : Real)) hd.1 hDomain hMK.le
  have hSub : ((k - l : Nat) : Real) = (k : Real) - (l : Real) := Nat.cast_sub hl.2.le
  have hWeights : 2 * ((k - l : Nat) : Real) + 2 * (l : Real) = 2 * (k : Real) := by rw [hSub]; ring
  constructor
  case mp =>
    intro hLattice
    have hFirst : 2 * ((k - l : Nat) : Real) * d + 2 * (l : Real) * z = M := by
      rw [hSub]
      change M - d * (2 * (k : Real)) = 2 * (z - d) * (l : Real) at hLattice
      nlinarith only [hLattice]
    have hr := thresholdNegativeRoot_relation d M (2 * (k : Real)) hDomain
    change d * z * (2 * (k : Real)) = M * (z - 1 + d) at hr
    have hFirstMul := congrArg (fun q : Real => q * (z + d)) hFirst
    have hWeightMul := congrArg (fun q : Real => q * d * z) hWeights
    have hSecond : 2 * ((k - l : Nat) : Real) * d ^ 2 + 2 * (l : Real) * z ^ 2 = M := by
      nlinarith only [hFirstMul, hWeightMul, hr]
    have hMoment : (l : Real) * z * (z - 1) = ((k - l : Nat) : Real) * d * (1 - d) := by
      nlinarith only [hFirst, hSecond]
    have hScaled := congrArg (fun q : Real => 4 * (l : Real) * q) hMoment
    have hSq : (2 * (l : Real) * z - (l : Real)) ^ 2 =
        (l : Real) ^ 2 + 4 * (l : Real) * ((k - l : Nat) : Real) * d * (1 - d) := by
      nlinarith only [hScaled]
    have hPos : 0 <= 2 * (l : Real) * z - (l : Real) := by
      have hh := mul_nonneg (Nat.cast_nonneg l) (sub_nonneg.mpr hz)
      nlinarith only [hh, (show 0 <= (l : Real) from Nat.cast_nonneg l)]
    have hRoot : Real.sqrt ((l : Real) ^ 2 + 4 * (l : Real) * ((k - l : Nat) : Real) * d * (1 - d)) =
        2 * (l : Real) * z - (l : Real) := by
      rw [<- hSq, Real.sqrt_sq_eq_abs, abs_of_nonneg hPos]
    unfold negativeThresholdExceptionalMass
    rw [hRoot]
    linarith only [hFirst]
  case mpr =>
    intro hMass
    unfold negativeThresholdExceptionalMass at hMass
    have hOne : 0 < 1 - d := sub_pos.mpr hd.2
    have hRad : 0 <= (l : Real) ^ 2 + 4 * (l : Real) * ((k - l : Nat) : Real) * d * (1 - d) := by
      exact add_nonneg (sq_nonneg _) (mul_nonneg (mul_nonneg (mul_nonneg
        (mul_nonneg (by norm_num) (Nat.cast_nonneg l)) (Nat.cast_nonneg (k - l))) hd.1.le) hOne.le)
    have hSq := Real.sq_sqrt hRad
    have hExpr : M - 2 * ((k - l : Nat) : Real) * d - (l : Real) =
        Real.sqrt ((l : Real) ^ 2 + 4 * (l : Real) * ((k - l : Nat) : Real) * d * (1 - d)) := by linarith only [hMass]
    have hPoly : (M - 2 * ((k - l : Nat) : Real) * d - (l : Real)) ^ 2 =
        (l : Real) ^ 2 + 4 * (l : Real) * ((k - l : Nat) : Real) * d * (1 - d) := by
      rw [hExpr]
      exact hSq
    have hKCast : (k : Real) = ((k - l : Nat) : Real) + (l : Real) := by rw [hSub]; ring
    have hPpoly : (M - d * (2 * (k : Real))) ^ 2 =
        2 * (l : Real) * (M * (1 - d) - d * (M - d * (2 * (k : Real)))) := by
      rw [hKCast]
      nlinarith only [hPoly]
    have hr := thresholdNegativeRoot_relation d M (2 * (k : Real)) hDomain
    change d * z * (2 * (k : Real)) = M * (z - 1 + d) at hr
    have hCross : (M - d * (2 * (k : Real))) * z = M * (1 - d) := by nlinarith only [hr]
    have hScaled := congrArg (fun q : Real => 2 * (l : Real) * q) hCross
    have hProduct : (M - d * (2 * (k : Real))) *
        (M - d * (2 * (k : Real)) - 2 * (z - d) * (l : Real)) = 0 := by
      nlinarith only [hPpoly, hScaled]
    have hZero := (mul_eq_zero.mp hProduct).resolve_left (sub_pos.mpr hDomain).ne'
    change M - d * (2 * (k : Real)) = 2 * (z - d) * (l : Real)
    linarith only [hZero]

theorem thresholdEvenNegative_approximable_iff_spectrum (d M : Real) (k : Nat)
    (hd : And (0 < d) (d < 1)) (hk : 0 < k)
    (hDomain : d * (2 * (k : Real)) < M) (hMK : M < 2 * (k : Real)) :
    thresholdEvenApproximable d M (2 * (k : Real)) <->
      exists l : Nat, And (And (0 < l) (l < k)) (M = negativeThresholdExceptionalMass d k l) := by
  rw [thresholdEvenNegative_approximable_iff_lattice d M k hd hk hDomain hMK]
  constructor
  case mp =>
    intro h
    choose l hl using h
    have hc := thresholdEvenNegative_lattice_counts d M k l hd hk hDomain hMK hl
    exact Exists.intro l (And.intro hc ((thresholdEvenNegative_lattice_mass_iff d M k l hd hk hDomain hMK hc).mp hl))
  case mpr =>
    intro h
    choose l hl using h
    exact Exists.intro l ((thresholdEvenNegative_lattice_mass_iff d M k l hd hk hDomain hMK hl.1).mpr hl.2)

end PrimeFactorOscillations

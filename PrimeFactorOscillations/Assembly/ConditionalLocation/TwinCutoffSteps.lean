/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.ConditionalLocation.LocalRatioPrefixOrder
import PrimeFactorOscillations.Helpers.OrdinaryLocalLawBridge
import PrimeFactorOscillations.Helpers.PrimeDensitySteps

/-!
# Twin Cutoff Steps

Maintained implementation of the conditional last-ascent location argument.
The arithmetic coverage assumptions remain explicit; no conjecture is an axiom.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations

theorem localRankDensity_step_gt_iff (eta : Nat -> Rat) (k i : Nat)
    (hk : 2 <= k)
    (hp : 0 < eta (PrimeFactorUnimodality.primeAt i))
    (hq : 0 < eta (PrimeFactorUnimodality.primeAt (i + 1)))
    (hden : 0 < finiteLocalMass eta
      (PrimeFactorUnimodality.primesBelow (PrimeFactorUnimodality.primeAt i)) (k - 1)) :
    localRankDensity eta k i < localRankDensity eta k (i + 1) <->
      1 / eta (PrimeFactorUnimodality.primeAt (i + 1)) -
        1 / eta (PrimeFactorUnimodality.primeAt i) + 1 <
          localPrimeRatio eta (k - 1) i := by
  have hindex : k - 2 + 1 = k - 1 := by omega
  have hsub : k - 1 - 1 = k - 2 := by omega
  have h := localStep_gt_iff eta
    (PrimeFactorUnimodality.primesBelow (PrimeFactorUnimodality.primeAt i))
    (k - 2) (PrimeFactorUnimodality.primeAt i) (PrimeFactorUnimodality.primeAt (i + 1))
    hp hq (by simpa only [hindex] using hden)
  unfold localRankDensity
  rw [finiteLocalMass_perm eta _ _
    (PrimeFactorUnimodality.primesBelow_primeAt_succ_perm i) (k - 1)]
  simpa only [localPrimeRatio, hindex, hsub] using h

theorem generic_twin_threshold_exact (p : Nat) (hp : 2 < p) :
    1 / genericOddEta (p + 2) - 1 / genericOddEta p + 1 =
      genericTwinThreshold p := by
  rw [genericOddEta_reciprocal (p + 2) (by omega), genericOddEta_reciprocal p hp]
  have hpR : (2 : Rat) < p := by exact_mod_cast hp
  have hp0 : Not ((p : Rat) = 0) := ne_of_gt (by linarith)
  have hp2 : Not ((p : Rat) - 2 = 0) := ne_of_gt (by linarith)
  simp only [genericTwinThreshold, Nat.cast_add, Nat.cast_ofNat]
  field_simp [hp0, hp2]
  ring

theorem generic_twin_threshold_le_actual (p q : Nat)
    (hp : 2 < p) (hgap : p + 2 <= q) :
    genericTwinThreshold p <= 1 / genericOddEta q - 1 / genericOddEta p + 1 := by
  have hq : 2 < q := by omega
  have hprob := genericOddEta_antitone (show 2 < p + 2 by omega) hgap
  have hinv := one_div_le_one_div_of_le (genericOddEta_pos q hq) hprob
  rw [<- generic_twin_threshold_exact p hp]
  linarith only [hinv]

theorem generic_ascent_implies_twin_potential (k i : Nat) (hk : 2 <= k)
    (hp : 2 < PrimeFactorUnimodality.primeAt i)
    (hden : 0 < finiteLocalMass genericOddEta
      (PrimeFactorUnimodality.primesBelow (PrimeFactorUnimodality.primeAt i)) (k - 1))
    (hascent : genericOddDensity k i < genericOddDensity k (i + 1)) :
    genericTwinThreshold (PrimeFactorUnimodality.primeAt i) <
      localPrimeRatio genericOddEta (k - 1) i := by
  have hgap := primeAt_gap_ge_two i hp
  have hq : 2 < PrimeFactorUnimodality.primeAt (i + 1) := by omega
  have h := (localRankDensity_step_gt_iff genericOddEta k i hk
    (genericOddEta_pos _ hp) (genericOddEta_pos _ hq) hden).mp hascent
  exact (generic_twin_threshold_le_actual _ _ hp hgap).trans_lt h

theorem generic_twin_ascent_iff (k i : Nat) (hk : 2 <= k)
    (hp : 2 < PrimeFactorUnimodality.primeAt i)
    (hden : 0 < finiteLocalMass genericOddEta
      (PrimeFactorUnimodality.primesBelow (PrimeFactorUnimodality.primeAt i)) (k - 1))
    (htwin : PrimeFactorUnimodality.primeAt (i + 1) =
      PrimeFactorUnimodality.primeAt i + 2) :
    genericOddDensity k i < genericOddDensity k (i + 1) <->
      genericTwinThreshold (PrimeFactorUnimodality.primeAt i) <
        localPrimeRatio genericOddEta (k - 1) i := by
  have hq : 2 < PrimeFactorUnimodality.primeAt (i + 1) := by omega
  have h := localRankDensity_step_gt_iff genericOddEta k i hk
    (genericOddEta_pos _ hp) (genericOddEta_pos _ hq) hden
  simpa only [htwin, generic_twin_threshold_exact _ hp, genericOddDensity] using h

theorem ordinary_ascent_implies_twin_potential (k i : Nat) (hk : 2 <= k)
    (hp : 2 < PrimeFactorUnimodality.primeAt i)
    (hden : 0 < finiteLocalMass (fun p => 1 / (p : Rat))
      (PrimeFactorUnimodality.primesBelow (PrimeFactorUnimodality.primeAt i)) (k - 1))
    (hascent : ordinaryDensity k i < ordinaryDensity k (i + 1)) :
    3 < localPrimeRatio (fun p => 1 / (p : Rat)) (k - 1) i := by
  have hgap := primeAt_gap_ge_two i hp
  have hq : 2 < PrimeFactorUnimodality.primeAt (i + 1) := by omega
  have hpR : (0 : Rat) < PrimeFactorUnimodality.primeAt i := by
    exact_mod_cast (show 0 < PrimeFactorUnimodality.primeAt i by omega)
  have hqR : (0 : Rat) < PrimeFactorUnimodality.primeAt (i + 1) := by
    exact_mod_cast (show 0 < PrimeFactorUnimodality.primeAt (i + 1) by omega)
  rw [ordinaryDensity_eq_localRankDensity, ordinaryDensity_eq_localRankDensity] at hascent
  have h := (localRankDensity_step_gt_iff (fun p => 1 / (p : Rat)) k i hk
    (div_pos (by norm_num) hpR) (div_pos (by norm_num) hqR) hden).mp hascent
  simp only [one_div_one_div] at h
  have hgapR : (PrimeFactorUnimodality.primeAt i : Rat) + 2 <=
      PrimeFactorUnimodality.primeAt (i + 1) := by exact_mod_cast hgap
  linarith only [h, hgapR]

theorem ordinary_twin_ascent_iff (k i : Nat) (hk : 2 <= k)
    (hp : 2 < PrimeFactorUnimodality.primeAt i)
    (hden : 0 < finiteLocalMass (fun p => 1 / (p : Rat))
      (PrimeFactorUnimodality.primesBelow (PrimeFactorUnimodality.primeAt i)) (k - 1))
    (htwin : PrimeFactorUnimodality.primeAt (i + 1) =
      PrimeFactorUnimodality.primeAt i + 2) :
    ordinaryDensity k i < ordinaryDensity k (i + 1) <->
      3 < localPrimeRatio (fun p => 1 / (p : Rat)) (k - 1) i := by
  have hpR : (0 : Rat) < PrimeFactorUnimodality.primeAt i := by
    exact_mod_cast (show 0 < PrimeFactorUnimodality.primeAt i by omega)
  have hqR : (0 : Rat) < PrimeFactorUnimodality.primeAt (i + 1) := by
    exact_mod_cast (show 0 < PrimeFactorUnimodality.primeAt (i + 1) by omega)
  rw [ordinaryDensity_eq_localRankDensity, ordinaryDensity_eq_localRankDensity]
  rw [localRankDensity_step_gt_iff _ k i hk
    (div_pos (by norm_num) hpR) (div_pos (by norm_num) hqR) hden]
  simp only [one_div_one_div, htwin, Nat.cast_add, Nat.cast_ofNat]
  ring_nf

end PrimeFactorOscillations

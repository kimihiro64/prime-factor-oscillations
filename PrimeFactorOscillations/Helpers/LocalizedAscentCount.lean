/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.LocalizedReversalCriterion
import PrimeFactorOscillations.Helpers.TiltedPowerExcursion

/-!
# Actual local ascent counts and the RH forward inequality

The finite grid tests real tilted-density ascents on selected distinct
actual prime pairs. The sampling premise contains only pair positions,
gap widths and count growth. Its scalar representation and RH forward
comparison retain the same rank, pairs and grid as the reference.
-/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace PrimeFactorOscillations
open Filter PrimeFactorUnimodality

def localTiltAscentSet (H M r i : Nat) : Finset Nat := by
  classical
  exact (Finset.range (H * M + 1)).filter (fun j =>
    (oddsTiltLaw (tiltGridValue M j) (tiltGridValue_pos M j)).rankDensity (r + 1) i <
      (oddsTiltLaw (tiltGridValue M j) (tiltGridValue_pos M j)).rankDensity (r + 1) (i + 1))

def localAscentCount (H : Nat) (m : Nat -> Nat)
    (a : (X : Nat) -> Fin (m X) -> Nat) (X : Nat) : Nat :=
  Finset.sum Finset.univ (fun i =>
    (localTiltAscentSet H (localTiltMesh X) (localTiltRank H X) (a X i)).card)

/-- Distinct actual pairs in a window, with a power-logarithmic-size supply. -/
def LocalAscentSampling (H : Nat) (m : Nat -> Nat)
    (a : (X : Nat) -> Fin (m X) -> Nat) : Prop :=
  (forall e : Real, 0 < e -> Filter.Eventually (fun X : Nat =>
    (X : Real) ^ (7 / 10 - e) <= (m X : Real)) atTop) /\
  Filter.Eventually (fun X : Nat => Function.Injective (a X) /\
    forall i, 2 <= primeGap (a X i) /\ primeGap (a X i) <= H /\
      (X : Real) <= ((primeAt (a X i) - 1 : Nat) : Real) /\
      ((primeAt (a X i) - 1 : Nat) : Real) <= X + (X : Real) ^ (3 / 4 : Real)) atTop

theorem localTiltAscentSet_eq_scalar (H M r i : Nat)
    (hr : 1 <= r) (hs : r <= (primesBelow (primeAt i)).length) :
    localTiltAscentSet H M r i =
      tiltAscentSet H M (densityRatio (primesBelow (primeAt i)) r : Real) (primeGap i : Real) := by
  classical
  ext j
  simp only [localTiltAscentSet, tiltAscentSet, Finset.mem_filter]
  rw [oddsTilt_rank_ascent_index_iff _ _ i r hr hs]
  simp only [tiltGridValue, add_assoc]

theorem localAscentCount_eq_scalar_eventually
    (H : Nat) (m : Nat -> Nat) (a : (X : Nat) -> Fin (m X) -> Nat)
    (hs : LocalAscentSampling H m a) :
    Filter.Eventually (fun X : Nat =>
      localAscentCount H m a X = Finset.sum Finset.univ (fun i =>
        (tiltAscentSet H (localTiltMesh X)
          (densityRatio (primesBelow (primeAt (a X i))) (localTiltRank H X) : Real)
          (primeGap (a X i) : Real)).card)) atTop := by
  let alpha : Real := (H : Real) + 2
  have ha : 0 < alpha := by dsimp [alpha]; positivity
  have hCast : Tendsto (fun n : Nat => (n : Real)) atTop atTop := tendsto_natCast_atTop_atTop
  have hBands := hCast.eventually (eventually_primeProfile_fixed_window_bands alpha ha)
  filter_upwards [hs.2, hBands, eventually_ge_atTop (1 : Nat)] with X hc hb hx
  have hx1 : (1 : Real) <= X := by exact_mod_cast hx
  have hp : (X : Real) ^ (3 / 4 : Real) <= X := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hx1
      (by norm_num : (3 / 4 : Real) <= 1)
  unfold localAscentCount
  apply Finset.sum_congr rfl
  intro i hi
  have hPair := hc.2 i
  let y : Real := ((primeAt (a X i) - 1 : Nat) : Real)
  have hy : X <= y := hPair.2.2.1
  have hB := hb.2 y hy (by dsimp [y]; linarith [hPair.2.2.2])
  have hCut : Nat.floor y + 1 = primeAt (a X i) := by
    dsimp [y]
    rw [Nat.floor_natCast, Nat.sub_add_cancel (prime_primeAt (a X i)).one_lt.le]
  rw [hCut] at hB
  rw [localTiltAscentSet_eq_scalar H (localTiltMesh X) (localTiltRank H X) (a X i) hb.1
    (weightEsymm_positive_degree_supported _ _ hB.2.2.1)]

theorem localAscentCount_le_reference_eventually_of_RH
    (H : Nat) (m : Nat -> Nat) (a : (X : Nat) -> Fin (m X) -> Nat)
    (hs : LocalAscentSampling H m a) (hRH : RiemannHypothesis) :
    Filter.Eventually (fun X : Nat => localAscentCount H m a X <=
      localReferenceCount H m a X) atTop := by
  let alpha : Real := (H : Real) + 2
  have ha : 0 < alpha := by dsimp [alpha]; positivity
  have hCast : Tendsto (fun n : Nat => (n : Real)) atTop atTop := tendsto_natCast_atTop_atTop
  have hBands := hCast.eventually (eventually_primeProfile_fixed_window_bands alpha ha)
  choose Y hY using eventually_atTop.mp
    (eventually_densityRatio_thetaClock_lt_reference_uniform_of_RH hRH
      (alpha / 3) (2 * alpha) (by linarith) (by linarith))
  filter_upwards [hs.2, hBands, localAscentCount_eq_scalar_eventually H m a hs,
    hCast.eventually (eventually_ge_atTop Y), eventually_ge_atTop (1 : Nat)]
    with X hc hb he hxY hx
  have hx1 : (1 : Real) <= X := by exact_mod_cast hx
  have hp : (X : Real) ^ (3 / 4 : Real) <= X := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hx1
      (by norm_num : (3 / 4 : Real) <= 1)
  rw [he]
  unfold localReferenceCount prescribedTiltReferenceCount
  apply Finset.sum_le_sum
  intro i hi
  have hPair := hc.2 i
  let y : Real := ((primeAt (a X i) - 1 : Nat) : Real)
  have hy : X <= y := hPair.2.2.1
  have hB := hb.2 y hy (by dsimp [y]; linarith [hPair.2.2.2])
  have hCompare := (hY y (hxY.trans hy)).2.2 (localTiltRank H X) hB.1 hB.2.1
  have hCut : Nat.floor y + 1 = primeAt (a X i) := by
    dsimp [y]
    rw [Nat.floor_natCast, Nat.sub_add_cancel (prime_primeAt (a X i)).one_lt.le]
  rw [hCut] at hCompare
  exact tiltAscentSet_card_le H (localTiltMesh X) _ _ _ hCompare.2.2.le

end PrimeFactorOscillations



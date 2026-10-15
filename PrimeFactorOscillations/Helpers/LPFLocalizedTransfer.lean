/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.LPFAnalyticStateTransfer

/-!
# Localized actual-state transfer

Position intervals remove coarse pair-profile variation before the joint
energy estimate. Every band retains both exact frontier rows and their full
7/8 error. Empty bands and nonunit output classes are included.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.LPF

def oddBand (M L U : Nat) : Finset Nat :=
  (oddInterval M).filter (fun n => L < n /\ n <= U)

def bandRow (M L U m : Nat) : Finset Nat :=
  Nat.largestPrimeFactorRow (min (4 * M - 1) U) (max M (L / m)) m

theorem filter_row_eq_bandRow (M L U m : Nat) (hm : 0 < m) :
    (Nat.largestPrimeFactorRow (4 * M - 1) M m).filter
      (fun r => L < m * r /\ m * r <= U) = bandRow M L U m := by
  ext r
  simp only [Finset.mem_filter, Nat.mem_largestPrimeFactorRow hm, bandRow,
    max_lt_iff, le_min_iff, Nat.div_lt_iff_lt_mul hm]
  simp [Nat.mul_comm, and_assoc, and_left_comm, and_comm]

theorem sum_odd_band_frontier_eq_rows (f : Nat -> Real) (M L U : Nat) (hM : 3 <= M) :
    Finset.sum ((oddBand M L U).filter (fun n => M < Nat.largestPrimeFactor n)) f =
      Finset.sum (bandRow M L U 1) f +
      Finset.sum (bandRow M L U 3) (fun r => f (3 * r)) := by
  let g : Nat -> Real := fun n => if L < n /\ n <= U then f n else 0
  have h := sum_odd_frontier_eq_rows g M hM
  have hLeft : Finset.sum ((oddInterval M).filter (fun n => M < Nat.largestPrimeFactor n)) g =
      Finset.sum ((oddBand M L U).filter (fun n => M < Nat.largestPrimeFactor n)) f := by
    simp only [oddBand, Finset.sum_filter, g]
    apply Finset.sum_congr rfl
    intro n hn
    by_cases hc : L < n /\ n <= U
    next => simp [hc]
    next => simp [hc]
  have hOne : Finset.sum (Nat.largestPrimeFactorRow (4 * M - 1) M 1) g =
      Finset.sum (bandRow M L U 1) f := by
    rw [<- filter_row_eq_bandRow M L U 1 (by decide), Finset.sum_filter]
    simp only [g, one_mul]
  have hThree : Finset.sum (Nat.largestPrimeFactorRow (4 * M - 1) M 3) (fun r => g (3 * r)) =
      Finset.sum (bandRow M L U 3) (fun r => f (3 * r)) := by
    rw [<- filter_row_eq_bandRow M L U 3 (by decide), Finset.sum_filter]
  rw [hLeft, hOne, hThree] at h
  exact h

noncomputable def bandMean (S : Finset Nat) (M Q L U : Nat) (a : ZMod Q) : Real :=
  Finset.fiberMean (oddBand M L U) (fun n => n % Q)
    (fun n => (pairWeight S n : Real)) a.val

noncomputable def bandPairEnergy (S : Finset Nat) (M Q L U : Nat) : Real :=
  Finset.sum (oddBand M L U) (fun n => ((pairWeight S n : Real) -
    Finset.fiberMean (oddBand M L U) (fun k => k % Q)
      (fun k => (pairWeight S k : Real)) (n % Q)) ^ 2)

noncomputable def bandFrontierEnergy (M Q L U : Nat) : Real :=
  Finset.sum (oddBand M L U) (fun n => (frontierIndicator M n -
    Finset.fiberMean (oddBand M L U) (fun k => k % Q)
      (frontierIndicator M) (n % Q)) ^ 2)

noncomputable def bandProjection (S : Finset Nat) (M Q L U : Nat) : Real :=
  Finset.sum (oddBand M L U) (fun n =>
    Finset.fiberMean (oddBand M L U) (fun k => k % Q)
      (fun k => (pairWeight S k : Real)) (n % Q) * frontierIndicator M n)

noncomputable def bandFrontierMass (S : Finset Nat) (M L U : Nat) : Real :=
  Finset.sum ((oddBand M L U).filter (fun n => M < Nat.largestPrimeFactor n))
    (fun n => (pairWeight S n : Real))

noncomputable def bandRowMass (S : Finset Nat) (M Q L U m : Nat) [NeZero Q] : Real :=
  Finset.sum (Finset.univ : Finset (Units (ZMod Q)))
    (fun a => bandMean S M Q L U ((m : ZMod Q) * (a : ZMod Q)))

noncomputable def bandModel (S : Finset Nat) (M Q L U : Nat) [NeZero Q] : Real :=
  ((bandRow M L U 1).card : Real) / (Q.totient : Real) * bandRowMass S M Q L U 1 +
  ((bandRow M L U 3).card : Real) / (Q.totient : Real) * bandRowMass S M Q L U 3

noncomputable def bandAnalyticError (C : Real) (S : Finset Nat)
    (M Q L U : Nat) [NeZero Q] : Real :=
  C * ((min (4 * M - 1) U : Nat) : Real) ^ (7 / 8 : Real) *
    (1 + Real.log Q + Real.log (((min (4 * M - 1) U : Nat) : Real) + 2)) ^ 2 *
    (bandRowMass S M Q L U 1 + bandRowMass S M Q L U 3)

theorem bandMean_nonneg (S : Finset Nat) (M Q L U : Nat) (a : ZMod Q) :
    0 <= bandMean S M Q L U a := by
  unfold bandMean Finset.fiberMean
  exact div_nonneg (Finset.sum_nonneg (fun n hn => Nat.cast_nonneg _)) (Nat.cast_nonneg _)

theorem band_joint_lower_bound (S : Finset Nat) (M Q L U : Nat) :
    bandProjection S M Q L U -
      Real.sqrt (bandPairEnergy S M Q L U * bandFrontierEnergy M Q L U) <=
      bandFrontierMass S M L U := by
  have h := Finset.fiber_projection_sub_covariance_le_sum_mul (oddBand M L U)
    (fun n => n % Q) (fun n => (pairWeight S n : Real)) (frontierIndicator M)
  rw [<- Finset.sum_fiberMean_mul_eq_projection] at h
  have hSum : Finset.sum (oddBand M L U)
      (fun n => (pairWeight S n : Real) * frontierIndicator M n) =
      bandFrontierMass S M L U := by
    unfold bandFrontierMass
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro n hn
    simp [frontierIndicator, mul_ite]
  rw [hSum] at h
  exact h

theorem bandFrontierMass_le_frontierCount (S : Finset Nat) (M L U : Nat)
    (hBound : forall p, Membership.mem S p -> p <= M) :
    bandFrontierMass S M L U <= (frontierCount S M : Real) := by
  have hCount : (frontierCount S M : Real) =
      Finset.sum ((Finset.Icc 1 (4 * M - 1)).filter (fun n => M < Nat.largestPrimeFactor n))
        (fun n => (pairWeight S n : Real)) := by
    exact_mod_cast frontierCount_eq_sum_pairWeight S M hBound
  rw [hCount]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  next =>
    intro n hn
    have h := Finset.mem_filter.mp hn
    have hb := Finset.mem_filter.mp h.1
    have ho := Finset.mem_filter.mp hb.1
    exact Finset.mem_filter.mpr (And.intro ho.1 h.2)
  next => intro n hn hnot; exact Nat.cast_nonneg _

theorem bandProjection_eq_rows (S : Finset Nat) (M Q L U : Nat) [NeZero Q]
    (hM : 3 <= M) :
    bandProjection S M Q L U =
      Finset.sum (bandRow M L U 1) (fun r => bandMean S M Q L U (r : ZMod Q)) +
      Finset.sum (bandRow M L U 3) (fun r => bandMean S M Q L U (3 * (r : ZMod Q))) := by
  have hEq : bandProjection S M Q L U =
      Finset.sum ((oddBand M L U).filter (fun n => M < Nat.largestPrimeFactor n))
        (fun n => bandMean S M Q L U (n : ZMod Q)) := by
    unfold bandProjection
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro n hn
    simp [bandMean, ZMod.val_natCast, frontierIndicator, mul_ite]
  rw [hEq, sum_odd_band_frontier_eq_rows _ M L U hM]
  simp only [Nat.cast_mul, Nat.cast_ofNat]

theorem exists_uniform_band_lower_bound :
    exists C : Real, And (0 < C)
      (forall {Q : Nat} [NeZero Q] (S : Finset Nat) (M L U : Nat), 3 <= M ->
        Nat.largestPrimeFactor Q <= M ->
        bandModel S M Q L U - bandAnalyticError C S M Q L U -
          Real.sqrt (bandPairEnergy S M Q L U * bandFrontierEnergy M Q L U) <=
          bandFrontierMass S M L U) := by
  let C : Real := Classical.choose exists_uniform_weighted_prime_row_lower_bound
  have hC := Classical.choose_spec exists_uniform_weighted_prime_row_lower_bound
  refine Exists.intro C (And.intro hC.1 ?_)
  intro Q inst S M L U hM hQ
  have hOne := hC.2 (min (4 * M - 1) U) (max M (L / 1)) 1 (by decide)
    (hQ.trans (le_max_left _ _))
    (fun a => bandMean S M Q L U ((1 : ZMod Q) * a))
    (fun a => bandMean_nonneg S M Q L U _)
  have hThree := hC.2 (min (4 * M - 1) U) (max M (L / 3)) 3 (by decide)
    (hQ.trans (le_max_left _ _))
    (fun a => bandMean S M Q L U ((3 : ZMod Q) * a))
    (fun a => bandMean_nonneg S M Q L U _)
  have hAnalytic : bandModel S M Q L U - bandAnalyticError C S M Q L U <=
      bandProjection S M Q L U := by
    rw [bandProjection_eq_rows S M Q L U hM]
    unfold bandModel bandAnalyticError bandRowMass bandRow
    simp only [one_mul] at hOne
    simp only [Nat.cast_one, one_mul]
    linarith
  have hJoint := band_joint_lower_bound S M Q L U
  linarith

theorem exists_uniform_localized_growth_criterion :
    exists C : Real, And (0 < C)
      (forall {Q : Nat} [NeZero Q] (S : Finset Nat) (M L U : Nat), 3 <= M ->
        Nat.largestPrimeFactor Q <= M ->
        (forall p, Membership.mem S p -> p <= M) ->
        bandAnalyticError C S M Q L U +
            Real.sqrt (bandPairEnergy S M Q L U * bandFrontierEnergy M Q L U) <
          bandModel S M Q L U ->
        Not (step S = S)) := by
  let C : Real := Classical.choose exists_uniform_band_lower_bound
  have hC := Classical.choose_spec exists_uniform_band_lower_bound
  refine Exists.intro C (And.intro hC.1 ?_)
  intro Q inst S M L U hM hQ hBound hSurplus
  have h := hC.2 S M L U hM hQ
  have hMass := bandFrontierMass_le_frontierCount S M L U hBound
  have hPos : (0 : Real) < (frontierCount S M : Real) := by linarith
  apply not_closed_of_frontierCount_pos S M hBound
  exact_mod_cast hPos

theorem oddBand_full (M : Nat) : oddBand M 0 (4 * M - 1) = oddInterval M := by
  apply Finset.filter_eq_self.mpr
  intro n hn
  have h := Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1
  exact And.intro (by omega) h.2

theorem full_band_bound_eq (C : Real) (S : Finset Nat) (M Q : Nat) [NeZero Q] :
    bandModel S M Q 0 (4 * M - 1) - bandAnalyticError C S M Q 0 (4 * M - 1) -
        Real.sqrt (bandPairEnergy S M Q 0 (4 * M - 1) *
          bandFrontierEnergy M Q 0 (4 * M - 1)) =
      modeledProjection S M Q - projectedRowError C S M Q -
        Real.sqrt (pairResidueEnergy S M Q * frontierResidueEnergy M Q) := by
  simp only [bandModel, bandRow, bandRowMass, bandMean, bandAnalyticError,
    bandPairEnergy, bandFrontierEnergy, oddBand_full, modeledProjection,
    projectedRowMass, stateResidueMean, projectedRowError, pairResidueEnergy,
    frontierResidueEnergy, min_self, Nat.zero_div, Nat.max_zero]

end PrimeFactorOscillations.LPF

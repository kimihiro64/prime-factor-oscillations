/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Tactic.Linarith
import PrimeFactorOscillations.Proof.PrimeClassDeletion.GreedyPrimeClass
import PrimeFactorOscillations.Proof.PrimeClassDeletion.PrimeRecordEnergy

/-!
# Keep exactly the primes with gap at least log p

The first gap is measured from zero. The class is selected using the
original prime sequence, independently of all previous deletion decisions.
The cap and exact headroom ledger are finite unconditional statements.
No sparse-deletion estimate is asserted.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.PrimeClassDeletion

open PrimeFactorUnimodality
open PrimeFactorOscillations.PrimeClassSampling

noncomputable def primePredecessorPosition : Nat -> Real
  | 0 => 0
  | i + 1 => (primeAt i : Real)

noncomputable def primeGapWeight (i : Nat) : Real :=
  (primeAt i : Real) - primePredecessorPosition i

noncomputable def shortGapKeptIndices (i : Nat) : Prop :=
  primeLogWeight i <= primeGapWeight i

noncomputable def shortGapKeptPrimeClass : Set Nat :=
  fun p => And (Nat.Prime p) (shortGapKeptIndices (Nat.count Nat.Prime p))

noncomputable def shortGapDeletedPrimeClass : Set Nat :=
  fun p => And (Nat.Prime p) (Not (shortGapKeptIndices (Nat.count Nat.Prime p)))

noncomputable def shortGapHeadroomCredit (i : Nat) : Real := by
  classical
  exact if shortGapKeptIndices i then primeGapWeight i - primeLogWeight i
    else primeGapWeight i

theorem classPrimeIndices_shortGapKept :
    classPrimeIndices shortGapKeptPrimeClass = shortGapKeptIndices := by
  funext i
  apply propext
  change And (Nat.Prime (primeAt i))
    (shortGapKeptIndices (Nat.count Nat.Prime (primeAt i))) <->
      shortGapKeptIndices i
  rw [primeCount_primeAt]
  exact and_iff_right (prime_primeAt i)

theorem shortGapDeletedPrimeClass_iff (p : Nat) :
    Membership.mem shortGapDeletedPrimeClass p <->
      And (Nat.Prime p)
        (primeGapWeight (Nat.count Nat.Prime p) <
          primeLogWeight (Nat.count Nat.Prime p)) := by
  change And (Nat.Prime p) (Not (_ <= _)) <-> _
  rw [not_le]

theorem primeGapWeight_nonneg (i : Nat) : 0 <= primeGapWeight i := by
  cases i with
  | zero =>
      simp only [primeGapWeight, primePredecessorPosition, sub_zero]
      exact Nat.cast_nonneg _
  | succ i =>
      exact sub_nonneg.mpr
        (Nat.cast_le.mpr (primeAt_strictMono.monotone (Nat.le_succ i)))

theorem shortGapKept_prefix_cost_le (n : Nat) :
    selectionCost shortGapKeptIndices primeLogWeight (n + 1) <=
      (primeAt n : Real) := by
  classical
  induction n with
  | zero =>
      by_cases h : shortGapKeptIndices 0
      case pos =>
        simp only [selectionCost, ite_eq_left h, zero_add]
        simpa only [shortGapKeptIndices, primeGapWeight,
          primePredecessorPosition, sub_zero] using h
      case neg =>
        simp only [selectionCost, ite_eq_right h, add_zero]
        exact Nat.cast_nonneg _
  | succ n ih =>
      by_cases h : shortGapKeptIndices (n + 1)
      case pos =>
        rw [selectionCost, ite_eq_left h]
        have hw := h
        change primeLogWeight (n + 1) <=
          (primeAt (n + 1) : Real) - (primeAt n : Real) at hw
        linarith
      case neg =>
        rw [selectionCost, ite_eq_right h, add_zero]
        exact ih.trans (Nat.cast_le.mpr (primeAt_strictMono.monotone (Nat.le_succ n)))

theorem shortGapKeptPrimeClass_theta_eq_cost (X : Nat) :
    primeClassTheta shortGapKeptPrimeClass X =
      selectionCost shortGapKeptIndices primeLogWeight (primeCutoffLength X) := by
  unfold primeClassTheta
  rw [primeClassPrefix_logSum_eq_selectionCost, classPrimeIndices_shortGapKept]

theorem shortGapKeptPrimeClass_theta_le (X : Nat) :
    primeClassTheta shortGapKeptPrimeClass X <= (X : Real) := by
  rw [shortGapKeptPrimeClass_theta_eq_cost]
  cases hN : primeCutoffLength X with
  | zero => exact Nat.cast_nonneg X
  | succ n =>
      have hp : primeAt n <= X := (primeAt_le_cutoff_iff n X).mpr (by
        rw [hN]
        exact Nat.lt_succ_self n)
      exact (shortGapKept_prefix_cost_le n).trans (Nat.cast_le.mpr hp)

theorem shortGapKeptPrimeClass_thetaReal_le (x : Real) (hx : 0 <= x) :
    primeClassThetaReal shortGapKeptPrimeClass x <= x :=
  (shortGapKeptPrimeClass_theta_le (Nat.floor x)).trans (Nat.floor_le hx)

theorem primeClockError_gap_increment (i : Nat) :
    primeClockError i - clockPreviousError primeClockError i =
      primeLogWeight i - primeGapWeight i := by
  cases i with
  | zero =>
      change (primeFullPrefixCost 1 - (primeAt 0 : Real)) - 0 =
        primeLogWeight 0 - ((primeAt 0 : Real) - 0)
      rw [primeFullPrefixCost_succ]
      change (0 + primeLogWeight 0 - (primeAt 0 : Real)) - 0 = _
      ring
  | succ i =>
      simp only [primeClockError, clockPreviousError, primeFullPrefixCost_succ,
        primeGapWeight, primePredecessorPosition]
      ring

theorem shortGapKeptIndices_iff_original_wave (i : Nat) :
    shortGapKeptIndices i <->
      primeClockError i <= clockPreviousError primeClockError i := by
  have h := primeClockError_gap_increment i
  unfold shortGapKeptIndices
  constructor <;> intro hi <;> linarith

/-- Every gap appears, including the full gap preceding each deleted prime. -/
theorem shortGapKept_headroom_ledger (n : Nat) :
    primePredecessorPosition n - selectionCost shortGapKeptIndices primeLogWeight n =
      (Finset.range n).sum shortGapHeadroomCredit := by
  classical
  induction n with
  | zero => simp [primePredecessorPosition, selectionCost]
  | succ n ih =>
      rw [Finset.sum_range_succ, <- ih, selectionCost]
      by_cases h : shortGapKeptIndices n
      all_goals simp only [shortGapHeadroomCredit, h, ite_true, ite_false]
      all_goals simp only [primeGapWeight, primePredecessorPosition]
      all_goals ring

theorem shortGapKept_headroom_summands_nonneg (i : Nat) :
    0 <= shortGapHeadroomCredit i := by
  classical
  unfold shortGapHeadroomCredit
  split_ifs with h
  case pos => exact sub_nonneg.mpr h
  case neg => exact primeGapWeight_nonneg i

theorem greedy_deleted_count_le_shortGap (X : Nat) :
    (primeClassPrefix greedyDeletedPrimeClass X).card <=
      (primeClassPrefix shortGapDeletedPrimeClass X).card := by
  have h := greedyDeletedPrimeClass_count_optimal shortGapKeptPrimeClass
    shortGapKeptPrimeClass_theta_le X
  have hprefix :
      primeClassPrefix (fun p => Not (Membership.mem shortGapKeptPrimeClass p)) X =
        primeClassPrefix shortGapDeletedPrimeClass X := by
    apply Finset.ext
    intro p
    simp only [primeClassPrefix, Finset.mem_filter]
    change (And (Membership.mem (Finset.Icc 2 X) p)
      (And (Nat.Prime p) (Not (And (Nat.Prime p)
        (shortGapKeptIndices (Nat.count Nat.Prime p)))))) <->
      (And (Membership.mem (Finset.Icc 2 X) p)
        (And (Nat.Prime p) (And (Nat.Prime p)
          (Not (shortGapKeptIndices (Nat.count Nat.Prime p))))))
    tauto
  rw [hprefix] at h
  exact h

end PrimeFactorOscillations.PrimeClassDeletion

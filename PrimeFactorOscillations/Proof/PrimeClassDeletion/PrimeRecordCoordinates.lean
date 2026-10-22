/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Proof.PrimeClassDeletion.CappedPrimeWeights
import PrimeFactorOscillations.Proof.PrimeClassDeletion.ClockRecordEnergy
import PrimeFactorOscillations.Proof.PrimeClassDeletion.GreedyPrimeRealCutoffs

/-! # Actual prime coordinates of the retained record energy

The jump sums and quadratic variation are over the literal finite prime
support. At a prime p the jump is exactly R(p)-R(p-1). Nonprime values of
the coordinate map are not inserted into any prime sum.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.PrimeClassDeletion

open PrimeFactorUnimodality
open PrimeFactorOscillations.PrimeClassSampling

theorem primeFullPrefix_sum_eq_index (f : Nat -> Real) (X : Nat) :
    (primeClassPrefix Set.univ X).sum f =
      (Finset.range (primeCutoffLength X)).sum (fun i => f (primeAt i)) := by
  classical
  rw [primeClassPrefix_eq_indexImage]
  rw [Finset.sum_image (fun i _ j _ hij => primeAt_strictMono.injective hij)]
  have hset : selectionPrefix (classPrimeIndices Set.univ) (primeCutoffLength X) =
      Finset.range (primeCutoffLength X) := by
    ext i
    simp only [selectionPrefix, Finset.mem_filter, classPrimeIndices, Set.mem_univ, and_true]
  rw [hset]

noncomputable def primeRecordJump (p : Nat) : Real :=
  clockRecordIncrement primeClockError (Nat.count Nat.Prime p)

theorem primeRecordJump_nonneg (p : Nat) : 0 <= primeRecordJump p :=
  clockRecordIncrement_nonneg primeClockError (Nat.count Nat.Prime p)

theorem primeRecordJump_le_log (p : Nat) (hp : Nat.Prime p) :
    primeRecordJump p <= Real.log (p : Real) := by
  have h := clockRecordIncrement_le_of_clock primeClockError primeLogWeight
    primeLogWeight_nonneg primeClockError_initial primeClockError_increment
    (Nat.count Nat.Prime p)
  simpa only [primeRecordJump, primeLogWeight, primeAt_count_prime p hp] using h

theorem primeRecordJump_eq_regulator_sub (p : Nat) (hp : Nat.Prime p) :
    primeRecordJump p = greedyPrimeRegulator p - greedyPrimeRegulator (p - 1) := by
  let i := Nat.count Nat.Prime p
  have hN : primeCutoffLength p = i + 1 := by
    have h := Nat.count_nth_succ_of_infinite Nat.infinite_setOfPred_prime i
    change primeCutoffLength (primeAt i) = i + 1 at h
    rw [show primeAt i = p from primeAt_count_prime p hp] at h
    exact h
  have hB : primeCutoffLength (p - 1) = i := by
    unfold primeCutoffLength
    rw [Nat.sub_add_cancel hp.one_lt.le]
  simp only [primeRecordJump, clockRecordIncrement, greedyPrimeRegulator, hN, hB, i]

theorem primeRecordJump_sum (x : Real) :
    (primeClassPrefix Set.univ (Nat.floor x)).sum primeRecordJump =
      greedyPrimeRegulatorReal x := by
  rw [primeFullPrefix_sum_eq_index]
  simpa only [primeRecordJump, primeCount_primeAt, greedyPrimeRegulatorReal,
    greedyPrimeRegulator] using clockRecordIncrement_sum primeClockError
      (primeCutoffLength (Nat.floor x))

noncomputable def primeRecordQuadraticVariation (x : Real) : Real :=
  (primeClassPrefix Set.univ (Nat.floor x)).sum (fun p => (primeRecordJump p) ^ 2)

theorem primeRecordQuadraticVariation_eq_clock (x : Real) :
    primeRecordQuadraticVariation x =
      clockRecordQuadraticVariation primeClockError (primeCutoffLength (Nat.floor x)) := by
  rw [primeRecordQuadraticVariation, primeFullPrefix_sum_eq_index]
  simp only [primeRecordJump, primeCount_primeAt, clockRecordQuadraticVariation]

theorem primeRecordQuadraticVariation_bounds (x : Real) (hx : 2 <= x) :
    And (0 <= primeRecordQuadraticVariation x)
      (primeRecordQuadraticVariation x <= greedyPrimeRegulatorReal x * Real.log x) := by
  rw [primeRecordQuadraticVariation_eq_clock]
  refine And.intro (clockRecordQuadraticVariation_nonneg _ _) ?_
  have hW : forall i : Nat, i < primeCutoffLength (Nat.floor x) ->
      clockRecordIncrement primeClockError i <= Real.log x := by
    intro i hi
    have hp : primeAt i <= Nat.floor x := (primeAt_le_cutoff_iff i (Nat.floor x)).mpr hi
    have hpR : (primeAt i : Real) <= x :=
      (Nat.cast_le.mpr hp).trans (Nat.floor_le (by linarith only [hx]))
    have hlog : primeLogWeight i <= Real.log x :=
      Real.log_le_log (Nat.cast_pos.mpr (prime_primeAt i).pos) hpR
    exact (clockRecordIncrement_le_of_clock primeClockError primeLogWeight
      primeLogWeight_nonneg primeClockError_initial primeClockError_increment i).trans hlog
  have h := clockRecordQuadraticVariation_le primeClockError
    (primeCutoffLength (Nat.floor x)) (Real.log x) hW
  simpa only [greedyPrimeRegulatorReal, greedyPrimeRegulator, mul_comm] using h

theorem primeClockError_increment_eq (n : Nat) :
    primeClockError (n + 1) - primeClockError n =
      primeLogWeight (n + 1) -
        ((primeAt (n + 1) : Real) - (primeAt n : Real)) := by
  unfold primeClockError
  rw [primeFullPrefixCost_succ (n + 1)]
  ring

end PrimeFactorOscillations.PrimeClassDeletion

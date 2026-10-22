/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Proof.PrimeClassDeletion.ClockRecordProduct
import PrimeFactorOscillations.Proof.PrimeClassDeletion.PrimeRecordIntegral

/-! # Full actual signed prime-record energy

The prime supply and the actual ordinary integral remain coupled.
The terminal correction is retained at every real cutoff and vanishes
only under the stated record condition. These are exact identities,
not an independent estimate for the signed energy.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.PrimeClassDeletion

open PrimeFactorUnimodality
open PrimeFactorOscillations.PrimeClassSampling

noncomputable def primeRecordPrimeSupply (x : Real) : Real :=
  (primeClassPrefix Set.univ (Nat.floor x)).sum
    (fun p => greedyPrimeRegulator (p - 1) * Real.log (p : Real))

noncomputable def primeRecordPositionJumps (x : Real) : Real :=
  (primeClassPrefix Set.univ (Nat.floor x)).sum
    (fun p => (p : Real) * primeRecordJump p)

noncomputable def primeRecordSignedEnergy (x : Real) : Real :=
  primeRecordPrimeSupply x -
    intervalIntegral greedyPrimeRegulatorReal 2 x MeasureTheory.volume

theorem greedyPrimeRegulator_before_primeAt (i : Nat) :
    greedyPrimeRegulator (primeAt i - 1) = clockRecord primeClockError i := by
  unfold greedyPrimeRegulator primeCutoffLength
  rw [Nat.sub_add_cancel (prime_primeAt i).one_lt.le, primeCount_primeAt]

theorem primeRecordPrimeSupply_eq_index (x : Real) :
    primeRecordPrimeSupply x =
      (Finset.range (primeCutoffLength (Nat.floor x))).sum
        (fun i => clockRecord primeClockError i * primeLogWeight i) := by
  rw [primeRecordPrimeSupply, primeFullPrefix_sum_eq_index]
  apply Finset.sum_congr rfl
  intro i _
  rw [greedyPrimeRegulator_before_primeAt]
  rfl

theorem primeRecordPositionJumps_eq_index (x : Real) :
    primeRecordPositionJumps x =
      (Finset.range (primeCutoffLength (Nat.floor x))).sum
        (fun i => (primeAt i : Real) * clockRecordIncrement primeClockError i) := by
  rw [primeRecordPositionJumps, primeFullPrefix_sum_eq_index]
  simp only [primeRecordJump, primeCount_primeAt]

theorem primeClassTheta_univ_eq_fullCost (X : Nat) :
    primeClassTheta Set.univ X = primeFullPrefixCost (primeCutoffLength X) := by
  unfold primeClassTheta
  rw [primeClassPrefix_logSum_eq_selectionCost]
  rfl

theorem primeRecord_product_ledger (x : Real) :
    greedyPrimeRegulatorReal x * primeClassThetaReal Set.univ x =
      primeRecordPrimeSupply x + primeRecordPositionJumps x +
        (Finset.range (primeCutoffLength (Nat.floor x))).sum
          (fun i => clockRecord primeClockError (i + 1) *
            clockRecordIncrement primeClockError i) := by
  let n := primeCutoffLength (Nat.floor x)
  have hsupply :
      (Finset.range n).sum
        (fun i => clockRecord primeClockError i *
          (primeFullPrefixCost (i + 1) - primeFullPrefixCost i)) =
        primeRecordPrimeSupply x := by
    rw [primeRecordPrimeSupply_eq_index]
    apply Finset.sum_congr rfl
    intro i _
    rw [primeFullPrefixCost_succ]
    ring
  have hsecond :
      (Finset.range n).sum
        (fun i => primeFullPrefixCost (i + 1) * clockRecordIncrement primeClockError i) =
      primeRecordPositionJumps x +
        (Finset.range n).sum
          (fun i => clockRecord primeClockError (i + 1) *
            clockRecordIncrement primeClockError i) := by
    rw [primeRecordPositionJumps_eq_index, <- Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    have hcomp := clockRecordIncrement_complementarity primeClockError i
    have heq : primeClockError i =
        primeFullPrefixCost (i + 1) - (primeAt i : Real) := rfl
    rw [heq] at hcomp
    nlinarith only [hcomp]
  have h := clockRecord_product_ledger primeClockError primeFullPrefixCost n
  rw [hsupply, hsecond] at h
  simpa only [greedyPrimeRegulatorReal, greedyPrimeRegulator, primeClassThetaReal,
    primeClassTheta_univ_eq_fullCost, add_assoc, n] using h

theorem greedyPrimeRegulatorReal_integral_signed (x : Real) (hx : 2 <= x) :
    intervalIntegral greedyPrimeRegulatorReal 2 x MeasureTheory.volume =
      x * greedyPrimeRegulatorReal x - primeRecordPositionJumps x := by
  classical
  calc
    intervalIntegral greedyPrimeRegulatorReal 2 x MeasureTheory.volume =
        (primeClassPrefix Set.univ (Nat.floor x)).sum
          (fun p => x * primeRecordJump p - (p : Real) * primeRecordJump p) := by
      rw [greedyPrimeRegulatorReal_integral x hx]
      apply Finset.sum_congr rfl
      intro p _
      ring
    _ = _ := by
      rw [Finset.sum_sub_distrib, <- Finset.mul_sum, primeRecordJump_sum]
      rfl

theorem primeRecordEnergy_identity (x : Real) (hx : 2 <= x) :
    (greedyPrimeRegulatorReal x) ^ 2 = 2 * primeRecordSignedEnergy x +
      2 * greedyPrimeRegulatorReal x *
        (greedyPrimeRegulatorReal x - (primeClassThetaReal Set.univ x - x)) +
          primeRecordQuadraticVariation x := by
  have hproduct := primeRecord_product_ledger x
  have hintegral := greedyPrimeRegulatorReal_integral_signed x hx
  have hjump := clockRecord_right_jump_energy primeClockError
    (primeCutoffLength (Nat.floor x))
  have hjump' :
      2 * (Finset.range (primeCutoffLength (Nat.floor x))).sum
          (fun i => clockRecord primeClockError (i + 1) *
            clockRecordIncrement primeClockError i) =
        (greedyPrimeRegulatorReal x) ^ 2 + primeRecordQuadraticVariation x := by
    simpa only [greedyPrimeRegulatorReal, greedyPrimeRegulator,
      primeRecordQuadraticVariation_eq_clock] using hjump
  unfold primeRecordSignedEnergy
  nlinarith only [hproduct, hintegral, hjump']

theorem primeRecordEnergy_at_record (x : Real) (hx : 2 <= x)
    (hrecord : greedyPrimeRegulatorReal x = primeClassThetaReal Set.univ x - x) :
    And ((greedyPrimeRegulatorReal x) ^ 2 =
      2 * primeRecordSignedEnergy x + primeRecordQuadraticVariation x)
      (And (0 <= primeRecordQuadraticVariation x)
        (primeRecordQuadraticVariation x <= greedyPrimeRegulatorReal x * Real.log x)) := by
  refine And.intro ?_ (primeRecordQuadraticVariation_bounds x hx)
  have h := primeRecordEnergy_identity x hx
  rw [<- hrecord] at h
  simpa only [sub_self, mul_zero, add_zero] using h

theorem greedyPrimeRegulator_at_primeAt (i : Nat) :
    greedyPrimeRegulator (primeAt i) = clockRecord primeClockError (i + 1) := by
  have h : primeCutoffLength (primeAt i) = i + 1 :=
    Nat.count_nth_succ_of_infinite Nat.infinite_setOfPred_prime i
  simp only [greedyPrimeRegulator, h]

theorem primeRecordRightJump_sum (x : Real) :
    (primeClassPrefix Set.univ (Nat.floor x)).sum
        (fun p => greedyPrimeRegulator p * primeRecordJump p) =
      (Finset.range (primeCutoffLength (Nat.floor x))).sum
        (fun i => clockRecord primeClockError (i + 1) *
          clockRecordIncrement primeClockError i) := by
  rw [primeFullPrefix_sum_eq_index]
  simp only [greedyPrimeRegulator_at_primeAt, primeRecordJump, primeCount_primeAt]

theorem primeRecord_error_product (x : Real) (hx : 2 <= x) :
    greedyPrimeRegulatorReal x * (primeClassThetaReal Set.univ x - x) =
      primeRecordSignedEnergy x +
        (primeClassPrefix Set.univ (Nat.floor x)).sum
          (fun p => greedyPrimeRegulator p * primeRecordJump p) := by
  rw [primeRecordRightJump_sum]
  have hproduct := primeRecord_product_ledger x
  have hintegral := greedyPrimeRegulatorReal_integral_signed x hx
  unfold primeRecordSignedEnergy
  nlinarith only [hproduct, hintegral]

theorem primeRecord_jump_energy (x : Real) :
    2 * (primeClassPrefix Set.univ (Nat.floor x)).sum
        (fun p => greedyPrimeRegulator p * primeRecordJump p) =
      (greedyPrimeRegulatorReal x) ^ 2 + primeRecordQuadraticVariation x := by
  rw [primeRecordRightJump_sum]
  simpa only [greedyPrimeRegulatorReal, greedyPrimeRegulator,
    primeRecordQuadraticVariation_eq_clock] using
      clockRecord_right_jump_energy primeClockError (primeCutoffLength (Nat.floor x))

end PrimeFactorOscillations.PrimeClassDeletion

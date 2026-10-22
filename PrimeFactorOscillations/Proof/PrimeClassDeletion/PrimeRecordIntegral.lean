/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Proof.PrimeClassDeletion.PrimeRecordCoordinates
import PrimeFactorOscillations.Proof.PrimeClassDeletion.RecordStepIntegral

/-! # The actual real-cutoff record integral

The fixed upper prime support is filtered at the running real coordinate.
The exact jump representation holds at prime endpoints as well, and the
ordinary integral is evaluated without changing the retained regulator.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.PrimeClassDeletion

open PrimeFactorOscillations.PrimeClassSampling

theorem primeClassPrefix_mem_iff (P : Set Nat) (X p : Nat) :
    Membership.mem (primeClassPrefix P X) p <->
      And (2 <= p) (And (p <= X) (And (Nat.Prime p) (Membership.mem P p))) := by
  classical
  simp only [primeClassPrefix, Finset.mem_filter, Finset.mem_Icc, and_assoc]

theorem primeFullPrefix_filter_real (x t : Real) (ht : 0 <= t) (htx : t <= x) :
    primeClassPrefix Set.univ (Nat.floor t) =
      (primeClassPrefix Set.univ (Nat.floor x)).filter (fun p : Nat => (p : Real) <= t) := by
  classical
  ext p
  constructor
  case mp =>
    intro hp
    have hm := (primeClassPrefix_mem_iff Set.univ (Nat.floor t) p).mp hp
    have hpt : (p : Real) <= t := (Nat.cast_le.mpr hm.2.1).trans (Nat.floor_le ht)
    have hpx : p <= Nat.floor x := Nat.le_floor (hpt.trans htx)
    exact Finset.mem_filter.mpr (And.intro
      ((primeClassPrefix_mem_iff Set.univ (Nat.floor x) p).mpr
        (And.intro hm.1 (And.intro hpx hm.2.2))) hpt)
  case mpr =>
    intro hp
    have hout := Finset.mem_filter.mp hp
    have hm := (primeClassPrefix_mem_iff Set.univ (Nat.floor x) p).mp hout.1
    have hpt : p <= Nat.floor t := Nat.le_floor hout.2
    exact (primeClassPrefix_mem_iff Set.univ (Nat.floor t) p).mpr
      (And.intro hm.1 (And.intro hpt hm.2.2))

theorem greedyPrimeRegulatorReal_eq_jump_steps (x t : Real)
    (ht : 0 <= t) (htx : t <= x) :
    greedyPrimeRegulatorReal t =
      (primeClassPrefix Set.univ (Nat.floor x)).sum
        (fun p => recordRightStep (p : Real) (primeRecordJump p) t) := by
  classical
  rw [<- primeRecordJump_sum t, primeFullPrefix_filter_real x t ht htx,
    Finset.sum_filter]
  simp only [recordRightStep]

theorem greedyPrimeRegulatorReal_intervalIntegrable (x : Real) (hx : 2 <= x) :
    IntervalIntegrable greedyPrimeRegulatorReal MeasureTheory.volume 2 x := by
  classical
  have hsum : forall S : Finset Nat,
      IntervalIntegrable
        (fun t => S.sum (fun p => recordRightStep (p : Real) (primeRecordJump p) t))
        MeasureTheory.volume 2 x := by
    intro S
    induction S using Finset.induction with
    | empty => simpa only [Finset.sum_empty] using
        (intervalIntegrable_const (c := (0 : Real)))
    | @insert p S hp ih =>
        simpa only [Finset.sum_insert hp] using
          (recordRightStep_intervalIntegrable (p : Real) (primeRecordJump p) 2 x).add ih
  apply IntervalIntegrable.congr _ (hsum (primeClassPrefix Set.univ (Nat.floor x)))
  intro t ht
  have hinterval : Membership.mem (Set.Ioc (2 : Real) x) t := by
    simpa only [Set.uIoc_of_le hx] using ht
  exact (greedyPrimeRegulatorReal_eq_jump_steps x t
    (by linarith only [hinterval.1]) hinterval.2).symm

theorem greedyPrimeRegulatorReal_integral (x : Real) (hx : 2 <= x) :
    intervalIntegral greedyPrimeRegulatorReal 2 x MeasureTheory.volume =
      (primeClassPrefix Set.univ (Nat.floor x)).sum
        (fun p => primeRecordJump p * (x - (p : Real))) := by
  classical
  calc
    intervalIntegral greedyPrimeRegulatorReal 2 x MeasureTheory.volume =
        intervalIntegral
          (fun t => (primeClassPrefix Set.univ (Nat.floor x)).sum
            (fun p => recordRightStep (p : Real) (primeRecordJump p) t))
          2 x MeasureTheory.volume := by
      apply intervalIntegral.integral_congr
      intro t ht
      have hinterval : Membership.mem (Set.Icc (2 : Real) x) t := by
        simpa only [Set.uIcc_of_le hx] using ht
      exact greedyPrimeRegulatorReal_eq_jump_steps x t
        (by linarith only [hinterval.1]) hinterval.2
    _ = _ := by
      apply recordRightStep_sum_integral
      intro p hp
      have hm := (primeClassPrefix_mem_iff Set.univ (Nat.floor x) p).mp hp
      exact And.intro (Nat.cast_le.mpr hm.1)
        ((Nat.cast_le.mpr hm.2.1).trans (Nat.floor_le (by linarith only [hx])))

end PrimeFactorOscillations.PrimeClassDeletion

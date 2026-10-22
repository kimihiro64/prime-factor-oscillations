/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Proof.PrimeClassDeletion.PrimeClassAbelKernel

/-!
# Exact partial summation for every actual prime class

The finite support consists of the actual class primes up to the fixed
upper cutoff. Both real endpoints, including the first prime two, are
retained throughout the pointwise identities and ordinary integrals.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.PrimeClassDeletion

open PrimeFactorOscillations.PrimeClassSampling

theorem primeClassPrefix_filter_real (P : Set Nat) (x t : Real)
    (ht : 0 <= t) (htx : t <= x) :
    primeClassPrefix P (Nat.floor t) =
      (primeClassPrefix P (Nat.floor x)).filter (fun p : Nat => (p : Real) <= t) := by
  classical
  ext p
  constructor
  case mp =>
    intro hp
    have hm := (primeClassPrefix_mem_iff P (Nat.floor t) p).mp hp
    have hpt : (p : Real) <= t := (Nat.cast_le.mpr hm.2.1).trans (Nat.floor_le ht)
    have hpx : p <= Nat.floor x := Nat.le_floor (hpt.trans htx)
    exact Finset.mem_filter.mpr (And.intro
      ((primeClassPrefix_mem_iff P (Nat.floor x) p).mpr
        (And.intro hm.1 (And.intro hpx hm.2.2))) hpt)
  case mpr =>
    intro hp
    have hout := Finset.mem_filter.mp hp
    have hm := (primeClassPrefix_mem_iff P (Nat.floor x) p).mp hout.1
    have hpt : p <= Nat.floor t := Nat.le_floor hout.2
    exact (primeClassPrefix_mem_iff P (Nat.floor t) p).mpr
      (And.intro hm.1 (And.intro hpt hm.2.2))

theorem primeClassThetaReal_abel_steps (P : Set Nat) (x t : Real)
    (ht : 0 <= t) (htx : t <= x) :
    primeClassThetaReal P t / (t * (Real.log t) ^ 2) =
      (primeClassPrefix P (Nat.floor x)).sum (fun p =>
        (Set.Ici (p : Real)).indicator (fun u => Real.log (p : Real) * primeClassAbelKernel u) t) := by
  classical
  rw [primeClassThetaReal, primeClassTheta, primeClassPrefix_filter_real P x t ht htx,
    Finset.sum_filter, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro p _
  by_cases hp : (p : Real) <= t
  all_goals simp only [Set.indicator, Set.mem_Ici, hp, ite_true, ite_false,
    primeClassAbelKernel, div_eq_mul_inv, one_mul, zero_mul]

theorem primeClassAbel_step_intervalIntegrable (p : Nat) (x : Real) (hx : 2 <= x) :
    IntervalIntegrable
      ((Set.Ici (p : Real)).indicator (fun t => Real.log (p : Real) * primeClassAbelKernel t))
      MeasureTheory.volume 2 x := by
  have h := (primeClassAbelKernel_intervalIntegrable 2 x (le_refl _) hx).const_mul
    (Real.log (p : Real))
  exact And.intro (h.1.indicator measurableSet_Ici) (h.2.indicator measurableSet_Ici)

theorem primeClassAbel_intervalIntegrable (P : Set Nat) (x : Real) (hx : 2 <= x) :
    IntervalIntegrable (fun t => primeClassThetaReal P t / (t * (Real.log t) ^ 2))
      MeasureTheory.volume 2 x := by
  classical
  have hsum : forall S : Finset Nat,
      IntervalIntegrable (fun t => S.sum (fun p => (Set.Ici (p : Real)).indicator
        (fun u => Real.log (p : Real) * primeClassAbelKernel u) t))
        MeasureTheory.volume 2 x := by
    intro S
    induction S using Finset.induction with
    | empty => simpa only [Finset.sum_empty] using
        (intervalIntegrable_const (c := (0 : Real)))
    | @insert p S hp ih =>
        simpa only [Finset.sum_insert hp] using
          (primeClassAbel_step_intervalIntegrable p x hx).add ih
  apply IntervalIntegrable.congr _ (hsum (primeClassPrefix P (Nat.floor x)))
  intro t ht
  have hinterval : Membership.mem (Set.Ioc (2 : Real) x) t := by
    simpa only [Set.uIoc_of_le hx] using ht
  exact (primeClassThetaReal_abel_steps P x t
    (by linarith only [hinterval.1]) hinterval.2).symm

theorem primeClassAbel_integral (P : Set Nat) (x : Real) (hx : 2 <= x) :
    intervalIntegral (fun t => primeClassThetaReal P t / (t * (Real.log t) ^ 2))
        2 x MeasureTheory.volume =
      (primeClassPrefix P (Nat.floor x)).sum
        (fun p => Real.log (p : Real) * (1 / Real.log (p : Real) - 1 / Real.log x)) := by
  classical
  calc
    _ = intervalIntegral (fun t => (primeClassPrefix P (Nat.floor x)).sum
          (fun p => (Set.Ici (p : Real)).indicator
            (fun u => Real.log (p : Real) * primeClassAbelKernel u) t))
        2 x MeasureTheory.volume := by
      apply intervalIntegral.integral_congr
      intro t ht
      have hinterval : Membership.mem (Set.Icc (2 : Real) x) t := by
        simpa only [Set.uIcc_of_le hx] using ht
      exact primeClassThetaReal_abel_steps P x t
        (by linarith only [hinterval.1]) hinterval.2
    _ = _ := by
      rw [intervalIntegral.integral_finsetSum
        (fun p _ => primeClassAbel_step_intervalIntegrable p x hx)]
      apply Finset.sum_congr rfl
      intro p hp
      have hm := (primeClassPrefix_mem_iff P (Nat.floor x) p).mp hp
      have hp2 : (2 : Real) <= (p : Real) := Nat.cast_le.mpr hm.1
      have hpx : (p : Real) <= x :=
        (Nat.cast_le.mpr hm.2.1).trans (Nat.floor_le (by linarith only [hx]))
      rw [rightCutoff_integral _ (p : Real) 2 x hp2 hpx,
        intervalIntegral.integral_const_mul, primeClassAbelKernel_integral (p : Real) x hp2 hpx]

theorem primeClassCount_abel (P : Set Nat) (x : Real) (hx : 2 <= x) :
    ((primeClassPrefix P (Nat.floor x)).card : Real) = primeClassThetaReal P x / Real.log x +
      intervalIntegral (fun t => primeClassThetaReal P t / (t * (Real.log t) ^ 2))
        2 x MeasureTheory.volume := by
  classical
  have hlx : 0 < Real.log x := Real.log_pos (by linarith only [hx])
  have hsum : (primeClassPrefix P (Nat.floor x)).sum
      (fun p => Real.log (p : Real) * (1 / Real.log (p : Real) - 1 / Real.log x)) =
      ((primeClassPrefix P (Nat.floor x)).card : Real) - primeClassThetaReal P x / Real.log x := by
    calc
      _ = (primeClassPrefix P (Nat.floor x)).sum
          (fun p => 1 - Real.log (p : Real) / Real.log x) := by
        apply Finset.sum_congr rfl
        intro p hp
        have hm := (primeClassPrefix_mem_iff P (Nat.floor x) p).mp hp
        have hp2 : (2 : Real) <= (p : Real) := Nat.cast_le.mpr hm.1
        have hlp : 0 < Real.log (p : Real) := Real.log_pos (by linarith only [hp2])
        field_simp
      _ = _ := by
        rw [Finset.sum_sub_distrib]
        simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
        rw [<- Finset.sum_div]
        rfl
  have h := (primeClassAbel_integral P x hx).trans hsum
  linarith only [h]

end PrimeFactorOscillations.PrimeClassDeletion

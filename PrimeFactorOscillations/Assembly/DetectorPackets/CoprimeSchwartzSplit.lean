/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Assembly.DetectorPackets.CoprimeSchwartzCenter

/-!
# CoprimeSchwartzSplit

Maintained extraction of completed detector/packet proof components.
All original theorem hypotheses and retained proof bodies are preserved.
This module alone asserts no improved zero-free boundary.
-/

set_option autoImplicit false
set_option Elab.async false

/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described by LICENSE.
Authors: Prime Factor Oscillations contributors
-/


noncomputable section
open scoped BigOperators Classical

namespace PrimeFactorOscillations.CoprimeSchwartzSplit

open CoprimeSchwartzPoisson CoprimeSchwartzCenter
open MeasureTheory

theorem finite_tsum_split (F : Finset Int) (u : Int -> Complex) (hu : Summable u) :
    tsum u = F.sum u + tsum (fun n => if Membership.mem F n then 0 else u n) := by
  let small := fun n => if Membership.mem F n then u n else 0
  let large := fun n => if Membership.mem F n then 0 else u n
  have hs : Summable small := by
    apply (hu.indicator (Set.ofPred (fun n => Membership.mem F n))).congr
    intro n
    simp only [Set.indicator_apply, Set.mem_ofPred_eq, small]
  have hl : Summable large := by
    apply (hu.indicator (Set.ofPred (fun n => Not (Membership.mem F n)))).congr
    intro n
    simp only [Set.indicator_apply, Set.mem_ofPred_eq, large]
    by_cases hn : Membership.mem F n <;> simp only [hn, ite_true, ite_false, not_true_eq_false, not_false_eq_true]
  have heq : tsum small = F.sum u := by
    calc
      _ = F.sum small := tsum_eq_sum (fun n hn => by
        rw [if_neg hn])
      _ = _ := by
        apply Finset.sum_congr rfl
        intro n hn
        exact if_pos hn
  calc
    _ = tsum (fun n => small n + large n) := by
      apply tsum_congr
      intro n
      dsimp only [small, large]
      by_cases hn : Membership.mem F n <;> simp only [hn, ite_true, ite_false, zero_add, add_zero]
    _ = tsum small + tsum large := hs.tsum_add hl
    _ = _ := by rw [heq]

def frequencyRange (L : Nat) : Finset Int := Finset.Icc (-(L : Int)) (L : Int)

def frequencyPacket (L : Nat) (f : SchwartzMap Real Complex) (a : Real) : Complex :=
  (frequencyRange L).sum (fun n => if n = 0 then 0 else f ((n : Real) * a))

def frequencyTail (L : Nat) (f : SchwartzMap Real Complex) (a : Real) : Complex :=
  tsum (fun n : Int => if Membership.mem (frequencyRange L) n then 0 else f ((n : Real) * a))

theorem zero_mem_frequencyRange (L : Nat) : Membership.mem (frequencyRange L) 0 := by
  apply Finset.mem_Icc.mpr
  constructor <;> omega

theorem offZero_summable (f : SchwartzMap Real Complex) (a : Real) (ha : 0 < a) :
    Summable (fun n : Int => if n = 0 then 0 else f ((n : Real) * a)) := by
  have hs : Summable (fun n : Int => f ((n : Real) * a)) := by
    simpa only [mul_comm] using scaled_samples_summable a (ne_of_gt ha) f
  apply (hs.indicator (Set.ofPred (fun n : Int => Not (n = 0)))).congr
  intro n
  simp only [Set.indicator_apply, Set.mem_ofPred_eq]
  by_cases hn : n = 0 <;> simp only [hn, ite_true, ite_false, not_true_eq_false, not_false_eq_true]

theorem frequency_split (L : Nat) (f : SchwartzMap Real Complex) (a : Real) (ha : 0 < a) :
    offZeroSum f a = frequencyPacket L f a + frequencyTail L f a := by
  have h := finite_tsum_split (frequencyRange L)
    (fun n : Int => if n = 0 then 0 else f ((n : Real) * a))
    (offZero_summable f a ha)
  change offZeroSum f a = frequencyPacket L f a + _ at h
  rw [h]
  congr 1
  apply tsum_congr
  intro n
  by_cases hn : Membership.mem (frequencyRange L) n
  . rw [if_pos hn, if_pos hn]
  . rw [if_neg hn, if_neg hn]
    have hn0 : Not (n = 0) := by
      intro hz
      apply hn
      rw [hz]
      exact zero_mem_frequencyRange L
    rw [if_neg hn0]

theorem primal_dual_balance (f : SchwartzMap Real Complex) (a : Real) (ha : 0 < a) :
    f 0 + offZeroSum f a =
      ((1 / a : Real) : Complex) *
        (integral volume (fun x : Real => f x) +
          offZeroSum (FourierTransform.fourier f) (1 / a)) := by
  rw [<- samples_split_zero f a ha]
  calc
    _ = tsum (fun n : Int => f (a * (n : Real))) := by
      apply tsum_congr
      intro n
      congr 1
      ring
    _ = ((1 / a : Real) : Complex) *
        tsum (fun n : Int => (FourierTransform.fourier f) ((n : Real) / a)) := by
      simpa only [zpow_neg_one, one_div] using plain_poisson_scale a ha f
    _ = ((1 / a : Real) : Complex) *
        tsum (fun n : Int => (FourierTransform.fourier f) ((n : Real) * (1 / a))) := by
      congr 1
      apply tsum_congr
      intro n
      congr 1
      ring
    _ = _ := by
      rw [samples_split_zero (FourierTransform.fourier f) (1 / a)
        (div_pos (by norm_num) ha), fourier_at_zero]

end PrimeFactorOscillations.CoprimeSchwartzSplit

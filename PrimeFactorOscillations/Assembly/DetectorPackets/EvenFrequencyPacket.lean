/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Assembly.DetectorPackets.CoprimeSchwartzSplit
import PrimeFactorOscillations.Assembly.DetectorPackets.SchwartzQuadraticSource

/-!
# EvenFrequencyPacket

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

namespace PrimeFactorOscillations.EvenFrequencyPacket

open CoprimeSchwartzSplit SchwartzQuadraticSource

theorem frequencyRange_succ (L : Nat) :
    frequencyRange (L + 1) =
      insert (-((L + 1 : Nat) : Int)) (insert ((L + 1 : Nat) : Int) (frequencyRange L)) := by
  ext n
  simp only [frequencyRange, Finset.mem_Icc, Finset.mem_insert]
  omega

theorem even_frequencyPacket (f : SchwartzMap Real Complex)
    (hf : forall x : Real, f (-x) = f x) (a : Real) (L : Nat) :
    frequencyPacket L f a =
      2 * (Finset.Ioc 0 L).sum (fun ell => f ((ell : Real) * a)) := by
  induction L with
  | zero =>
      simp only [frequencyPacket, frequencyRange, Nat.cast_zero, neg_zero,
        Finset.Icc_self, Finset.sum_singleton, ite_true, Finset.Ioc_self, Finset.sum_empty, mul_zero]
  | succ L ih =>
      let k : Int := ((L + 1 : Nat) : Int)
      have hp0 : Not (k = 0) := by dsimp only [k]; omega
      have hn0 : Not (-k = 0) := by dsimp only [k]; omega
      have hp : Not (Membership.mem (frequencyRange L) k) := by
        simp only [frequencyRange, Finset.mem_Icc]
        dsimp only [k]
        omega
      have hn : Not (Membership.mem (insert k (frequencyRange L)) (-k)) := by
        simp only [Finset.mem_insert, frequencyRange, Finset.mem_Icc]
        dsimp only [k]
        omega
      have hposval :
          (if k = 0 then (0 : Complex) else f ((k : Real) * a)) =
            f (((L + 1 : Nat) : Real) * a) := by
        rw [if_neg hp0]
        simp only [k, Int.cast_natCast]
      have hnegval :
          (if -k = 0 then (0 : Complex) else f (((-k : Int) : Real) * a)) =
            f (((L + 1 : Nat) : Real) * a) := by
        rw [if_neg hn0]
        simpa only [k, Int.cast_neg, Int.cast_natCast, neg_mul] using
          hf (((L + 1 : Nat) : Real) * a)
      have hNat : Finset.Ioc 0 (L + 1) = insert (L + 1) (Finset.Ioc 0 L) := by
        ext n
        simp only [Finset.mem_Ioc, Finset.mem_insert]
        omega
      have hNatNew : Not (Membership.mem (Finset.Ioc 0 L) (L + 1)) := by
        simp only [Finset.mem_Ioc]
        omega
      change frequencyPacket (L + 1) f a = _
      unfold frequencyPacket
      rw [frequencyRange_succ]
      change (insert (-k) (insert k (frequencyRange L))).sum
        (fun n : Int => if n = 0 then 0 else f ((n : Real) * a)) = _
      rw [Finset.sum_insert hn, Finset.sum_insert hp, hnegval, hposval]
      change f (((L + 1 : Nat) : Real) * a) +
        (f (((L + 1 : Nat) : Real) * a) + frequencyPacket L f a) = _
      rw [ih, hNat, Finset.sum_insert hNatNew]
      ring

theorem source_frequencyPacket (W : SchwartzMap Real Complex) (a : Real)
    (ha : Not (a = 0)) (scale : Real) (L : Nat) :
    frequencyPacket L (sourceRho W a ha) scale =
      2 * (Finset.Ioc 0 L).sum (fun ell => sourceRho W a ha ((ell : Real) * scale)) :=
  even_frequencyPacket (sourceRho W a ha) (sourceRho_even W a ha) scale L

end PrimeFactorOscillations.EvenFrequencyPacket


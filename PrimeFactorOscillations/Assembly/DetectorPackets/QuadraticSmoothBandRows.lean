/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Assembly.DetectorPackets.QuadraticBandUniformPhase
import PrimeFactorOscillations.Assembly.DetectorPackets.SchwartzFinitePacket

/-!
# QuadraticSmoothBandRows

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

namespace PrimeFactorOscillations.QuadraticSmoothBandRows

open QuadraticCarrierPacket QuadraticProductDivisor QuadraticProductBand
open SchwartzFiniteSeparation

def bandRows (D : Nat) (R : Finset Nat) : Finset (Prod Nat Nat) :=
  (Finset.Ioc D (2 * D)).product R

def coefficient (a b : Nat -> Complex) (d r n m : Nat) : Complex :=
  if Nat.Coprime n m /\ Dvd.dvd d (n * m) then
    a n * kernel r n * (b m * kernel r m) else 0

def logArgument (eta theta delta epsilon : Nat -> Real)
    (p q : Prod Nat Nat) : Real :=
  eta q.1 + theta q.2 + delta p.1 + epsilon p.2

def smoothBandMean (D : Nat) (R S T : Finset Nat) (a b : Nat -> Complex)
    (F : SchwartzMap Real Complex) (scale : Real) (eta theta delta epsilon : Nat -> Real) : Real :=
  (bandRows D R).sum (fun p => norm ((S.product T).sum (fun q =>
    coefficient a b p.1 p.2 q.1 q.2 *
      F (scale * Real.exp (logArgument eta theta delta epsilon p q)))))

theorem phase_row (S T : Finset Nat) (a b : Nat -> Complex) (d r : Nat)
    (eta theta delta epsilon : Nat -> Real) (t : Real) :
    (S.product T).sum (fun q => coefficient a b d r q.1 q.2 *
      (phase t (logArgument eta theta delta epsilon (Prod.mk d r) q) : Complex)) =
      (phase t (delta d + epsilon r) : Complex) *
        divisorRow d S T (fun n => a n * (phase t (eta n) : Complex))
          (fun m => b m * (phase t (theta m) : Complex)) r := by
  let Z : Nat -> Nat -> Complex := fun n m =>
    if Nat.Coprime n m /\ Dvd.dvd d (n * m) then
      (a n * (phase t (eta n) : Complex)) * kernel r n *
        ((b m * (phase t (theta m) : Complex)) * kernel r m) else 0
  have hterm (n m : Nat) :
      coefficient a b d r n m *
        (phase t (logArgument eta theta delta epsilon (Prod.mk d r) (Prod.mk n m)) : Complex) =
        (phase t (delta d + epsilon r) : Complex) * Z n m := by
    have hy : logArgument eta theta delta epsilon (Prod.mk d r) (Prod.mk n m) =
        (delta d + epsilon r) + (eta n + theta m) := by
      unfold logArgument
      ring
    by_cases h : Nat.Coprime n m /\ Dvd.dvd d (n * m)
    next =>
      dsimp only [coefficient, Z]
      rw [if_pos h, if_pos h, hy,
        phase_add t (delta d + epsilon r) (eta n + theta m),
        phase_add t (eta n) (theta m), Circle.coe_mul, Circle.coe_mul]
      ring
    next =>
      dsimp only [coefficient, Z]
      rw [if_neg h, if_neg h, zero_mul, mul_zero]
  calc
    _ = S.sum (fun n => T.sum (fun m => coefficient a b d r n m *
        (phase t (logArgument eta theta delta epsilon (Prod.mk d r) (Prod.mk n m)) : Complex))) :=
      Finset.sum_product S T _
    _ = S.sum (fun n => T.sum (fun m =>
        (phase t (delta d + epsilon r) : Complex) * Z n m)) := by
      apply Finset.sum_congr rfl
      intro n hn
      apply Finset.sum_congr rfl
      intro m hm
      exact hterm n m
    _ = S.sum (fun n => (phase t (delta d + epsilon r) : Complex) *
        T.sum (Z n)) := by
      apply Finset.sum_congr rfl
      intro n hn
      exact (Finset.mul_sum _ _ _).symm
    _ = (phase t (delta d + epsilon r) : Complex) *
        S.sum (fun n => T.sum (Z n)) := (Finset.mul_sum _ _ _).symm
    _ = _ := rfl

theorem phase_band_mean (D : Nat) (R S T : Finset Nat) (a b : Nat -> Complex)
    (eta theta delta epsilon : Nat -> Real) (t : Real) :
    (bandRows D R).sum (fun p => norm ((S.product T).sum (fun q =>
      coefficient a b p.1 p.2 q.1 q.2 *
        (phase t (logArgument eta theta delta epsilon p q) : Complex)))) =
      productBandMean D R S T (fun n => a n * (phase t (eta n) : Complex))
        (fun m => b m * (phase t (theta m) : Complex)) := by
  calc
    _ = (bandRows D R).sum (fun p =>
        norm (divisorRow p.1 S T (fun n => a n * (phase t (eta n) : Complex))
          (fun m => b m * (phase t (theta m) : Complex)) p.2)) := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [phase_row, norm_mul, phase_norm, one_mul]
    _ = (Finset.Ioc D (2 * D)).sum (fun d => R.sum (fun r =>
        norm (divisorRow d S T (fun n => a n * (phase t (eta n) : Complex))
          (fun m => b m * (phase t (theta m) : Complex)) r))) :=
      Finset.sum_product _ _ _
    _ = _ := rfl

end PrimeFactorOscillations.QuadraticSmoothBandRows


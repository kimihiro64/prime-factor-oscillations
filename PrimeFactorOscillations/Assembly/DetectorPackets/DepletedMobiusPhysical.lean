/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Assembly.DetectorPackets.DepletedMobiusUniform

/-!
# DepletedMobiusPhysical

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

namespace PrimeFactorOscillations.DepletedMobius

theorem moebius_mul_masked (h m : Nat) :
    ArithmeticFunction.moebius (h * m) =
      ArithmeticFunction.moebius h * maskedMobius h m := by
  by_cases hc : m.Coprime h
  . rw [ArithmeticFunction.isMultiplicative_moebius.2 hc.symm]
    simp [maskedMobius, hc]
  . have hnsf : Not (Squarefree (h * m)) :=
      fun hs => hc (Nat.coprime_of_squarefree_mul hs).symm
    simp [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hnsf, maskedMobius, hc]

def multiplePrefix {R : Type*} [Ring R] (h : Nat) (eta : Nat -> R) (N : Nat) : R :=
  (Finset.Ioc 0 N).sum (fun m =>
    (ArithmeticFunction.moebius (h * m) : R) * eta (h * m))

theorem multiple_prefix_eq {R : Type*} [CommRing R] (h N : Nat) (eta : Nat -> R)
    (heta : forall m n : Nat, eta (m * n) = eta m * eta n) :
    multiplePrefix h eta N =
      ((ArithmeticFunction.moebius h : R) * eta h) * depletedPrefix h eta N := by
  rw [multiplePrefix, depletedPrefix, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m _
  rw [moebius_mul_masked, Int.cast_mul, heta]
  by_cases hc : m.Coprime h
  <;> simp [maskedMobius, hc]
  <;> ring

theorem moebius_cast_norm_le {R : Type*} [NormedField R] (n : Nat) :
    norm (ArithmeticFunction.moebius n : R) <= 1 := by
  rcases ArithmeticFunction.moebius_eq_or n with hz | ho | hn
  . simp only [hz, Int.cast_zero, norm_zero, zero_le_one]
  . simp only [ho, Int.cast_one, norm_one, le_refl]
  . simp only [hn, Int.cast_neg, Int.cast_one, norm_neg, norm_one, le_refl]

theorem multiple_prefix_uniform {R : Type*} [NormedField R]
    (eta : Nat -> R) (heta : forall m n : Nat, eta (m * n) = eta m * eta n)
    (hnorm : forall n : Nat, norm (eta n) <= 1)
    (alpha eps C : Real) (halpha : 0 < alpha) (heps : 0 < eps) (hC : 0 <= C)
    (hbase : forall n : Nat, norm (mertensPrefix eta n) <= C * (n : Real) ^ alpha) :
    exists B : Real, 0 < B /\ forall h N : Nat, Not (h = 0) ->
      norm (multiplePrefix h eta N) <= C * B * (N : Real) ^ alpha * (h : Real) ^ eps := by
  choose B hB hb using depleted_prefix_uniform eta heta hnorm alpha eps C halpha heps hC hbase
  refine Exists.intro B (And.intro hB ?_)
  intro h N hh
  rw [multiple_prefix_eq h N eta heta, norm_mul]
  have hc : norm ((ArithmeticFunction.moebius h : R) * eta h) <= 1 := by
    rw [norm_mul]
    exact (mul_le_mul (moebius_cast_norm_le h) (hnorm h) (norm_nonneg _) zero_le_one).trans
      (by norm_num)
  calc
    _ <= 1 * norm (depletedPrefix h eta N) :=
      mul_le_mul_of_nonneg_right hc (norm_nonneg _)
    _ <= _ := by simpa only [one_mul] using hb h N hh

theorem cutoff_multiple_uniform {R : Type*} [NormedField R]
    (eta : Nat -> R) (heta : forall m n : Nat, eta (m * n) = eta m * eta n)
    (hnorm : forall n : Nat, norm (eta n) <= 1)
    (alpha eps C : Real) (halpha : 0 < alpha) (heps : 0 < eps) (hC : 0 <= C)
    (hbase : forall n : Nat, norm (mertensPrefix eta n) <= C * (n : Real) ^ alpha) :
    exists B : Real, 0 < B /\ forall h X : Nat, Not (h = 0) ->
      norm (multiplePrefix h eta (X / h)) <=
        C * B * (X : Real) ^ alpha * (h : Real) ^ (eps - alpha) := by
  choose B hB hb using multiple_prefix_uniform eta heta hnorm alpha eps C halpha heps hC hbase
  refine Exists.intro B (And.intro hB ?_)
  intro h X hh
  have hhpos : 0 < h := Nat.pos_iff_ne_zero.mpr hh
  have hhreal : 0 < (h : Real) := by exact_mod_cast hhpos
  calc
    _ <= C * B * ((X / h : Nat) : Real) ^ alpha * (h : Real) ^ eps := hb h (X / h) hh
    _ <= C * B * ((X : Real) ^ alpha / (h : Real) ^ alpha) * (h : Real) ^ eps :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (floor_rpow_le halpha.le X h hhpos) (by positivity))
        (Real.rpow_nonneg hhreal.le eps)
    _ = _ := by rw [Real.rpow_sub hhreal]; ring

theorem mixed_cutoff_multiple_uniform {I R : Type*} [NormedField R]
    (S : Finset I) (weight : I -> R) (eta : I -> Nat -> R)
    (heta : forall i m n, eta i (m * n) = eta i m * eta i n)
    (hnorm : forall i n, norm (eta i n) <= 1)
    (alpha eps : Real) (C : I -> Real)
    (halpha : 0 < alpha) (heps : 0 < eps) (hC : forall i, 0 <= C i)
    (hbase : forall i n, norm (mertensPrefix (eta i) n) <= C i * (n : Real) ^ alpha) :
    exists K : Real, 0 <= K /\ forall h X : Nat, Not (h = 0) ->
      norm (S.sum (fun i => weight i * multiplePrefix h (eta i) (X / h))) <=
        K * (X : Real) ^ alpha * (h : Real) ^ (eps - alpha) := by
  have hinput (i : I) := cutoff_multiple_uniform (eta i) (heta i) (hnorm i)
    alpha eps (C i) halpha heps (hC i) (hbase i)
  choose B hB hb using hinput
  refine Exists.intro (S.sum (fun i => norm (weight i) * C i * B i)) (And.intro ?_ ?_)
  . apply Finset.sum_nonneg
    intro i _
    exact mul_nonneg (mul_nonneg (norm_nonneg _) (hC i)) (hB i).le
  . intro h X hh
    apply (norm_sum_le _ _).trans
    calc
      _ <= S.sum (fun i => (norm (weight i) * C i * B i) *
          (X : Real) ^ alpha * (h : Real) ^ (eps - alpha)) := by
        apply Finset.sum_le_sum
        intro i _
        rw [norm_mul]
        have hi := mul_le_mul_of_nonneg_left (hb i h X hh) (norm_nonneg (weight i))
        convert hi using 1 <;> ring
      _ = _ := by rw [<- Finset.sum_mul, <- Finset.sum_mul]

end PrimeFactorOscillations.DepletedMobius

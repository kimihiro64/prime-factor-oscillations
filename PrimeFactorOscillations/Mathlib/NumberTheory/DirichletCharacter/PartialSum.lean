/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Nat.Periodic
import Mathlib.NumberTheory.DirichletCharacter.Bounds
import Mathlib.Order.Interval.Finset.Nat

/-!
# Exact modulus bounds for nonprincipal character sums

Complete periods cancel. The remaining initial segment has fewer than N
terms, each of norm at most one; no extra endpoint error is added.
-/

set_option autoImplicit false
set_option Elab.async false

namespace Finset

theorem norm_sum_range_le_period (f : Nat -> Complex) (P : Nat) (hP : 0 < P)
    (hperiod : Function.Periodic f P)
    (hzero : Finset.sum (Finset.range P) f = 0)
    (hunit : forall n, norm (f n) <= 1) (X : Nat) :
    norm (Finset.sum (Finset.range X) f) <= (P : Real) := by
  induction X using Nat.strong_induction_on with
  | h X ih =>
    by_cases hXP : X < P
    next =>
      calc
        _ <= Finset.sum (Finset.range X) (fun n => norm (f n)) := norm_sum_le _ _
        _ <= Finset.sum (Finset.range X) (fun _ => (1 : Real)) :=
          Finset.sum_le_sum (fun n hn => hunit n)
        _ = (X : Real) := by simp
        _ <= (P : Real) := Nat.cast_le.mpr hXP.le
    next =>
      have hle : P <= X := Nat.le_of_not_gt hXP
      have hsplit : X = P + (X - P) := by omega
      have hshift (n : Nat) : f (P + n) = f n :=
        (congrArg f (Nat.add_comm P n)).trans (hperiod n)
      calc
        _ = norm (Finset.sum (Finset.range (P + (X - P))) f) :=
          congrArg (fun k => norm (Finset.sum (Finset.range k) f)) hsplit
        _ = norm (Finset.sum (Finset.range (X - P)) (fun n => f (P + n))) := by
          rw [Finset.sum_range_add, hzero, zero_add]
        _ = norm (Finset.sum (Finset.range (X - P)) f) := by
          congr 1
          apply Finset.sum_congr rfl
          intro n hn
          exact hshift n
        _ <= (P : Real) := ih (X - P) (by omega)

end Finset

namespace DirichletCharacter

theorem norm_sum_range_le_modulus {N : Nat} [NeZero N]
    (chi : DirichletCharacter Complex N) (hchi : Not (chi = 1)) (X : Nat) :
    norm (Finset.sum (Finset.range X) (fun n => chi (n : ZMod N))) <= (N : Real) := by
  classical
  have hAll : Finset.sum (Finset.range N) (fun n => chi (n : ZMod N)) =
      Finset.sum Finset.univ chi := by
    apply Finset.sum_bij (fun (n : Nat) _ => (n : ZMod N))
    next => intro n hn; exact Finset.mem_univ _
    next =>
      intro n hn m hm h
      have hv := congrArg ZMod.val h
      simpa only [ZMod.val_natCast_of_lt (Finset.mem_range.mp hn),
        ZMod.val_natCast_of_lt (Finset.mem_range.mp hm)] using hv
    next =>
      intro a ha
      exact Exists.intro a.val (Exists.intro (Finset.mem_range.mpr (ZMod.val_lt a))
        (ZMod.natCast_zmod_val a))
    next => intro n hn; rfl
  have hZero : Finset.sum (Finset.range N) (fun n => chi (n : ZMod N)) = 0 :=
    hAll.trans (chi.sum_eq_zero_of_ne_one hchi)
  have hPeriod : Function.Periodic (fun n : Nat => chi (n : ZMod N)) N := by
    intro n
    simp [Nat.cast_add]
  exact Finset.norm_sum_range_le_period (fun n => chi (n : ZMod N)) N
    (Nat.pos_of_ne_zero (NeZero.ne N)) hPeriod hZero (fun n => chi.norm_le_one _) X

theorem norm_sum_Icc_le_modulus {N : Nat} [NeZero N]
    (chi : DirichletCharacter Complex N) (hchi : Not (chi = 1)) (X : Nat) :
    norm (Finset.sum (Finset.Icc 1 X) (fun n => chi (n : ZMod N))) <= (N : Real) := by
  have hZero : chi (0 : ZMod N) = 0 :=
    chi.map_zero' (fun hN => hchi (chi.level_one' hN))
  have hRange : Finset.sum (Finset.Icc 1 X) (fun n => chi (n : ZMod N)) =
      Finset.sum (Finset.range (X + 1)) (fun n => chi (n : ZMod N)) := by
    have h := Finset.sum_Ico_eq_sub (fun n : Nat => chi (n : ZMod N))
      (Nat.succ_le_succ (Nat.zero_le X))
    have hset : Finset.Ico 1 (X + 1) = Finset.Icc 1 X := by
      ext n
      simp only [Finset.mem_Ico, Finset.mem_Icc]
      omega
    rw [hset] at h
    simpa [hZero] using h
  rw [hRange]
  exact norm_sum_range_le_modulus chi hchi (X + 1)

end DirichletCharacter

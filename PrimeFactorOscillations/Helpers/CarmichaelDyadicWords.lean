/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Basic.Real.Basic
import Mathlib.Data.List.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Free dyadic word geometry

The two reflected inverse power maps have disjoint images inside a fixed
interval. The root lies in their gap, so all finite words, including words
of different lengths, represent distinct real coordinates. This is the
point-injectivity input for fixed-strip atomic carrier sharpness.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations.CarmichaelDyadicSharpness

def wordReal : List Bool -> Real
  | [] => 1 / 4
  | false :: w => (1 - wordReal w) / 2
  | true :: w => (1 - wordReal w) / 4

def wordScore : List Bool -> Nat
  | [] => 0
  | false :: w => wordScore w + 1
  | true :: w => wordScore w + 2

theorem wordReal_bounds (w : List Bool) :
    (1 / 7 : Real) <= wordReal w /\ wordReal w <= (3 / 7 : Real) := by
  induction w with
  | nil => norm_num [wordReal]
  | cons b w ih =>
    cases b <;> constructor <;> simp only [wordReal] <;> linarith [ih.1, ih.2]

theorem wordReal_false_bounds (w : List Bool) :
    (2 / 7 : Real) <= wordReal (false :: w) /\
      wordReal (false :: w) <= (3 / 7 : Real) := by
  have h := wordReal_bounds w
  constructor <;> simp only [wordReal] <;> linarith [h.1, h.2]

theorem wordReal_true_bounds (w : List Bool) :
    (1 / 7 : Real) <= wordReal (true :: w) /\
      wordReal (true :: w) <= (3 / 14 : Real) := by
  have h := wordReal_bounds w
  constructor <;> simp only [wordReal] <;> linarith [h.1, h.2]

theorem wordReal_injective : Function.Injective wordReal := by
  intro u v
  induction u generalizing v with
  | nil =>
    intro h
    cases v with
    | nil => rfl
    | cons b v =>
      cases b
      . have hb := (wordReal_false_bounds v).1
        rw [<- h] at hb
        norm_num [wordReal] at hb
      . have hb := (wordReal_true_bounds v).2
        rw [<- h] at hb
        norm_num [wordReal] at hb
  | cons a u ih =>
    intro h
    cases v with
    | nil =>
      cases a
      . have hb := (wordReal_false_bounds u).1
        rw [h] at hb
        norm_num [wordReal] at hb
      . have hb := (wordReal_true_bounds u).2
        rw [h] at hb
        norm_num [wordReal] at hb
    | cons b v =>
      cases a <;> cases b
      . have ht : wordReal u = wordReal v := by
          simp only [wordReal] at h
          linarith
        exact congrArg (List.cons false) (ih ht)
      . exfalso
        have hLower := (wordReal_false_bounds u).1
        have hUpper := (wordReal_true_bounds v).2
        rw [h] at hLower
        linarith
      . exfalso
        have hLower := (wordReal_false_bounds v).1
        have hUpper := (wordReal_true_bounds u).2
        rw [h] at hUpper
        linarith
      . have ht : wordReal u = wordReal v := by
          simp only [wordReal] at h
          linarith
        exact congrArg (List.cons true) (ih ht)

theorem wordScore_le_twice_length (w : List Bool) :
    wordScore w <= 2 * w.length := by
  induction w with
  | nil => simp [wordScore]
  | cons b w ih =>
    cases b
    . simp only [wordScore, List.length_cons]
      calc
        wordScore w + 1 <= 2 * w.length + 2 := Nat.add_le_add ih (by decide)
        _ = 2 * (w.length + 1) := by ring
    . simp only [wordScore, List.length_cons]
      calc
        wordScore w + 2 <= 2 * w.length + 2 := Nat.add_le_add_right ih 2
        _ = 2 * (w.length + 1) := by ring

def wordSupport : Nat -> Finset (List Bool)
  | 0 => {[]}
  | n + 1 => Insert.insert []
      (Union.union ((wordSupport n).image (List.cons false))
        ((wordSupport n).image (List.cons true)))

theorem mem_wordSupport (n : Nat) (w : List Bool) :
    Membership.mem (wordSupport n) w <-> w.length <= n := by
  induction n generalizing w with
  | zero => simp [wordSupport]
  | succ n ih =>
    cases w with
    | nil => simp [wordSupport]
    | cons b w =>
      cases b <;> simp [wordSupport, ih]

theorem wordScore_le_of_mem (n : Nat) (w : List Bool)
    (hw : Membership.mem (wordSupport n) w) : wordScore w <= 2 * n := by
  exact (wordScore_le_twice_length w).trans
    (Nat.mul_le_mul_left 2 ((mem_wordSupport n w).mp hw))

end PrimeFactorOscillations.CarmichaelDyadicSharpness

/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Data.List.Count
import Mathlib.Tactic.Ring

/-! # Finite Bernoulli coefficient algebra and deterministic rank shifts -/

set_option autoImplicit false
set_option Elab.async false

namespace List

variable {R : Type*} [CommRing R]

/-- Coefficients of the finite product of the factors (1-a)+a*z.
The definition is algebraic; positivity is supplied only when required. -/
def bernoulliMass : List R -> Nat -> R
  | [], 0 => 1
  | [], _ + 1 => 0
  | a :: s, 0 => (1 - a) * bernoulliMass s 0
  | a :: s, r + 1 =>
      (1 - a) * bernoulliMass s (r + 1) + a * bernoulliMass s r

/-- An excluded coordinate has no effect on any coefficient. -/
theorem bernoulliMass_zero_cons (s : List R) (r : Nat) :
    bernoulliMass (0 :: s) r = bernoulliMass s r := by
  cases r <;> simp [bernoulliMass]

/-- A forced coordinate annihilates the constant coefficient. -/
theorem bernoulliMass_one_cons_zero (s : List R) :
    bernoulliMass (1 :: s) 0 = 0 := by simp [bernoulliMass]

/-- A forced coordinate shifts the coefficient rank by exactly one. -/
theorem bernoulliMass_one_cons_succ (s : List R) (r : Nat) :
    bernoulliMass (1 :: s) (r + 1) = bernoulliMass s r := by simp [bernoulliMass]

/-- Below the number of forced coordinates every coefficient vanishes. -/
theorem bernoulliMass_eq_zero_of_lt_count_one [DecidableEq R]
    (s : List R) (r : Nat) (hr : r < s.count 1) :
    bernoulliMass s r = 0 := by
  induction s generalizing r with
  | nil => simp at hr
  | cons a s ih =>
      by_cases ha : a = 1
      next =>
        subst a
        have hc : (1 :: s).count 1 = s.count 1 + 1 := by simp
        rw [hc] at hr
        cases r with
        | zero => exact bernoulliMass_one_cons_zero s
        | succ r =>
            rw [bernoulliMass_one_cons_succ]
            exact ih r (by omega)
      next =>
        have hc : (a :: s).count 1 = s.count 1 := by simp [ha]
        rw [hc] at hr
        cases r with
        | zero => simp [bernoulliMass, ih 0 hr]
        | succ r =>
            simp [bernoulliMass, ih (r + 1) hr, ih r (by omega)]

/-- Removing all forced coordinates shifts the degree by their exact count.
No approximation or asymptotic rank replacement occurs here. -/
theorem bernoulliMass_count_one_add [DecidableEq R]
    (s : List R) (r : Nat) :
    bernoulliMass s (s.count 1 + r) =
      bernoulliMass (s.filter (fun a => decide (Not (a = 1)))) r := by
  induction s generalizing r with
  | nil => simp
  | cons a s ih =>
      by_cases ha : a = 1
      next =>
        subst a
        have hc : (1 :: s).count 1 = s.count 1 + 1 := by simp
        have hf : (1 :: s).filter (fun a => decide (Not (a = 1))) =
            s.filter (fun a => decide (Not (a = 1))) := by simp
        rw [hc, hf, show s.count 1 + 1 + r = (s.count 1 + r) + 1 by omega,
          bernoulliMass_one_cons_succ, ih]
      next =>
        have hc : (a :: s).count 1 = s.count 1 := by simp [ha]
        have hf : (a :: s).filter (fun a => decide (Not (a = 1))) =
            a :: s.filter (fun a => decide (Not (a = 1))) := by simp [ha]
        rw [hc, hf]
        cases r with
        | zero =>
            cases hs : s.count 1 with
            | zero =>
                have htail := ih 0
                simp only [hs, Nat.add_zero] at htail
                simp only [bernoulliMass]
                rw [htail]
            | succ n =>
                have htail := ih 0
                simp only [hs, Nat.add_zero] at htail
                have hbelow := bernoulliMass_eq_zero_of_lt_count_one s n (by omega)
                simp only [bernoulliMass]
                rw [htail, hbelow]
                simp
        | succ r =>
            rw [Nat.add_succ]
            simp only [bernoulliMass]
            rw [show s.count 1 + r + 1 = s.count 1 + (r + 1) by omega, ih, ih]

/-- All excluded coordinates can be erased without changing rank. -/
theorem bernoulliMass_filter_nonzero [DecidableEq R] (s : List R) (r : Nat) :
    bernoulliMass (s.filter (fun a => decide (Not (a = 0)))) r =
      bernoulliMass s r := by
  induction s generalizing r with
  | nil => simp
  | cons a s ih =>
      by_cases ha : a = 0
      next =>
        subst a
        have hf : (0 :: s).filter (fun a => decide (Not (a = 0))) =
            s.filter (fun a => decide (Not (a = 0))) := by simp
        rw [hf, bernoulliMass_zero_cons, ih]
      next =>
        have hf : (a :: s).filter (fun a => decide (Not (a = 0))) =
            a :: s.filter (fun a => decide (Not (a = 0))) := by simp [ha]
        rw [hf]
        cases r <;> simp only [bernoulliMass, ih]

/-- Every finite Bernoulli coefficient is invariant under permutation,
including when probability coordinates are zero or one. -/
theorem bernoulliMass_perm {R : Type*} [CommRing R] {s t : List R}
    (h : s.Perm t) (r : Nat) : bernoulliMass s r = bernoulliMass t r := by
  induction h generalizing r with
  | nil => rfl
  | cons a h ih =>
      cases r with
      | zero => simp only [bernoulliMass, ih 0]
      | succ r => simp only [bernoulliMass, ih r, ih (r + 1)]
  | swap a b entries =>
      cases r with
      | zero => simp only [bernoulliMass]; ring
      | succ r =>
          cases r with
          | zero => simp only [bernoulliMass]; ring
          | succ r => simp only [bernoulliMass]; ring
  | trans h1 h2 ih1 ih2 => exact (ih1 r).trans (ih2 r)


end List

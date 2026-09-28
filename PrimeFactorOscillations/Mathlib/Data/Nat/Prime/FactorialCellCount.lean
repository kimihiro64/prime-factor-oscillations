/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Order.Interval.Finset.Nat
import PrimeFactorOscillations.Mathlib.Data.Nat.Prime.FactorialCells

/-! # Uniform finite fibers for primes in factorial cells -/

namespace Nat

/-- The full shift interval of a factorial cell contains at most F+H shifts. -/
theorem card_factorial_cell_shift_interval_le (F H c : Nat) :
    (Finset.Icc (c * F + 2 - H) ((c + 1) * F + 1)).card <= F + H := by
  rw [Nat.card_Icc, Nat.add_mul, Nat.one_mul]
  omega

/-- Distinct window shifts have bounded fibers under their selected prime's cell. -/
theorem prime_window_shifts_le_factorial_cells (S : Finset Nat)
    (p : Nat -> Nat) (L H : Nat) (hL : 1 <= L)
    (hp : forall n, Membership.mem S n -> Nat.Prime (p n))
    (hlarge : forall n, Membership.mem S n -> Nat.factorial L + 2 <= p n)
    (hwindow : forall n, Membership.mem S n -> n <= p n /\ p n <= n + H) :
    S.card <= (Nat.factorial L + H) *
      (S.image (fun n => (p n - 2) / Nat.factorial L)).card := by
  classical
  let F := Nat.factorial L
  let cell := fun n => (p n - 2) / F
  have hfiber : forall c, (S.filter (fun n => cell n = c)).card <= F + H := by
    intro c
    apply (Finset.card_le_card (show
      S.filter (fun n => cell n = c) <=
        Finset.Icc (c * F + 2 - H) ((c + 1) * F + 1) from ?_)).trans
      (card_factorial_cell_shift_interval_le F H c)
    intro n hn
    have hnS := (Finset.mem_filter.mp hn).1
    have hcell := (Finset.mem_filter.mp hn).2
    have hb := prime_factorial_cell_bounds (hp n hnS) (hlarge n hnS)
    change 0 < cell n /\ cell n * F + L + 1 <= p n /\
      p n <= (cell n + 1) * F + 1 at hb
    rw [hcell] at hb
    have hw := hwindow n hnS
    exact Finset.mem_Icc.mpr (And.intro (by omega) (by omega))
  calc
    S.card = (S.image cell).sum (fun c => (S.filter (fun n => cell n = c)).card) :=
      Finset.card_eq_sum_card_image cell S
    _ <= (S.image cell).sum (fun _ => F + H) := by
      exact Finset.sum_le_sum (fun c _ => hfiber c)
    _ = (Nat.factorial L + H) *
        (S.image (fun n => (p n - 2) / Nat.factorial L)).card := by
      simp [F, cell, Nat.mul_comm]

end Nat

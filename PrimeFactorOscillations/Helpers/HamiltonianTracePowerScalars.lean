/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Analysis.MeanInequalities
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Ring

/-! # General mixed-power bounds for the complete trace-power Hessian

Every exponent and every ordered return pair is retained. These bounds
are for the full Hessian after orthogonal diagonalization, not for a
fixed low moment or a dimension-times-entry replacement.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

theorem hamiltonian_mixed_power_endpoint_bound (x y : Real) (n j : Nat)
    (hx : 0 <= x) (hy : 0 <= y) (hj : j <= n) :
    x ^ j * y ^ (n - j) <= x ^ n + y ^ n := by
  rcases le_total x y with hxy | hyx
  . calc
      _ <= y ^ j * y ^ (n - j) := by gcongr
      _ = y ^ n := by
        rw [<- pow_add, Nat.add_comm j (n - j), Nat.sub_add_cancel hj]
      _ <= _ := le_add_of_nonneg_left (pow_nonneg hx _)
  . calc
      _ <= x ^ j * x ^ (n - j) := by gcongr
      _ = x ^ n := by
        rw [<- pow_add, Nat.add_comm j (n - j), Nat.sub_add_cancel hj]
      _ <= _ := le_add_of_nonneg_right (pow_nonneg hy _)

variable {Iota : Type*} [Fintype Iota]

theorem hamiltonian_signed_mixed_return_power_bound
    (B : Matrix Iota Iota Real) (lam : Iota -> Real) (b : Real) (n j : Nat)
    (hj : j <= n)
    (hRows : forall i, Finset.univ.sum (fun k => B i k ^ 2) <= b)
    (hCols : forall k, Finset.univ.sum (fun i => B i k ^ 2) <= b) :
    Finset.univ.sum (fun i => Finset.univ.sum
      (fun k => B i k ^ 2 * lam i ^ j * lam k ^ (n - j))) <=
        2 * b * Finset.univ.sum (fun i => abs (lam i) ^ n) := by
  have hPoint (i k : Iota) :
      B i k ^ 2 * lam i ^ j * lam k ^ (n - j) <=
        B i k ^ 2 * (abs (lam i) ^ n + abs (lam k) ^ n) := by
    have hSigned : lam i ^ j * lam k ^ (n - j) <=
        abs (lam i) ^ j * abs (lam k) ^ (n - j) := by
      calc
        _ <= abs (lam i ^ j * lam k ^ (n - j)) := le_abs_self _
        _ = _ := by rw [abs_mul, abs_pow, abs_pow]
    have hBound := hSigned.trans (hamiltonian_mixed_power_endpoint_bound
      (abs (lam i)) (abs (lam k)) n j (abs_nonneg _) (abs_nonneg _) hj)
    calc
      _ = B i k ^ 2 * (lam i ^ j * lam k ^ (n - j)) := by ring
      _ <= _ := mul_le_mul_of_nonneg_left hBound (sq_nonneg _)
  have hLeft :
      Finset.univ.sum (fun i => Finset.univ.sum
        (fun k => B i k ^ 2 * abs (lam i) ^ n)) =
      Finset.univ.sum (fun i => abs (lam i) ^ n *
        Finset.univ.sum (fun k => B i k ^ 2)) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  have hRight :
      Finset.univ.sum (fun i => Finset.univ.sum
        (fun k => B i k ^ 2 * abs (lam k) ^ n)) =
      Finset.univ.sum (fun k => abs (lam k) ^ n *
        Finset.univ.sum (fun i => B i k ^ 2)) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  calc
    _ <= Finset.univ.sum (fun i => Finset.univ.sum
        (fun k => B i k ^ 2 * (abs (lam i) ^ n + abs (lam k) ^ n))) :=
      Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun k _ => hPoint i k))
    _ = Finset.univ.sum (fun i => abs (lam i) ^ n *
          Finset.univ.sum (fun k => B i k ^ 2)) +
        Finset.univ.sum (fun k => abs (lam k) ^ n *
          Finset.univ.sum (fun i => B i k ^ 2)) := by
      simp_rw [mul_add, Finset.sum_add_distrib]
      rw [hLeft, hRight]
    _ <= Finset.univ.sum (fun i => abs (lam i) ^ n * b) +
        Finset.univ.sum (fun k => abs (lam k) ^ n * b) :=
      add_le_add
        (Finset.sum_le_sum (fun i _ =>
          mul_le_mul_of_nonneg_left (hRows i) (pow_nonneg (abs_nonneg _) _)))
        (Finset.sum_le_sum (fun k _ =>
          mul_le_mul_of_nonneg_left (hCols k) (pow_nonneg (abs_nonneg _) _)))
    _ = _ := by simp only [<- Finset.sum_mul]; ring

theorem hamiltonian_full_mixed_return_power_bound
    (B : Matrix Iota Iota Real) (lam : Iota -> Real) (b : Real) (n : Nat)
    (hRows : forall i, Finset.univ.sum (fun k => B i k ^ 2) <= b)
    (hCols : forall k, Finset.univ.sum (fun i => B i k ^ 2) <= b) :
    (Finset.range (n + 1)).sum (fun j =>
      Finset.univ.sum (fun i => Finset.univ.sum
        (fun k => B i k ^ 2 * lam i ^ j * lam k ^ (n - j)))) <=
      2 * ((n + 1 : Nat) : Real) * b * Finset.univ.sum (fun i => abs (lam i) ^ n) := by
  calc
    _ <= (Finset.range (n + 1)).sum (fun _ =>
        2 * b * Finset.univ.sum (fun i => abs (lam i) ^ n)) :=
      Finset.sum_le_sum (fun j hj =>
        hamiltonian_signed_mixed_return_power_bound B lam b n j
          (Nat.le_of_lt_succ (Finset.mem_range.mp hj)) hRows hCols)
    _ = _ := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring

end PrimeFactorOscillations

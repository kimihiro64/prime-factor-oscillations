/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Analysis.PSeries
import Mathlib.NumberTheory.LSeries.Basic
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Vertical-uniform Dirichlet-series remainders

A reciprocal-square coefficient bound controls the complete tail uniformly
on the closed right half-plane. Exact initial coefficients turn this into a
small analytic correction without any restriction on the imaginary part.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 5000000

noncomputable section
namespace LSeries

theorem norm_term_le_of_nonneg_re (f : Nat -> Complex) (s : Complex)
    (hs : 0 <= s.re) (n : Nat) : norm (term f s n) <= norm (f n) := by
  have h := norm_term_le_of_re_le_re f (s := (0 : Complex)) (s' := s) hs n
  by_cases hn : n = 0
  . subst n
    simp only [term_zero, norm_zero]
    exact norm_nonneg _
  . simpa only [norm_term_eq, ite_eq_right hn, Complex.zero_re, Real.rpow_zero,
      div_one] using h

theorem inv_sq_sum_tail_le (N M : Nat) (hN : 0 < N) :
    Finset.sum (Finset.range M)
      (fun n => Inv.inv ((((n + (N + 1) : Nat) : Real)) ^ 2)) <= 1 / (N : Real) := by
  have he : Finset.sum (Finset.range M)
      (fun n => Inv.inv ((((n + (N + 1) : Nat) : Real)) ^ 2)) =
      Finset.sum (Finset.Ioc N (N + M)) (fun n => Inv.inv ((n : Real) ^ 2)) := by
    apply Finset.sum_bij (fun n _ => n + (N + 1))
    . intro n hn
      have hh := Finset.mem_range.mp hn
      apply Finset.mem_Ioc.mpr
      constructor <;> omega
    . intro i hi j hj hij
      exact Nat.add_right_cancel hij
    . intro n hn
      have hh := Finset.mem_Ioc.mp hn
      refine Exists.intro (n - (N + 1)) (Exists.intro ?_ ?_)
      . apply Finset.mem_range.mpr
        omega
      . omega
    . intro n hn
      rfl
  rw [he]
  have hh : Finset.sum (Finset.Ioc N (N + M))
      (fun n => Inv.inv ((n : Real) ^ 2)) <=
      Inv.inv (N : Real) - Inv.inv ((N + M : Nat) : Real) :=
    sum_Ioc_inv_sq_le_sub (Nat.ne_of_gt hN) (show N <= N + M by omega)
  calc
    _ <= Inv.inv (N : Real) - Inv.inv ((N + M : Nat) : Real) := hh
    _ <= Inv.inv (N : Real) := sub_le_self _ (inv_nonneg.mpr (Nat.cast_nonneg _))
    _ = _ := by rw [one_div]

theorem norm_tail_le_of_inv_sq (f : Nat -> Complex) (C : Real) (hC : 0 <= C)
    (hbound : forall n : Nat, Not (n = 0) -> norm (f n) <= C / (n : Real) ^ 2)
    (s : Complex) (hs : 0 <= s.re) (N : Nat) (hN : 0 < N) :
    norm (LSeries f s - Finset.sum (Finset.range (N + 1)) (term f s)) <= C / (N : Real) := by
  have hmajor (n : Nat) : norm (term f s n) <= C / (n : Real) ^ 2 := by
    by_cases hn : n = 0
    . subst n
      simp
    . exact (norm_term_le_of_nonneg_re f s hs n).trans (hbound n hn)
  have hsum : Summable (fun n : Nat => C / (n : Real) ^ 2) := by
    simpa only [div_eq_mul_inv, one_mul] using
      (Real.summable_one_div_nat_pow.mpr (by decide : 1 < (2 : Nat))).mul_left C
  have hnorm : Summable (fun n : Nat => norm (term f s n)) :=
    hsum.of_nonneg_of_le (fun n => norm_nonneg _) hmajor
  have hseries : Summable (term f s) := summable_norm_iff.mp hnorm
  have htail : Summable (fun n : Nat => term f s (n + (N + 1))) :=
    hseries.comp_injective (fun _ _ h => Nat.add_right_cancel h)
  have hfinite (M : Nat) : Finset.sum (Finset.range M)
      (fun n => norm (term f s (n + (N + 1)))) <= C / (N : Real) := by
    calc
      _ <= Finset.sum (Finset.range M)
          (fun n => C * Inv.inv ((((n + (N + 1) : Nat) : Real)) ^ 2)) := by
        apply Finset.sum_le_sum
        intro n hn
        simpa only [div_eq_mul_inv] using hmajor (n + (N + 1))
      _ = C * Finset.sum (Finset.range M)
          (fun n => Inv.inv ((((n + (N + 1) : Nat) : Real)) ^ 2)) := by
        rw [Finset.mul_sum]
      _ <= C * (1 / (N : Real)) :=
        mul_le_mul_of_nonneg_left (inv_sq_sum_tail_le N M hN) hC
      _ = _ := by ring
  have htailBound : tsum (fun n : Nat => norm (term f s (n + (N + 1)))) <=
      C / (N : Real) := le_of_tendsto htail.norm.hasSum.tendsto_sum_nat
        (Filter.Eventually.of_forall hfinite)
  have hsplit := hseries.sum_add_tsum_nat_add (N + 1)
  have he : LSeries f s - Finset.sum (Finset.range (N + 1)) (term f s) =
      tsum (fun n : Nat => term f s (n + (N + 1))) := by
    change tsum (term f s) - _ = _
    rw [<- hsplit]
    ring
  rw [he]
  exact (norm_tsum_le_tsum_norm htail.norm).trans htailBound

theorem norm_le_of_initial_vanishing_inv_sq (f : Nat -> Complex)
    (C : Real) (hC : 0 <= C)
    (hbound : forall n : Nat, Not (n = 0) -> norm (f n) <= C / (n : Real) ^ 2)
    (N : Nat) (hN : 0 < N) (hsmall : forall n : Nat, n <= N -> f n = 0)
    (s : Complex) (hs : 0 <= s.re) : norm (LSeries f s) <= C / (N : Real) := by
  have hh := norm_tail_le_of_inv_sq f C hC hbound s hs N hN
  have hhead : Finset.sum (Finset.range (N + 1)) (term f s) = 0 := by
    apply Finset.sum_eq_zero
    intro n hn
    have hz := hsmall n (Nat.le_of_lt_succ (Finset.mem_range.mp hn))
    simp [term_def, hz]
  simpa only [hhead, sub_zero] using hh

end LSeries
end

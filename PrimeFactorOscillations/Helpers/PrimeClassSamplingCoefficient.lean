/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic.Ring
import PrimeFactorOscillations.Helpers.PrimeClassDecoderCounts
import PrimeFactorOscillations.Helpers.PrimeClassSamplingFinite

/-!
# Uniform coefficient budget for the complete finite sampling remainder

The signed floor-error polynomial retains every prime subset. Only its
explicit sampling remainder is estimated. The full coefficient L1 budget
charges the exact binomial mass and the complete product of local weights.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.PrimeClassSampling

theorem abs_coeff_X_sub_one_pow (n k : Nat) :
    abs (((Polynomial.X - 1 : Polynomial Real) ^ n).coeff k) =
      (n.choose k : Real) := by
  have hbase : (Polynomial.X - 1 : Polynomial Real) =
      Polynomial.X + Polynomial.C (-1 : Real) := by simp [sub_eq_add_neg]
  rw [hbase, Polynomial.coeff_X_add_C_pow]
  simp only [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
  exact abs_of_nonneg (Nat.cast_nonneg (n.choose k))

theorem sum_abs_coeff_X_sub_one_pow (n K : Nat) (hn : n <= K) :
    (Finset.range (K + 1)).sum (fun k =>
      abs (((Polynomial.X - 1 : Polynomial Real) ^ n).coeff k)) =
        (2 : Real) ^ n := by
  simp only [abs_coeff_X_sub_one_pow]
  have hsub : Finset.range (n + 1) <= Finset.range (K + 1) := by
    intro k hk
    exact Finset.mem_range.mpr ((Finset.mem_range.mp hk).trans_le
      (Nat.add_le_add_right hn 1))
  have hzero : forall k, Membership.mem (Finset.range (K + 1)) k ->
      Not (Membership.mem (Finset.range (n + 1)) k) -> (n.choose k : Real) = 0 := by
    intro k hk hnot
    have hle : n + 1 <= k :=
      Nat.le_of_not_gt (fun h => hnot (Finset.mem_range.mpr h))
    have hnk : n < k := (Nat.lt_succ_self n).trans_le hle
    rw [Nat.choose_eq_zero_of_lt hnk]
    norm_num
  calc
    (Finset.range (K + 1)).sum (fun k => (n.choose k : Real)) =
        (Finset.range (n + 1)).sum (fun k => (n.choose k : Real)) :=
      (Finset.sum_subset hsub hzero).symm
    _ = (2 : Real) ^ n := by exact_mod_cast Nat.sum_range_choose n

theorem nat_prod_rpow (s : Finset Nat) (sigma : Real) :
    ((s.prod (fun p => p) : Nat) : Real) ^ sigma =
      s.prod (fun p => (p : Real) ^ sigma) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert p s hps ih =>
      rw [Finset.prod_insert hps, Nat.cast_mul,
        Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _),
        ih, Finset.prod_insert hps]

theorem squarefree_rpow_budget (s : Finset Nat) (sigma : Real) :
    s.powerset.sum (fun t => (2 : Real) ^ t.card *
      ((t.prod (fun p => p) : Nat) : Real) ^ (-sigma)) =
        s.prod (fun p => 1 + 2 * (p : Real) ^ (-sigma)) := by
  calc
    s.powerset.sum (fun t => (2 : Real) ^ t.card *
        ((t.prod (fun p => p) : Nat) : Real) ^ (-sigma)) =
        s.powerset.sum (fun t => t.prod (fun p => 2 * (p : Real) ^ (-sigma))) := by
      apply Finset.sum_congr rfl
      intro t ht
      rw [nat_prod_rpow, <- Finset.prod_const (2 : Real), <- Finset.prod_mul_distrib]
    _ = s.prod (fun p => 2 * (p : Real) ^ (-sigma) + 1) :=
      (Finset.prod_add_one s).symm
    _ = s.prod (fun p => 1 + 2 * (p : Real) ^ (-sigma)) := by
      apply Finset.prod_congr rfl
      intro p hp
      exact add_comm _ _

theorem sum_abs_coeff_weighted_basis_le
    (s : Finset Nat) (weight : Finset Nat -> Real) :
    (Finset.range (s.card + 1)).sum (fun k =>
      abs ((s.powerset.sum (fun t =>
        Polynomial.C (weight t) * (Polynomial.X - 1) ^ t.card)).coeff k)) <=
      s.powerset.sum (fun t => abs (weight t) * (2 : Real) ^ t.card) := by
  classical
  simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul]
  calc
    (Finset.range (s.card + 1)).sum (fun k =>
        abs (s.powerset.sum (fun t =>
          weight t * ((Polynomial.X - 1 : Polynomial Real) ^ t.card).coeff k))) <=
        (Finset.range (s.card + 1)).sum (fun k =>
          s.powerset.sum (fun t =>
            abs (weight t * ((Polynomial.X - 1 : Polynomial Real) ^ t.card).coeff k))) := by
      apply Finset.sum_le_sum
      intro k hk
      exact Finset.abs_sum_le_sum_abs _ _
    _ = s.powerset.sum (fun t => (Finset.range (s.card + 1)).sum
        (fun k => abs (weight t * ((Polynomial.X - 1 : Polynomial Real) ^ t.card).coeff k))) :=
      Finset.sum_comm
    _ = s.powerset.sum (fun t => abs (weight t) * (2 : Real) ^ t.card) := by
      apply Finset.sum_congr rfl
      intro t ht
      simp only [abs_mul]
      rw [<- Finset.mul_sum, sum_abs_coeff_X_sub_one_pow t.card s.card
        (Finset.card_le_card (Finset.mem_powerset.mp ht))]

noncomputable def finiteSamplingErrorPolynomial (s : Finset Nat) (N : Nat) :
    Polynomial Real :=
  s.powerset.sum (fun t =>
    Polynomial.C ((((N / t.prod (fun p => p) : Nat) : Real) / (N : Real)) -
      1 / ((t.prod (fun p => p) : Nat) : Real)) *
        (Polynomial.X - 1) ^ t.card)

theorem sum_abs_coeff_finiteSamplingError_le
    (s : Finset Nat) (hprime : forall p, Membership.mem s p -> Nat.Prime p)
    (N : Nat) (hN : 0 < N) (sigma : Real)
    (hs0 : 0 <= sigma) (hs1 : sigma <= 1) :
    (Finset.range (s.card + 1)).sum (fun k =>
      abs ((finiteSamplingErrorPolynomial s N).coeff k)) <=
        (N : Real) ^ (sigma - 1) *
          s.prod (fun p => 1 + 2 * (p : Real) ^ (-sigma)) := by
  unfold finiteSamplingErrorPolynomial
  apply (sum_abs_coeff_weighted_basis_le s _).trans
  calc
    s.powerset.sum (fun t =>
        abs ((((N / t.prod (fun p => p) : Nat) : Real) / (N : Real)) -
          1 / ((t.prod (fun p => p) : Nat) : Real)) * (2 : Real) ^ t.card) <=
        s.powerset.sum (fun t => (N : Real) ^ (sigma - 1) *
          ((2 : Real) ^ t.card * ((t.prod (fun p => p) : Nat) : Real) ^ (-sigma))) := by
      apply Finset.sum_le_sum
      intro t ht
      have hprodpos : 0 < t.prod (fun p => p) := by
        apply Finset.prod_pos
        intro p hp
        exact (hprime p ((Finset.mem_powerset.mp ht) hp)).pos
      have hneg :
          (((N / t.prod (fun p => p) : Nat) : Real) / (N : Real)) -
            1 / ((t.prod (fun p => p) : Nat) : Real) =
          -floorSamplingError N (t.prod (fun p => p)) := by
        unfold floorSamplingError
        ring
      rw [hneg, abs_neg, abs_of_nonneg
        (floorSamplingError_nonneg N (t.prod (fun p => p)) hN hprodpos)]
      calc
        floorSamplingError N (t.prod (fun p => p)) * (2 : Real) ^ t.card <=
            ((N : Real) ^ (sigma - 1) *
              ((t.prod (fun p => p) : Nat) : Real) ^ (-sigma)) * (2 : Real) ^ t.card :=
          mul_le_mul_of_nonneg_right
            (floorSamplingError_le_rpow N (t.prod (fun p => p)) hN hprodpos sigma hs0 hs1)
            (pow_nonneg (by norm_num) _)
        _ = (N : Real) ^ (sigma - 1) *
            ((2 : Real) ^ t.card * ((t.prod (fun p => p) : Nat) : Real) ^ (-sigma)) := by ring
    _ = (N : Real) ^ (sigma - 1) *
        s.powerset.sum (fun t => (2 : Real) ^ t.card *
          ((t.prod (fun p => p) : Nat) : Real) ^ (-sigma)) := by
      rw [Finset.mul_sum]
    _ = (N : Real) ^ (sigma - 1) *
        s.prod (fun p => 1 + 2 * (p : Real) ^ (-sigma)) := by
      rw [squarefree_rpow_budget]

end PrimeFactorOscillations.PrimeClassSampling

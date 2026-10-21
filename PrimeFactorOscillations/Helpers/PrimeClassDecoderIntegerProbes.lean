/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import PrimeFactorOscillations.Helpers.PrimeClassDecoderCounts

/-!
# Exact integer probes for a sampled prime-class decoder

The integer probes are literal finite sums of the observed counts. Their
normalization agrees exactly with evaluation of the count polynomial and,
for a positive sample size, the empirical polynomial. Their decoded labels
therefore consume the same degree budget, including at degree zero.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.PrimeClassDecoder

def integerProbe (M : Nat) (C : Nat -> Nat) (n : Nat) : Int :=
  (Finset.range (M + 1)).sum (fun k =>
    (-1 : Int) ^ k * (C k : Int) *
      ((2 * n + 1 : Nat) : Int) ^ k * (2 : Int) ^ (M - k))

theorem scaled_halfInteger_pow (M n k : Nat) (hk : k <= M) :
    (2 : Real) ^ M * (-(n : Real) - 1 / 2) ^ k =
      (-1 : Real) ^ k * (2 * (n : Real) + 1) ^ k *
        (2 : Real) ^ (M - k) := by
  have hpow : (2 : Real) ^ (M - k) * (2 : Real) ^ k = (2 : Real) ^ M := by
    rw [<- pow_add, Nat.sub_add_cancel hk]
  have hbase : (2 : Real) * (-(n : Real) - 1 / 2) =
      (-1 : Real) * (2 * (n : Real) + 1) := by ring
  calc
    (2 : Real) ^ M * (-(n : Real) - 1 / 2) ^ k =
        (2 : Real) ^ (M - k) *
          ((2 : Real) * (-(n : Real) - 1 / 2)) ^ k := by
      rw [mul_pow, <- mul_assoc, hpow]
    _ = (-1 : Real) ^ k * (2 * (n : Real) + 1) ^ k *
        (2 : Real) ^ (M - k) := by
      rw [hbase, mul_pow]
      ring

theorem integerProbe_eq_scaled_countPolynomial
    (M : Nat) (C : Nat -> Nat) (n : Nat) :
    (integerProbe M C n : Real) =
      (2 : Real) ^ M * (countPolynomial M C).eval (-(n : Real) - 1 / 2) := by
  rw [countPolynomial_eval, Finset.mul_sum]
  simp only [integerProbe, Int.cast_sum, Int.cast_mul, Int.cast_pow]
  apply Finset.sum_congr rfl
  intro k hk
  have hbound : k <= M := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
  have hterm := scaled_halfInteger_pow M n k hbound
  simp only [Int.cast_neg, Int.cast_one, Int.cast_natCast,
    Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  push_cast
  calc
    (-1 : Real) ^ k * (C k : Real) * (2 * (n : Real) + 1) ^ k *
        (2 : Real) ^ (M - k) =
        (C k : Real) * ((2 : Real) ^ M * (-(n : Real) - 1 / 2) ^ k) := by
      rw [hterm]
      ring
    _ = (2 : Real) ^ M * ((C k : Real) * (-(n : Real) - 1 / 2) ^ k) := by ring

theorem integerProbe_eq_scaled_empiricalPolynomial
    (N M : Nat) (C : Nat -> Nat) (n : Nat) (hN : 0 < N) :
    (integerProbe M C n : Real) =
      (N : Real) * (2 : Real) ^ M *
        (empiricalPolynomial N M C).eval (-(n : Real) - 1 / 2) := by
  have hNreal : Not ((N : Real) = 0) := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hN)
  rw [integerProbe_eq_scaled_countPolynomial]
  simp only [empiricalPolynomial, Polynomial.eval_mul, Polynomial.eval_C]
  calc
    (2 : Real) ^ M * (countPolynomial M C).eval (-(n : Real) - 1 / 2) =
        ((N : Real) * (1 / (N : Real))) *
          ((2 : Real) ^ M * (countPolynomial M C).eval (-(n : Real) - 1 / 2)) := by
      rw [mul_one_div_cancel hNreal, one_mul]
    _ = (N : Real) * (2 : Real) ^ M *
        (1 / (N : Real) * (countPolynomial M C).eval (-(n : Real) - 1 / 2)) := by
      ring

noncomputable def integerSignChangeIndices
    (R M : Nat) (C : Nat -> Nat) : Finset Nat :=
  (Finset.Icc 1 R).filter (fun n =>
    integerProbe M C (n - 1) * integerProbe M C n < 0)

noncomputable def integerDecodedPrimeLabels
    (R M : Nat) (C : Nat -> Nat) : Finset Nat :=
  (integerSignChangeIndices R M C).image Nat.succ

theorem integerSignChangeIndices_eq
    (R M : Nat) (C : Nat -> Nat) :
    integerSignChangeIndices R M C =
      signChangeIndices R (countPolynomial M C) := by
  classical
  apply Finset.ext
  intro n
  by_cases hn : Membership.mem (Finset.Icc 1 R) n
  case neg =>
    simp [integerSignChangeIndices, signChangeIndices, hn]
  case pos =>
    have hn1 : 1 <= n := (Finset.mem_Icc.mp hn).1
    have hsub : ((n - 1 : Nat) : Real) = (n : Real) - 1 := by
      rw [Nat.cast_sub hn1]
      norm_num
    have hleft : -((n - 1 : Nat) : Real) - 1 / 2 =
        -(n : Real) + 1 / 2 := by rw [hsub]; ring
    have hprev := integerProbe_eq_scaled_countPolynomial M C (n - 1)
    rw [hleft] at hprev
    have hnext := integerProbe_eq_scaled_countPolynomial M C n
    have hpos : 0 < (2 : Real) ^ M * (2 : Real) ^ M :=
      mul_pos (pow_pos (by norm_num) M) (pow_pos (by norm_num) M)
    simp only [integerSignChangeIndices, signChangeIndices, Finset.mem_filter, hn,
      true_and]
    have hcast :
        (integerProbe M C (n - 1) : Real) * (integerProbe M C n : Real) < 0 <->
          integerProbe M C (n - 1) * integerProbe M C n < 0 := by
      norm_cast
    rw [<- hcast, hprev, hnext]
    rw [show
      ((2 : Real) ^ M * (countPolynomial M C).eval (-(n : Real) + 1 / 2)) *
          ((2 : Real) ^ M * (countPolynomial M C).eval (-(n : Real) - 1 / 2)) =
        ((2 : Real) ^ M * (2 : Real) ^ M) *
          ((countPolynomial M C).eval (-(n : Real) + 1 / 2) *
            (countPolynomial M C).eval (-(n : Real) - 1 / 2)) by ring]
    constructor
    case mp =>
      intro h
      cases mul_neg_iff.mp h with
      | inl hsign => exact hsign.2
      | inr hsign => exact False.elim (lt_asymm hpos hsign.1)
    case mpr =>
      intro h
      exact mul_neg_of_pos_of_neg hpos h

theorem integerDecodedPrimeLabels_eq
    (R M : Nat) (C : Nat -> Nat) :
    integerDecodedPrimeLabels R M C =
      decodedPrimeLabels R (countPolynomial M C) := by
  unfold integerDecodedPrimeLabels decodedPrimeLabels
  rw [integerSignChangeIndices_eq]

theorem card_integerDecodedPrimeLabels_le
    (R M : Nat) (C : Nat -> Nat) (hC : 0 < C 0) :
    (integerDecodedPrimeLabels R M C).card <= M := by
  rw [integerDecodedPrimeLabels_eq]
  exact (card_decodedPrimeLabels_le_natDegree R (countPolynomial M C)
      (countPolynomial_ne_zero M C hC)).trans
    (natDegree_countPolynomial_le M C)

theorem card_integerDecodedSampleLabels_le
    (P : Set Nat) (N M R : Nat) (hN : 0 < N) :
    (integerDecodedPrimeLabels R M (sampleCount P N)).card <= M :=
  card_integerDecodedPrimeLabels_le R M (sampleCount P N)
    (sampleCount_zero_pos P N hN)

end PrimeFactorOscillations.PrimeClassDecoder

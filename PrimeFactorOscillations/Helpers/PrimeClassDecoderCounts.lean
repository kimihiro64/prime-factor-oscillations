/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Tactic.NormNum
import PrimeFactorOscillations.Helpers.PrimeClassDecoderDegree

/-!
# Actual finite integer samples and their decoder degree budget

The sample is the full set of integers from one through N. Divisor membership
is tested on the literal prime class and actual divisibility. The zero bin
contains one, making its count polynomial nonzero without a model assumption.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.PrimeClassDecoder

noncomputable def primeDivisorCount (P : Set Nat) (m : Nat) : Nat := by
  classical
  exact ((Finset.Icc 2 m).filter (fun p =>
    And (Nat.Prime p) (And (Dvd.dvd p m) (Membership.mem P p)))).card

noncomputable def sampleCount (P : Set Nat) (N k : Nat) : Nat := by
  classical
  exact ((Finset.Icc 1 N).filter (fun m => primeDivisorCount P m = k)).card

theorem primeDivisorCount_one (P : Set Nat) :
    primeDivisorCount P 1 = 0 := by
  simp [primeDivisorCount]

theorem sampleCount_zero_pos (P : Set Nat) (N : Nat) (hN : 0 < N) :
    0 < sampleCount P N 0 := by
  classical
  unfold sampleCount
  apply Finset.card_pos.mpr
  apply Exists.intro 1
  apply Finset.mem_filter.mpr
  exact And.intro
    (Finset.mem_Icc.mpr (And.intro (le_refl 1) (Nat.succ_le_of_lt hN)))
    (primeDivisorCount_one P)

noncomputable def countPolynomial (M : Nat) (C : Nat -> Nat) : Polynomial Real :=
  (Finset.range (M + 1)).sum (fun k =>
    Polynomial.C (C k : Real) * Polynomial.X ^ k)

noncomputable def empiricalPolynomial
    (N M : Nat) (C : Nat -> Nat) : Polynomial Real :=
  Polynomial.C (1 / (N : Real)) * countPolynomial M C

theorem countPolynomial_coeff_zero (M : Nat) (C : Nat -> Nat) :
    (countPolynomial M C).coeff 0 = (C 0 : Real) := by
  simp [countPolynomial]

theorem countPolynomial_eval (M : Nat) (C : Nat -> Nat) (z : Real) :
    (countPolynomial M C).eval z =
      (Finset.range (M + 1)).sum (fun k => (C k : Real) * z ^ k) := by
  simp [countPolynomial, Polynomial.eval_finsetSum]

theorem natDegree_countPolynomial_le (M : Nat) (C : Nat -> Nat) :
    (countPolynomial M C).natDegree <= M := by
  unfold countPolynomial
  apply Polynomial.natDegree_sum_le_of_forall_le (Finset.range (M + 1))
    (fun k => Polynomial.C (C k : Real) * Polynomial.X ^ k)
  intro k hk
  by_cases hz : (C k : Real) = 0
  case pos =>
    simp [hz]
  case neg =>
    rw [Polynomial.natDegree_C_mul_X_pow k (C k : Real) hz]
    exact Nat.le_of_lt_succ (Finset.mem_range.mp hk)

theorem countPolynomial_ne_zero (M : Nat) (C : Nat -> Nat)
    (hC : 0 < C 0) : Not (countPolynomial M C = 0) := by
  intro h
  have hz : (C 0 : Real) = 0 := by
    simpa only [countPolynomial_coeff_zero, Polynomial.coeff_zero] using
      congrArg (fun q : Polynomial Real => q.coeff 0) h
  exact (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hC)) hz

theorem natDegree_empiricalPolynomial_le
    (N M : Nat) (C : Nat -> Nat) :
    (empiricalPolynomial N M C).natDegree <= M := by
  unfold empiricalPolynomial
  calc
    (Polynomial.C (1 / (N : Real)) * countPolynomial M C).natDegree <=
        (Polynomial.C (1 / (N : Real))).natDegree +
          (countPolynomial M C).natDegree := Polynomial.natDegree_mul_le
    _ = (countPolynomial M C).natDegree := by rw [Polynomial.natDegree_C, zero_add]
    _ <= M := natDegree_countPolynomial_le M C

theorem empiricalPolynomial_ne_zero
    (N M : Nat) (C : Nat -> Nat) (hN : 0 < N) (hC : 0 < C 0) :
    Not (empiricalPolynomial N M C = 0) := by
  have hNreal : Not ((N : Real) = 0) := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hN)
  exact mul_ne_zero (Polynomial.C_ne_zero.mpr (one_div_ne_zero hNreal))
    (countPolynomial_ne_zero M C hC)

theorem card_decodedSamplePolynomial_le
    (P : Set Nat) (N M R : Nat) (hN : 0 < N) :
    (decodedPrimeLabels R
      (empiricalPolynomial N M (sampleCount P N))).card <= M := by
  exact (card_decodedPrimeLabels_le_natDegree R
      (empiricalPolynomial N M (sampleCount P N))
      (empiricalPolynomial_ne_zero N M (sampleCount P N) hN
        (sampleCount_zero_pos P N hN))).trans
    (natDegree_empiricalPolynomial_le N M (sampleCount P N))

end PrimeFactorOscillations.PrimeClassDecoder

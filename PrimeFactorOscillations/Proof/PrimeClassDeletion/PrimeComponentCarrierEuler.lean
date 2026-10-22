/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import PrimeFactorOscillations.Proof.PrimeClassDeletion.PrimeComponentCarrierArithmetic

/-!
# Absolute Mobius weights for a multiplicative prime carrier

The squarefree inverse coefficients are summable on every admissible thin
prime class. Their local Euler series is exactly one plus the prime weight.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.PrimeClassSampling

noncomputable def classPrimeComponentAbsMobiusArithmetic
    (P : Set Nat) (sigma : Real) : ArithmeticFunction Real where
  toFun n := abs (ArithmeticFunction.moebius n : Real) * classPrimePowerWeight P sigma n
  map_zero' := by simp [classPrimePowerWeight_zero]

theorem classPrimeComponentAbsMobiusArithmetic_apply
    (P : Set Nat) (sigma : Real) (n : Nat) :
    classPrimeComponentAbsMobiusArithmetic P sigma n =
      abs (ArithmeticFunction.moebius n : Real) * classPrimePowerWeight P sigma n := rfl

theorem classPrimeComponentAbsMobiusArithmetic_nonneg
    (P : Set Nat) (sigma : Real) (n : Nat) :
    0 <= classPrimeComponentAbsMobiusArithmetic P sigma n :=
  mul_nonneg (abs_nonneg _) (classPrimePowerWeight_nonneg P sigma n)

theorem classPrimeComponentMobiusArithmetic_norm
    (P : Set Nat) (sigma : Real) (n : Nat) :
    norm (classPrimeComponentMobiusArithmetic P sigma n) =
      classPrimeComponentAbsMobiusArithmetic P sigma n := by
  rw [Real.norm_eq_abs, classPrimeComponentMobiusArithmetic_apply,
    abs_mul, abs_of_nonneg (classPrimePowerWeight_nonneg P sigma n)]
  rfl

theorem classPrimeComponentAbsMobiusArithmetic_le_weight
    (P : Set Nat) (sigma : Real) (n : Nat) :
    classPrimeComponentAbsMobiusArithmetic P sigma n <= classPrimePowerWeight P sigma n := by
  have hm : abs (ArithmeticFunction.moebius n : Real) <= 1 := by
    exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := n))
  exact (mul_le_mul_of_nonneg_right hm
    (classPrimePowerWeight_nonneg P sigma n)).trans_eq (one_mul _)

theorem classPrimeComponentAbsMobiusArithmetic_summable
    (P : Set Nat) (sigma : Real) (hs : 0 < sigma)
    (hsum : Summable (classPowerWeight P sigma)) :
    Summable (classPrimeComponentAbsMobiusArithmetic P sigma) :=
  (classPrimePowerWeight_summable P sigma hs hsum).of_nonneg_of_le
    (classPrimeComponentAbsMobiusArithmetic_nonneg P sigma)
    (classPrimeComponentAbsMobiusArithmetic_le_weight P sigma)

theorem classPrimeComponentWeightArithmetic_isMultiplicative
    (P : Set Nat) (sigma : Real) :
    (classPrimeComponentWeightArithmetic P sigma).IsMultiplicative := by
  apply ArithmeticFunction.IsMultiplicative.iff_ne_zero.mpr
  refine And.intro ?_ ?_
  . rw [classPrimeComponentWeightArithmetic_apply, classPrimePowerWeight_one]
  . intro m n hm hn hcop
    simp only [classPrimeComponentWeightArithmetic_apply, classPrimePowerWeight_mul]

theorem classPrimeComponentAbsMobiusArithmetic_isMultiplicative
    (P : Set Nat) (sigma : Real) :
    (classPrimeComponentAbsMobiusArithmetic P sigma).IsMultiplicative := by
  apply ArithmeticFunction.IsMultiplicative.iff_ne_zero.mpr
  refine And.intro ?_ ?_
  . simp [classPrimeComponentAbsMobiusArithmetic_apply, classPrimePowerWeight_one]
  . intro m n hm hn hcop
    have hmu := (ArithmeticFunction.IsMultiplicative.iff_ne_zero.mp
      ArithmeticFunction.isMultiplicative_moebius).2 hm hn hcop
    simp only [classPrimeComponentAbsMobiusArithmetic_apply,
      classPrimePowerWeight_mul, hmu, Int.cast_mul, abs_mul]
    ring

theorem classPrimePowerWeight_pow (P : Set Nat) (sigma : Real) (n k : Nat) :
    classPrimePowerWeight P sigma (n ^ k) = (classPrimePowerWeight P sigma n) ^ k := by
  induction k with
  | zero => simp [classPrimePowerWeight_one]
  | succ k ih => rw [pow_succ, classPrimePowerWeight_mul, ih, pow_succ]

theorem classPrimePowerWeight_prime
    (P : Set Nat) (sigma : Real) (p : Nat) (hp : Nat.Prime p) :
    classPrimePowerWeight P sigma p = classPowerWeight P sigma p := by
  classical
  have hsupported : classPrimePowerSupported P p <-> Membership.mem P p := by
    rw [classPrimePowerSupported_iff_primeDivisors]
    constructor
    . intro h
      exact h.2 p hp (dvd_refl p)
    . intro h
      refine And.intro hp.ne_zero ?_
      intro q hq hqd
      have heq : q = p := (Nat.prime_dvd_prime_iff_eq hq hp).mp hqd
      rw [heq]
      exact h
  by_cases h : Membership.mem P p
  . simp [classPrimePowerWeight, classPowerWeight, hsupported.mpr h, hp, h]
  . have hn : Not (classPrimePowerSupported P p) := fun hc => h (hsupported.mp hc)
    simp [classPrimePowerWeight, classPowerWeight, hn, hp, h]

theorem classPrimePowerWeight_prime_lt_one
    (P : Set Nat) (sigma : Real) (hs : 0 < sigma) (p : Nat) (hp : Nat.Prime p) :
    classPrimePowerWeight P sigma p < 1 := by
  classical
  by_cases h : classPrimePowerSupported P p
  . rw [classPrimePowerWeight, if_pos h]
    exact Real.rpow_lt_one_of_one_lt_of_neg
      (by exact_mod_cast hp.one_lt) (neg_neg_of_pos hs)
  . simp [classPrimePowerWeight, h]

theorem classPrimePowerWeight_primePower_tsum
    (P : Set Nat) (sigma : Real) (hs : 0 < sigma) (p : Nat) (hp : Nat.Prime p) :
    tsum (fun k : Nat => classPrimePowerWeight P sigma (p ^ k)) =
      1 / (1 - classPrimePowerWeight P sigma p) := by
  have hnorm : norm (classPrimePowerWeight P sigma p) < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (classPrimePowerWeight_nonneg P sigma p)]
    exact classPrimePowerWeight_prime_lt_one P sigma hs p hp
  simp_rw [classPrimePowerWeight_pow]
  simpa only [one_div] using tsum_geometric_of_norm_lt_one hnorm

theorem classPrimeComponentAbsMobiusArithmetic_primePower_tsum
    (P : Set Nat) (sigma : Real) (p : Nat) (hp : Nat.Prime p) :
    tsum (fun k : Nat => classPrimeComponentAbsMobiusArithmetic P sigma (p ^ k)) =
      1 + classPrimePowerWeight P sigma p := by
  have hzero : classPrimeComponentAbsMobiusArithmetic P sigma (p ^ 0) = 1 := by
    simp [classPrimeComponentAbsMobiusArithmetic_apply, classPrimePowerWeight_one]
  have hone : classPrimeComponentAbsMobiusArithmetic P sigma (p ^ 1) =
      classPrimePowerWeight P sigma p := by
    simp [classPrimeComponentAbsMobiusArithmetic_apply, ArithmeticFunction.moebius_apply_prime hp]
  have htail : forall k : Nat, Not (Membership.mem ({0, 1} : Finset Nat) k) ->
      classPrimeComponentAbsMobiusArithmetic P sigma (p ^ k) = 0 := by
    intro k hk
    have hk0 : Not (k = 0) := by intro h; subst k; simp at hk
    have hk1 : Not (k = 1) := by intro h; subst k; simp at hk
    rw [classPrimeComponentAbsMobiusArithmetic_apply,
      ArithmeticFunction.moebius_apply_prime_pow hp hk0, if_neg hk1]
    simp
  rw [tsum_eq_sum htail]
  simpa only [Finset.sum_insert, Finset.mem_singleton, zero_ne_one, not_false_eq_true,
    Finset.sum_singleton] using congrArg (fun x : Real => x) (by
      rw [hzero, hone] : classPrimeComponentAbsMobiusArithmetic P sigma (p ^ 0) +
        classPrimeComponentAbsMobiusArithmetic P sigma (p ^ 1) =
          1 + classPrimePowerWeight P sigma p)

end PrimeFactorOscillations.PrimeClassSampling

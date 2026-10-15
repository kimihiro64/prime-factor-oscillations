/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Lean.Elab.Tactic.Omega
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Tactic.NormNum

/-!
An elementary uniform divisor power bound, with a symbolic finite constant.
For K>=1, tau(n)^K <= (K!*2^K)^(2^K)*n. No evaluation of the huge
constant at a fixed large K is used. K=320 would give tau(n)^2 <= C*n^(1/160),
which leaves a power margin for the COMPLETE LPF source budget.
-/

set_option autoImplicit false
set_option Elab.async false

open scoped Classical

namespace PrimeFactorOscillations.LPF

def lpfDivisorPowerConstant (K : Nat) : Nat := (K.factorial * 2 ^ K) ^ (2 ^ K)

private theorem lpf_succ_le_two_pow (e : Nat) : e + 1 <= 2 ^ e := by
  induction e with
  | zero => norm_num
  | succ e ih => rw [pow_succ]; omega

theorem lpf_exponent_power_le (e K : Nat) :
    (e + 1) ^ K <= (K.factorial * 2 ^ K) * 2 ^ e := by
  calc
    _ <= (e + 1).ascFactorial K := Nat.pow_succ_le_ascFactorial (e + 1) K
    _ = K.factorial * (e + K).choose K := Nat.ascFactorial_eq_factorial_mul_choose e K
    _ <= K.factorial * 2 ^ (e + K) := Nat.mul_le_mul_left _ (Nat.choose_le_two_pow _ _)
    _ = _ := by rw [pow_add]; ring

theorem lpf_large_base_exponent_power_le (p e K : Nat) (hp : 2 ^ K <= p) :
    (e + 1) ^ K <= p ^ e := by
  calc
    _ <= (2 ^ e) ^ K := Nat.pow_le_pow_left (lpf_succ_le_two_pow e) K
    _ = (2 ^ K) ^ e := by rw [<- pow_mul, Nat.mul_comm, pow_mul]
    _ <= _ := Nat.pow_le_pow_left hp e

theorem lpf_divisors_card_pow_le (n K : Nat) (hK : 1 <= K) :
    n.divisors.card ^ K <= lpfDivisorPowerConstant K * n := by
  by_cases hn : n = 0
  . subst n
    simp [show Not (K = 0) by omega]
  . let A := K.factorial * 2 ^ K
    let S := n.primeFactors
    let B := S.filter (fun p => p < 2 ^ K)
    have hA : 1 <= A := by
      exact Nat.mul_pos K.factorial_pos (pow_pos (by decide) K)
    have hSmall : B <= Finset.range (2 ^ K) := by
      intro p hp
      exact Finset.mem_range.mpr (Finset.mem_filter.mp hp).2
    have hCard : B.card <= 2 ^ K := by
      have h := Finset.card_le_card hSmall
      simpa only [Finset.card_range] using h
    have hPoint : forall p, Membership.mem S p ->
        (n.factorization p + 1) ^ K <=
          (if p < 2 ^ K then A else 1) * p ^ n.factorization p := by
      intro p hp
      have hPrime := Nat.prime_of_mem_primeFactors hp
      by_cases hBig : 2 ^ K <= p
      . rw [ite_eq_right (not_lt.mpr hBig), one_mul]
        exact lpf_large_base_exponent_power_le p (n.factorization p) K hBig
      . rw [ite_eq_left (lt_of_not_ge hBig)]
        exact (lpf_exponent_power_le (n.factorization p) K).trans
          (Nat.mul_le_mul_left A (Nat.pow_le_pow_left hPrime.two_le _))
    have hProd : S.prod (fun p => (n.factorization p + 1) ^ K) <=
        S.prod (fun p => (if p < 2 ^ K then A else 1) * p ^ n.factorization p) := by
      exact Finset.prod_le_prod hPoint
    have hFactors : S.prod (fun p => p ^ n.factorization p) = n := by
      rw [Nat.prod_primeFactors_prod_factorization]
      exact Nat.prod_factorization_pow_eq_self hn
    have hWeights : S.prod (fun p => if p < 2 ^ K then A else 1) = A ^ B.card := by
      rw [<- Finset.prod_filter]
      simp only [Finset.prod_const]
      rfl
    rw [Finset.prod_mul_distrib, hFactors, hWeights] at hProd
    have hPower : A ^ B.card <= A ^ (2 ^ K) := Nat.pow_le_pow_right hA hCard
    have hTau : n.divisors.card ^ K = S.prod (fun p => (n.factorization p + 1) ^ K) := by
      rw [Nat.card_divisors hn, Finset.prod_pow]
    rw [hTau]
    exact hProd.trans (Nat.mul_le_mul_right n hPower)

end PrimeFactorOscillations.LPF

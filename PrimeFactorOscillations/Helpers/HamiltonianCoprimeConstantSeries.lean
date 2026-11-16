/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import PrimeFactorOscillations.Helpers.HamiltonianCoprimeConstant

/-! # The full signed logarithmic series of the coprime count constant

Opposite logarithm arguments cancel every even power before any
arithmetic estimate. Finite supported divisor summation retains the
Mobius signs and the principal compensation.
-/

set_option autoImplicit false
set_option Elab.async false

open scoped Classical

noncomputable section

namespace PrimeFactorOscillations

theorem hamiltonian_log_odd_power_series (x : Real) (hx : abs x < 1) :
    HasSum (fun j : Nat => x ^ (2 * j + 1) / ((2 * j + 1 : Nat) : Real))
      ((Real.log (1 + x) - Real.log (1 - x)) / 2) := by
  let f := fun k : Nat =>
    x ^ (k + 1) / ((k : Real) + 1) - (-x) ^ (k + 1) / ((k : Real) + 1)
  have hNeg : abs (-x) < 1 := by simpa only [abs_neg] using hx
  have hFull : HasSum f (-Real.log (1 - x) - -Real.log (1 - -x)) :=
    (Real.hasSum_pow_div_log_of_abs_lt_one hx).sub
      (Real.hasSum_pow_div_log_of_abs_lt_one hNeg)
  have hValue : -Real.log (1 - x) - -Real.log (1 - -x) =
      Real.log (1 + x) - Real.log (1 - x) := by
    simp only [sub_neg_eq_add]
    ring
  rw [hValue] at hFull
  have hEvenSum : Summable (fun j : Nat => f (2 * j)) := by
    have h := hFull.summable.comp_injective
      (i := fun j : Nat => 2 * j) (by intro a b h; change 2 * a = 2 * b at h; omega)
    simpa only [Function.comp_def] using h
  have hEven := hEvenSum.hasSum
  have hOddTerm (j : Nat) : f (2 * j + 1) = 0 := by
    dsimp only [f]
    rw [show 2 * j + 1 + 1 = 2 * (j + 1) by omega,
      pow_mul, pow_mul, neg_sq, sub_self]
  have hOdd : HasSum (fun j : Nat => f (2 * j + 1)) (0 : Real) := by
    simp_rw [hOddTerm]
    exact hasSum_zero
  have hBoth : HasSum f ((tsum (fun j : Nat => f (2 * j))) + 0) :=
    hEven.even_add_odd hOdd
  have hEq := hBoth.unique hFull
  simp only [add_zero] at hEq
  have hHalf := hEven.div_const 2
  rw [hEq] at hHalf
  convert hHalf using 1
  funext j
  have hPower : (-x) ^ (2 * j + 1) = -(x ^ (2 * j + 1)) := by
    calc
      _ = ((-x) ^ 2) ^ j * (-x) := by rw [pow_add, pow_mul, pow_one]
      _ = _ := by rw [neg_sq, pow_add, pow_mul, pow_one]; ring
  dsimp only [f]
  rw [hPower]
  push_cast
  ring

theorem hamiltonian_log_ratio_odd_series (x : Real) (hx : abs x < 1) :
    HasSum (fun j : Nat => -(x ^ (2 * j + 1)) / ((2 * j + 1 : Nat) : Real))
      (Real.log ((1 - x) / (1 + x)) / 2) := by
  have hRange := abs_lt.mp hx
  have hMinus : 0 < 1 - x := by linarith only [hRange.2]
  have hPlus : 0 < 1 + x := by linarith only [hRange.1]
  rw [Real.log_div (ne_of_gt hMinus) (ne_of_gt hPlus)]
  convert (hamiltonian_log_odd_power_series x hx).mul_left (-1) using 1
  all_goals first | (funext j; ring) | ring

def hamiltonianCoprimeDivisorEigenvalue (t : Nat) : Real :=
  if t = 1 then 0 else
    (ArithmeticFunction.moebius t : Real) / (t.totient : Real)

variable {n : Nat} [NeZero n]

theorem hamiltonian_coprime_odd_divisor_eigenvalue_small (hOdd : Odd n) (t : Nat)
    (ht : Membership.mem n.divisors t) :
    abs (hamiltonianCoprimeDivisorEigenvalue t) < 1 := by
  by_cases hOne : t = 1
  case pos => simp [hamiltonianCoprimeDivisorEigenvalue, hOne]
  case neg =>
    have hSigns := hamiltonian_coprime_odd_divisor_signs hOdd t ht hOne
    have hPhi := hSigns.2.2
    have hPhiNe : Not ((t.totient : Real) = 0) := ne_of_gt hPhi
    have hMu : abs (ArithmeticFunction.moebius t : Real) < (t.totient : Real) := by
      apply abs_lt.mpr
      constructor <;> linarith only [hSigns.1, hSigns.2.1]
    rw [hamiltonianCoprimeDivisorEigenvalue, if_neg hOne, abs_div, abs_of_pos hPhi]
    apply (mul_lt_mul_iff_of_pos_right hPhi).mp
    have hCancel : (abs (ArithmeticFunction.moebius t : Real) / (t.totient : Real)) *
        (t.totient : Real) = abs (ArithmeticFunction.moebius t : Real) := by field_simp
    rw [hCancel, one_mul]
    exact hMu

theorem hamiltonian_coprime_odd_divisor_eigenvalue_ratio (hOdd : Odd n) (t : Nat)
    (ht : Membership.mem n.divisors t) :
    (1 - hamiltonianCoprimeDivisorEigenvalue t) /
        (1 + hamiltonianCoprimeDivisorEigenvalue t) =
      hamiltonianCoprimeArithmeticRatio t := by
  by_cases hOne : t = 1
  case pos => simp [hamiltonianCoprimeDivisorEigenvalue, hamiltonianCoprimeArithmeticRatio, hOne]
  case neg =>
    have h := hamiltonian_coprime_odd_factor_ratio hOdd t ht
    simpa only [hamiltonianCoprimeDivisorEigenvalue, hamiltonianCoprimeDeterminantFactor,
      hOne, ite_false, one_mul, neg_one_mul, sub_neg_eq_add] using h

theorem hamiltonian_coprime_odd_constant_log (hOdd : Odd n) :
    Real.log (hamiltonianCoprimeArithmeticConstant n) =
      n.divisors.sum (fun t =>
        ((t.totient : Real) / 2) * Real.log (hamiltonianCoprimeArithmeticRatio t)) := by
  unfold hamiltonianCoprimeArithmeticConstant
  rw [Real.log_prod (fun t ht =>
    ne_of_gt (Real.rpow_pos_of_pos
      (hamiltonian_coprime_odd_arithmetic_ratio_positive hOdd t ht) _))]
  apply Finset.sum_congr rfl
  intro t ht
  exact Real.log_rpow (hamiltonian_coprime_odd_arithmetic_ratio_positive hOdd t ht) _

theorem hamiltonian_coprime_odd_constant_signed_series (hOdd : Odd n) :
    HasSum (fun j : Nat => n.divisors.sum (fun t =>
      -(t.totient : Real) * hamiltonianCoprimeDivisorEigenvalue t ^ (2 * j + 1) /
        ((2 * j + 1 : Nat) : Real)))
      (Real.log (hamiltonianCoprimeArithmeticConstant n)) := by
  rw [hamiltonian_coprime_odd_constant_log hOdd]
  apply hasSum_sum
  intro t ht
  have h := (hamiltonian_log_ratio_odd_series (hamiltonianCoprimeDivisorEigenvalue t)
    (hamiltonian_coprime_odd_divisor_eigenvalue_small hOdd t ht)).mul_left
      (t.totient : Real)
  rw [hamiltonian_coprime_odd_divisor_eigenvalue_ratio hOdd t ht] at h
  convert h using 1
  all_goals first | (funext j; ring) | ring


theorem hamiltonian_coprime_constant_leading_coefficient (hn : 1 < n) :
    n.divisors.sum (fun t =>
      -(t.totient : Real) * hamiltonianCoprimeDivisorEigenvalue t) = 1 := by
  have hNotOne : Not (n = 1) := by omega
  have hTotal :
      n.divisors.sum (fun t => (ArithmeticFunction.moebius t : Real)) = 0 := by
    have h := congrArg (fun f : ArithmeticFunction Real => f n)
      (ArithmeticFunction.coe_moebius_mul_coe_zeta (R := Real))
    simpa only [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.intCoe_apply,
      ArithmeticFunction.one_apply, hNotOne, ite_false] using h
  have hOneDiv : Membership.mem n.divisors 1 :=
    Nat.mem_divisors.mpr (And.intro (one_dvd n) (NeZero.ne n))
  have hDelta : n.divisors.sum (fun t => if t = 1 then (1 : Real) else 0) = 1 := by
    simp [hOneDiv]
  have hTerm (t : Nat) (ht : Membership.mem n.divisors t) :
      -(t.totient : Real) * hamiltonianCoprimeDivisorEigenvalue t =
        (if t = 1 then (1 : Real) else 0) - (ArithmeticFunction.moebius t : Real) := by
    by_cases hOne : t = 1
    case pos =>
      simp [hOne, hamiltonianCoprimeDivisorEigenvalue, ArithmeticFunction.moebius_apply_one]
    case neg =>
      have htPos := Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp ht).1 (NeZero.pos n)
      have hPhi : Not ((t.totient : Real) = 0) := by
        exact_mod_cast (Nat.totient_pos.mpr htPos).ne'
      simp only [hamiltonianCoprimeDivisorEigenvalue, hOne, ite_false]
      field_simp
      <;> ring
  calc
    _ = n.divisors.sum (fun t =>
        (if t = 1 then (1 : Real) else 0) - (ArithmeticFunction.moebius t : Real)) := by
      apply Finset.sum_congr rfl
      intro t ht
      exact hTerm t ht
    _ = _ := by rw [Finset.sum_sub_distrib, hDelta, hTotal, sub_zero]

end PrimeFactorOscillations

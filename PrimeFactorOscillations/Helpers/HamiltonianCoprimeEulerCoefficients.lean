/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianCoprimeConstantSeries
import PrimeFactorOscillations.Helpers.LPFSingularEuler

/-! # Exact finite Euler products for the signed constant coefficients

The previously proved multiplicative rational Ramanujan functions are
used before division or prime-factor regrouping. All prime-power
exponents and supported divisors are retained.
-/

set_option autoImplicit false
set_option Elab.async false

open scoped Classical

noncomputable section

namespace PrimeFactorOscillations

def hamiltonianCoprimeEulerWeight (j : Nat) : ArithmeticFunction Complex :=
  (LPF.lpfRationalFunction.ppow (2 * j)).pmul (LPF.lpfRamanujanFunction 1)

def hamiltonianCoprimeEulerSum (j : Nat) : ArithmeticFunction Complex :=
  hamiltonianCoprimeEulerWeight j * (ArithmeticFunction.zeta : ArithmeticFunction Complex)

theorem hamiltonian_coprime_euler_weight_multiplicative (j : Nat) :
    (hamiltonianCoprimeEulerWeight j).IsMultiplicative :=
  ArithmeticFunction.IsMultiplicative.pmul
    LPF.lpfRationalFunction_multiplicative.ppow (LPF.lpfRamanujanFunction_multiplicative 1)

theorem hamiltonian_coprime_euler_sum_multiplicative (j : Nat) :
    (hamiltonianCoprimeEulerSum j).IsMultiplicative :=
  ArithmeticFunction.IsMultiplicative.mul (hamiltonian_coprime_euler_weight_multiplicative j)
    ArithmeticFunction.isMultiplicative_zeta.natCast

theorem hamiltonian_coprime_euler_weight_apply (j q : Nat) (hj : 0 < j) (hq : 0 < q) :
    hamiltonianCoprimeEulerWeight j q =
      (ArithmeticFunction.moebius q : Complex) / (q.totient : Complex) ^ (2 * j) := by
  letI : NeZero q := NeZero.mk (ne_of_gt hq)
  have hRam : LPF.lpfRamanujanFunction 1 q = (ArithmeticFunction.moebius q : Complex) := by
    rw [LPF.lpfRamanujanFunction_eq_sum]
    simpa using LPF.lpfRamanujanSum_divisors (q := q) 1
  have hMuRange := abs_le.mp (ArithmeticFunction.abs_moebius_le_one (n := q))
  have hMuCases : ArithmeticFunction.moebius q = -1 \/
      ArithmeticFunction.moebius q = 0 \/ ArithmeticFunction.moebius q = 1 := by omega
  have hMuPower : (ArithmeticFunction.moebius q : Complex) ^ (2 * j) *
      (ArithmeticFunction.moebius q : Complex) = (ArithmeticFunction.moebius q : Complex) := by
    rcases hMuCases with hMu | hMu | hMu <;> simp [hMu, pow_mul]
  rw [hamiltonianCoprimeEulerWeight, ArithmeticFunction.pmul_apply,
    ArithmeticFunction.ppow_apply (by omega : 0 < 2 * j),
    LPF.lpfRationalFunction_apply, hRam]
  unfold LPF.lpfRationalCoefficient
  rw [div_pow]
  calc
    _ = ((ArithmeticFunction.moebius q : Complex) ^ (2 * j) *
        (ArithmeticFunction.moebius q : Complex)) /
          (q.totient : Complex) ^ (2 * j) := by ring
    _ = _ := by rw [hMuPower]

theorem hamiltonian_coprime_euler_sum_apply (j n : Nat) :
    hamiltonianCoprimeEulerSum j n =
      n.divisors.sum (fun q => hamiltonianCoprimeEulerWeight j q) :=
  ArithmeticFunction.coe_mul_zeta_apply

theorem hamiltonian_coprime_euler_prime_power (j p a : Nat) (hj : 0 < j)
    (hp : Nat.Prime p) (ha : 0 < a) :
    hamiltonianCoprimeEulerSum j (p ^ a) =
      1 - 1 / ((p : Complex) - 1) ^ (2 * j) := by
  rw [hamiltonian_coprime_euler_sum_apply, Nat.sum_divisors_prime_pow hp]
  have hSubset : ({0, 1} : Finset Nat) <= Finset.range (a + 1) := by
    intro k hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    apply Finset.mem_range.mpr
    omega
  have hTail (k : Nat) (hk : Membership.mem (Finset.range (a + 1)) k)
      (hNot : Not (Membership.mem ({0, 1} : Finset Nat) k)) :
      hamiltonianCoprimeEulerWeight j (p ^ k) = 0 := by
    have hk2 : 2 <= k := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hNot
      omega
    rw [hamiltonian_coprime_euler_weight_apply j (p ^ k) hj (pow_pos hp.pos _),
      ArithmeticFunction.moebius_apply_prime_pow hp (by omega),
      if_neg (by omega : Not (k = 1))]
    simp
  calc
    _ = ({0, 1} : Finset Nat).sum (fun k => hamiltonianCoprimeEulerWeight j (p ^ k)) :=
      (Finset.sum_subset hSubset hTail).symm
    _ = hamiltonianCoprimeEulerWeight j 1 + hamiltonianCoprimeEulerWeight j p := by simp
    _ = _ := by
      rw [hamiltonian_coprime_euler_weight_apply j 1 hj (by norm_num),
        hamiltonian_coprime_euler_weight_apply j p hj hp.pos]
      simp only [ArithmeticFunction.moebius_apply_one, Int.cast_one, Nat.totient_one,
        Nat.cast_one, one_pow, div_one, ArithmeticFunction.moebius_apply_prime hp,
        Int.cast_neg, Nat.totient_prime hp]
      rw [Nat.cast_sub hp.one_lt.le, Nat.cast_one]
      ring

theorem hamiltonian_coprime_euler_finite_product (j n : Nat) (hj : 0 < j) (hn : 0 < n) :
    hamiltonianCoprimeEulerSum j n =
      n.primeFactors.prod (fun p => 1 - 1 / ((p : Complex) - 1) ^ (2 * j)) := by
  have hFactor := ArithmeticFunction.IsMultiplicative.multiplicative_factorization
    (hamiltonianCoprimeEulerSum j) (hamiltonian_coprime_euler_sum_multiplicative j)
    (ne_of_gt hn)
  change hamiltonianCoprimeEulerSum j n =
    n.factorization.support.prod
      (fun p => hamiltonianCoprimeEulerSum j (p ^ n.factorization p)) at hFactor
  rw [Nat.support_factorization] at hFactor
  rw [hFactor]
  apply Finset.prod_congr rfl
  intro p hp
  have hPrime := Nat.prime_of_mem_primeFactors hp
  have hSupport : Membership.mem n.factorization.support p := by
    simpa only [Nat.support_factorization] using hp
  have hExp : 0 < n.factorization p := by
    have hNonzero := Finsupp.mem_support_iff.mp hSupport
    omega
  exact hamiltonian_coprime_euler_prime_power j p _ hj hPrime hExp

theorem hamiltonian_coprime_moebius_totient_euler_product
    (j n : Nat) (hj : 0 < j) (hn : 0 < n) :
    n.divisors.sum (fun q =>
      (ArithmeticFunction.moebius q : Real) / (q.totient : Real) ^ (2 * j)) =
      n.primeFactors.prod (fun p => 1 - 1 / ((p : Real) - 1) ^ (2 * j)) := by
  have hComplex :
      n.divisors.sum (fun q =>
        (ArithmeticFunction.moebius q : Complex) / (q.totient : Complex) ^ (2 * j)) =
      n.primeFactors.prod (fun p => 1 - 1 / ((p : Complex) - 1) ^ (2 * j)) := by
    rw [<- hamiltonian_coprime_euler_finite_product j n hj hn,
      hamiltonian_coprime_euler_sum_apply]
    apply Finset.sum_congr rfl
    intro q hq
    exact (hamiltonian_coprime_euler_weight_apply j q hj
      (Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp hq).1 hn)).symm
  apply Complex.ofReal_injective
  push_cast
  exact hComplex


theorem hamiltonian_moebius_odd_power (q j : Nat) :
    (ArithmeticFunction.moebius q : Real) ^ (2 * j + 1) =
      (ArithmeticFunction.moebius q : Real) := by
  have hRange := abs_le.mp (ArithmeticFunction.abs_moebius_le_one (n := q))
  have hCases : ArithmeticFunction.moebius q = -1 \/
      ArithmeticFunction.moebius q = 0 \/ ArithmeticFunction.moebius q = 1 := by omega
  rcases hCases with h | h | h <;> simp [h, pow_add, pow_mul]

theorem hamiltonian_coprime_signed_divisor_coefficient
    (j n : Nat) [NeZero n] :
    n.divisors.sum (fun t =>
      -(t.totient : Real) * hamiltonianCoprimeDivisorEigenvalue t ^ (2 * j + 1)) =
      1 - n.divisors.sum (fun t =>
        (ArithmeticFunction.moebius t : Real) / (t.totient : Real) ^ (2 * j)) := by
  have hTerm (t : Nat) (ht : Membership.mem n.divisors t) :
      -(t.totient : Real) * hamiltonianCoprimeDivisorEigenvalue t ^ (2 * j + 1) =
        (if t = 1 then (1 : Real) else 0) -
          (ArithmeticFunction.moebius t : Real) / (t.totient : Real) ^ (2 * j) := by
    by_cases hOne : t = 1
    case pos =>
      simp [hOne, hamiltonianCoprimeDivisorEigenvalue, pow_add]
    case neg =>
      have htPos := Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp ht).1 (NeZero.pos n)
      have hPhi : Not ((t.totient : Real) = 0) := by
        exact_mod_cast (Nat.totient_pos.mpr htPos).ne'
      simp only [hamiltonianCoprimeDivisorEigenvalue, hOne, ite_false, zero_sub]
      rw [div_pow, hamiltonian_moebius_odd_power, pow_succ]
      field_simp
      <;> ring
  have hOneDiv : Membership.mem n.divisors 1 :=
    Nat.mem_divisors.mpr (And.intro (one_dvd n) (NeZero.ne n))
  have hDelta : n.divisors.sum (fun t => if t = 1 then (1 : Real) else 0) = 1 := by
    simp [hOneDiv]
  calc
    _ = n.divisors.sum (fun t => (if t = 1 then (1 : Real) else 0) -
        (ArithmeticFunction.moebius t : Real) / (t.totient : Real) ^ (2 * j)) := by
      apply Finset.sum_congr rfl
      intro t ht
      exact hTerm t ht
    _ = _ := by rw [Finset.sum_sub_distrib, hDelta]

theorem hamiltonian_coprime_constant_higher_coefficient
    (j n : Nat) [NeZero n] (hj : 0 < j) :
    n.divisors.sum (fun t =>
      -(t.totient : Real) * hamiltonianCoprimeDivisorEigenvalue t ^ (2 * j + 1) /
        ((2 * j + 1 : Nat) : Real)) =
      (1 - n.primeFactors.prod (fun p =>
        1 - 1 / ((p : Real) - 1) ^ (2 * j))) / ((2 * j + 1 : Nat) : Real) := by
  rw [<- Finset.sum_div, hamiltonian_coprime_signed_divisor_coefficient,
    hamiltonian_coprime_moebius_totient_euler_product j n hj (NeZero.pos n)]

theorem hamiltonian_coprime_odd_constant_prime_product_series
    (n : Nat) [NeZero n] (hOdd : Odd n) (hn : 1 < n) :
    HasSum (fun j : Nat => if j = 0 then (1 : Real) else
      (1 - n.primeFactors.prod (fun p =>
        1 - 1 / ((p : Real) - 1) ^ (2 * j))) / ((2 * j + 1 : Nat) : Real))
      (Real.log (hamiltonianCoprimeArithmeticConstant n)) := by
  convert hamiltonian_coprime_odd_constant_signed_series hOdd using 1
  funext j
  by_cases hZero : j = 0
  case pos =>
    subst j
    simpa only [ite_true, Nat.mul_zero, Nat.zero_add, pow_one, Nat.cast_one, div_one] using
      (hamiltonian_coprime_constant_leading_coefficient (n := n) hn).symm
  case neg =>
    have hj : 0 < j := by omega
    simpa only [hZero, ite_false] using
      (hamiltonian_coprime_constant_higher_coefficient j n hj).symm

end PrimeFactorOscillations

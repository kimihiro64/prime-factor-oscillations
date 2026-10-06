/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import PrimeFactorOscillations.Helpers.LcmPowerLocal

/-!
# The Mobius-defined generalized divisor sum

Constructs the actual arithmetic function and its prime-power factorization.
These finite identities will connect the local correction bounds to the
modified-LCM family, before any asymptotic estimate is applied.
-/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace PrimeFactorOscillations
open ArithmeticFunction

def sigmaRealPower (k : Real) (hk : 0 < k) : ArithmeticFunction Real where
  toFun n := ((sigma 1 n : Nat) : Real) ^ k
  map_zero' := by simp [Real.zero_rpow hk.ne']

theorem sigmaRealPower_isMultiplicative (k : Real) (hk : 0 < k) :
    (sigmaRealPower k hk).IsMultiplicative := by
  refine And.intro ?_ ?_
  . change ((sigma 1 1 : Nat) : Real) ^ k = 1
    rw [isMultiplicative_sigma.map_one, Nat.cast_one, Real.one_rpow]
  . intro m n hmn
    change ((sigma 1 (m * n) : Nat) : Real) ^ k =
      ((sigma 1 m : Nat) : Real) ^ k * ((sigma 1 n : Nat) : Real) ^ k
    rw [isMultiplicative_sigma.map_mul_of_coprime hmn, Nat.cast_mul,
      Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)]

def lcmDivisorSum (k : Real) (hk : 0 < k) : ArithmeticFunction Real :=
  (moebius : ArithmeticFunction Real) * sigmaRealPower k hk

theorem lcmDivisorSum_isMultiplicative (k : Real) (hk : 0 < k) :
    (lcmDivisorSum k hk).IsMultiplicative :=
  isMultiplicative_moebius.intCast.mul (sigmaRealPower_isMultiplicative k hk)

theorem lcmDivisorSum_mul_zeta (k : Real) (hk : 0 < k) :
    lcmDivisorSum k hk * (zeta : ArithmeticFunction Real) = sigmaRealPower k hk := by
  calc
    _ = sigmaRealPower k hk *
        ((moebius : ArithmeticFunction Real) * (zeta : ArithmeticFunction Real)) := by
      unfold lcmDivisorSum
      ac_rfl
    _ = _ := by rw [coe_moebius_mul_coe_zeta, mul_one]

theorem sum_lcmDivisorSum_divisors (k : Real) (hk : 0 < k) (n : Nat) :
    n.divisors.sum (fun d => lcmDivisorSum k hk d) = ((sigma 1 n : Nat) : Real) ^ k := by
  rw [<- coe_mul_zeta_apply, lcmDivisorSum_mul_zeta]
  rfl

theorem lcmDivisorSum_prime_pow_succ (k : Real) (hk : 0 < k)
    {p : Nat} (hp : Nat.Prime p) (a : Nat) :
    lcmDivisorSum k hk (p ^ (a + 1)) =
      ((sigma 1 (p ^ (a + 1)) : Nat) : Real) ^ k -
        ((sigma 1 (p ^ a) : Nat) : Real) ^ k := by
  have hPrev := sum_lcmDivisorSum_divisors k hk (p ^ a)
  have hNext := sum_lcmDivisorSum_divisors k hk (p ^ (a + 1))
  rw [Nat.sum_divisors_prime_pow hp] at hPrev
  rw [Nat.sum_divisors_prime_pow hp, Finset.sum_range_succ] at hNext
  linarith only [hPrev, hNext]

theorem lcmDivisorSum_eq_primeFactors_product (k : Real) (hk : 0 < k)
    (n : Nat) (hn : Not (n = 0)) :
    lcmDivisorSum k hk n = n.primeFactors.prod (fun p =>
      ((sigma 1 (p ^ n.factorization p) : Nat) : Real) ^ k -
        ((sigma 1 (p ^ (n.factorization p - 1)) : Nat) : Real) ^ k) := by
  rw [IsMultiplicative.multiplicative_factorization
    (lcmDivisorSum k hk) (lcmDivisorSum_isMultiplicative k hk) hn]
  change n.factorization.support.prod
    (fun p => lcmDivisorSum k hk (p ^ n.factorization p)) = _
  rw [Nat.support_factorization]
  apply Finset.prod_congr rfl
  intro p hp
  have hPrime : Nat.Prime p := (Nat.mem_primeFactors.mp hp).1
  have hSupport : Membership.mem n.factorization.support p := by
    rwa [Nat.support_factorization]
  have ha : Not (n.factorization p = 0) := Finsupp.mem_support_iff.mp hSupport
  have hPred : n.factorization p - 1 + 1 = n.factorization p := by omega
  simpa only [hPred] using
    lcmDivisorSum_prime_pow_succ k hk hPrime (n.factorization p - 1)

theorem lcmDivisorSum_prime_pow_succ_pos (k : Real) (hk : 0 < k)
    {p : Nat} (hp : Nat.Prime p) (a : Nat) :
    0 < lcmDivisorSum k hk (p ^ (a + 1)) := by
  have hSigma :
      sigma 1 (p ^ (a + 1)) = sigma 1 (p ^ a) + p ^ (a + 1) := by
    calc
      _ = (Finset.range ((a + 1) + 1)).sum (fun j => p ^ j) :=
        sigma_one_apply_prime_pow hp
      _ = (Finset.range (a + 1)).sum (fun j => p ^ j) + p ^ (a + 1) :=
        Finset.sum_range_succ _ _
      _ = _ := by rw [sigma_one_apply_prime_pow hp]
  have hNat : sigma 1 (p ^ a) < sigma 1 (p ^ (a + 1)) := by
    rw [hSigma]
    exact Nat.lt_add_of_pos_right (pow_pos hp.pos _)
  have hReal : ((sigma 1 (p ^ a) : Nat) : Real) <
      ((sigma 1 (p ^ (a + 1)) : Nat) : Real) := by exact_mod_cast hNat
  rw [lcmDivisorSum_prime_pow_succ k hk hp a]
  exact sub_pos.mpr (Real.rpow_lt_rpow (Nat.cast_nonneg _) hReal hk)

/-- This is the paper's actual Mobius divisor sum, including n=0. -/
theorem lcmDivisorSum_eq_moebius_sum (k : Real) (hk : 0 < k) (n : Nat) :
    lcmDivisorSum k hk n = n.divisors.sum (fun d =>
      (moebius (n / d) : Real) * ((sigma 1 d : Nat) : Real) ^ k) := by
  calc
    _ = (sigmaRealPower k hk * (moebius : ArithmeticFunction Real)) n := by
      exact congrArg (fun f : ArithmeticFunction Real => f n) (mul_comm _ _)
    _ = n.divisors.sum (fun d =>
        sigmaRealPower k hk d * (moebius (n / d) : Real)) := by
      rw [mul_apply]
      exact Nat.sum_divisorsAntidiagonal
        (fun a b => sigmaRealPower k hk a * (moebius b : Real))
    _ = _ := by
      apply Finset.sum_congr rfl
      intro d hd
      change ((sigma 1 d : Nat) : Real) ^ k * (moebius (n / d) : Real) = _
      ring

theorem sigma_prime_pow_real_normalization {p : Nat} (hp : Nat.Prime p) (a : Nat) :
    ((sigma 1 (p ^ a) : Nat) : Real) =
      (p : Real) ^ a / (1 - 1 / (p : Real)) *
        (1 - (p : Real) ^ (-((a : Real) + 1))) := by
  have hpPos : (0 : Real) < p := by exact_mod_cast hp.pos
  have hpOne : (1 : Real) < p := by exact_mod_cast hp.one_lt
  have hDen : 0 < 1 - 1 / (p : Real) := by
    have h := (div_lt_one hpPos).mpr hpOne
    linarith
  have hU : (p : Real) ^ (-((a : Real) + 1)) = Inv.inv ((p : Real) ^ (a + 1)) := by
    rw [Real.rpow_neg hpPos.le,
      show (a : Real) + 1 = ((a + 1 : Nat) : Real) by simp,
      Real.rpow_natCast]
  have hSum : ((sigma 1 (p ^ a) : Nat) : Real) =
      ((p : Real) ^ (a + 1) - 1) / ((p : Real) - 1) := by
    rw [sigma_one_apply_prime_pow hp, Nat.cast_sum]
    simp only [Nat.cast_pow]
    exact geom_sum_eq (by linarith) (a + 1)
  rw [hSum, hU, pow_succ]
  field_simp [hpPos.ne', (pow_pos hpPos a).ne', (sub_pos.mpr hpOne).ne', hDen.ne']

theorem lcmDivisorSum_prime_pow_factor (k : Real) (hk : 0 < k)
    {p : Nat} (hp : Nat.Prime p) (a : Nat) :
    lcmDivisorSum k hk (p ^ (a + 1)) =
      ((p : Real) ^ (a + 1) / (1 - 1 / (p : Real))) ^ k *
        (1 - (p : Real) ^ (-k)) * lcmPowerLocalFactor (p : Real) (a + 1) k := by
  have hpPos : (0 : Real) < p := by exact_mod_cast hp.pos
  have hpOne : (1 : Real) < p := by exact_mod_cast hp.one_lt
  have hDen : 0 < 1 - 1 / (p : Real) := by
    have h := (div_lt_one hpPos).mpr hpOne
    linarith
  let S : Real := (p : Real) ^ (a + 1) / (1 - 1 / (p : Real))
  let u : Real := (p : Real) ^ (-(((a + 1 : Nat) : Real) + 1))
  let t : Real := (p : Real) ^ (-((a + 1 : Nat) : Real))
  have hS : 0 < S := by dsimp [S]; positivity
  have hU : 0 <= 1 - u := by
    have hPower := Real.rpow_le_rpow_of_exponent_le hpOne.le
      (show -(((a + 1 : Nat) : Real) + 1) <= 0 by
        have ha : (0 : Real) <= (a + 1 : Nat) := Nat.cast_nonneg _
        linarith)
    simp only [Real.rpow_zero] at hPower
    dsimp [u]
    linarith
  have hT : 0 <= 1 - t := by
    have hPower := Real.rpow_le_rpow_of_exponent_le hpOne.le
      (show -((a + 1 : Nat) : Real) <= 0 from neg_nonpos.mpr (Nat.cast_nonneg _))
    simp only [Real.rpow_zero] at hPower
    dsimp [t]
    linarith
  have hV : 0 < 1 - (p : Real) ^ (-k) := by
    have hPower := Real.rpow_lt_rpow_of_exponent_lt hpOne (show -k < 0 by linarith)
    simp only [Real.rpow_zero] at hPower
    linarith
  have hCurrent : ((sigma 1 (p ^ (a + 1)) : Nat) : Real) = S * (1 - u) :=
    sigma_prime_pow_real_normalization hp (a + 1)
  have hPrevious : ((sigma 1 (p ^ a) : Nat) : Real) = (S / (p : Real)) * (1 - t) := by
    rw [sigma_prime_pow_real_normalization hp a]
    dsimp [S, t]
    simp only [Nat.cast_add, Nat.cast_one]
    rw [pow_succ]
    field_simp [hpPos.ne', hDen.ne']
  have hExpr : lcmDivisorSum k hk (p ^ (a + 1)) =
      S ^ k * ((1 - u) ^ k - (p : Real) ^ (-k) * (1 - t) ^ k) := by
    rw [lcmDivisorSum_prime_pow_succ k hk hp a, hCurrent, hPrevious,
      Real.mul_rpow hS.le hU, Real.mul_rpow (div_nonneg hS.le hpPos.le) hT,
      Real.div_rpow hS.le hpPos.le, Real.rpow_neg hpPos.le]
    ring
  rw [hExpr]
  change S ^ k * ((1 - u) ^ k - (p : Real) ^ (-k) * (1 - t) ^ k) =
    S ^ k * (1 - (p : Real) ^ (-k)) *
      (((1 - u) ^ k - (p : Real) ^ (-k) * (1 - t) ^ k) / (1 - (p : Real) ^ (-k)))
  field_simp [hV.ne']

theorem lcmDivisorSum_eq_normalized_product (k : Real) (hk : 0 < k)
    (n : Nat) (hn : Not (n = 0)) :
    lcmDivisorSum k hk n = n.primeFactors.prod (fun p =>
      ((p : Real) ^ n.factorization p / (1 - 1 / (p : Real))) ^ k *
        (1 - (p : Real) ^ (-k)) *
          lcmPowerLocalFactor (p : Real) (n.factorization p) k) := by
  rw [IsMultiplicative.multiplicative_factorization
    (lcmDivisorSum k hk) (lcmDivisorSum_isMultiplicative k hk) hn]
  change n.factorization.support.prod
    (fun p => lcmDivisorSum k hk (p ^ n.factorization p)) = _
  rw [Nat.support_factorization]
  apply Finset.prod_congr rfl
  intro p hp
  have hPrime : Nat.Prime p := (Nat.mem_primeFactors.mp hp).1
  have hSupport : Membership.mem n.factorization.support p := by
    rwa [Nat.support_factorization]
  have ha : Not (n.factorization p = 0) := Finsupp.mem_support_iff.mp hSupport
  have hPred : n.factorization p - 1 + 1 = n.factorization p := by omega
  simpa only [hPred] using
    lcmDivisorSum_prime_pow_factor k hk hPrime (n.factorization p - 1)

theorem sum_primeFactors_factorization_log (n : Nat) (hn : Not (n = 0)) :
    n.primeFactors.sum (fun p => (n.factorization p : Real) * Real.log (p : Real)) =
      Real.log (n : Real) := by
  have hNat := Nat.factorization_prod_pow_eq_self hn
  change n.factorization.support.prod (fun p => p ^ n.factorization p) = n at hNat
  rw [Nat.support_factorization] at hNat
  have hReal : n.primeFactors.prod (fun p => (p : Real) ^ n.factorization p) = (n : Real) := by
    exact_mod_cast hNat
  have hLog := congrArg Real.log hReal
  have hNonzero (p : Nat) (hp : Membership.mem n.primeFactors p) :
      Not ((p : Real) ^ n.factorization p = 0) :=
    (pow_pos (show (0 : Real) < (p : Real) by
      exact_mod_cast (Nat.mem_primeFactors.mp hp).1.pos) _).ne'
  rw [Real.log_prod (s := n.primeFactors)
    (f := fun p : Nat => (p : Real) ^ n.factorization p) hNonzero] at hLog
  simpa only [Real.log_pow] using hLog

theorem lcmPowerLocalFactor_prime_pos (k : Real) (hk : 0 < k)
    {p : Nat} (hp : Nat.Prime p) (a : Nat) (ha : 1 <= a) :
    0 < lcmPowerLocalFactor (p : Real) a k := by
  have hpPos : (0 : Real) < p := by exact_mod_cast hp.pos
  have hpOne : (1 : Real) < p := by exact_mod_cast hp.one_lt
  have hDen : 0 < 1 - 1 / (p : Real) := by
    have h := (div_lt_one hpPos).mpr hpOne
    linarith
  have hV : 0 < 1 - (p : Real) ^ (-k) := by
    have hPower := Real.rpow_lt_rpow_of_exponent_lt hpOne (show -k < 0 by linarith)
    simp only [Real.rpow_zero] at hPower
    linarith
  have hPred : a - 1 + 1 = a := by omega
  have hFactor := lcmDivisorSum_prime_pow_factor k hk hp (a - 1)
  have hPos := lcmDivisorSum_prime_pow_succ_pos k hk hp (a - 1)
  simp only [hPred] at hFactor hPos
  rw [hFactor] at hPos
  by_contra hNot
  have hNonpos := mul_nonpos_of_nonneg_of_nonpos
    (show 0 <= ((p : Real) ^ a / (1 - 1 / (p : Real))) ^ k *
      (1 - (p : Real) ^ (-k)) by positivity) (le_of_not_gt hNot)
  linarith only [hPos, hNonpos]

theorem lcmDivisorSum_pos (k : Real) (hk : 0 < k)
    (n : Nat) (hn : Not (n = 0)) : 0 < lcmDivisorSum k hk n := by
  rw [lcmDivisorSum_eq_normalized_product k hk n hn]
  apply Finset.prod_pos
  intro p hp
  have hPrime : Nat.Prime p := (Nat.mem_primeFactors.mp hp).1
  have hpPos : (0 : Real) < p := by exact_mod_cast hPrime.pos
  have hpOne : (1 : Real) < p := by exact_mod_cast hPrime.one_lt
  have hSupport : Membership.mem n.factorization.support p := by rwa [Nat.support_factorization]
  have ha : 1 <= n.factorization p := by
    have h := Finsupp.mem_support_iff.mp hSupport
    omega
  have hDen : 0 < 1 - 1 / (p : Real) := by
    have h := (div_lt_one hpPos).mpr hpOne
    linarith
  have hV : 0 < 1 - (p : Real) ^ (-k) := by
    have hPower := Real.rpow_lt_rpow_of_exponent_lt hpOne (show -k < 0 by linarith)
    simp only [Real.rpow_zero] at hPower
    linarith
  exact mul_pos (mul_pos (Real.rpow_pos_of_pos (by positivity) _) hV)
    (lcmPowerLocalFactor_prime_pos k hk hPrime _ ha)

theorem lcmDivisorSum_log_identity (k : Real) (hk : 0 < k)
    (n : Nat) (hn : Not (n = 0)) :
    Real.log (lcmDivisorSum k hk n) =
      k * Real.log (n : Real) -
        k * n.primeFactors.sum (fun p => Real.log (1 - 1 / (p : Real))) +
        n.primeFactors.sum (fun p => Real.log (1 - (p : Real) ^ (-k))) +
        n.primeFactors.sum (fun p =>
          Real.log (lcmPowerLocalFactor (p : Real) (n.factorization p) k)) := by
  let f : Nat -> Real := fun p =>
    ((p : Real) ^ n.factorization p / (1 - 1 / (p : Real))) ^ k *
      (1 - (p : Real) ^ (-k)) *
        lcmPowerLocalFactor (p : Real) (n.factorization p) k
  have hLocal (p : Nat) (hp : Membership.mem n.primeFactors p) :
      0 < f p /\
        Real.log (f p) =
          k * ((n.factorization p : Real) * Real.log (p : Real) -
            Real.log (1 - 1 / (p : Real))) +
          Real.log (1 - (p : Real) ^ (-k)) +
          Real.log (lcmPowerLocalFactor (p : Real) (n.factorization p) k) := by
    have hPrime : Nat.Prime p := (Nat.mem_primeFactors.mp hp).1
    have hpPos : (0 : Real) < p := by exact_mod_cast hPrime.pos
    have hpOne : (1 : Real) < p := by exact_mod_cast hPrime.one_lt
    have hSupport : Membership.mem n.factorization.support p := by rwa [Nat.support_factorization]
    have ha : 1 <= n.factorization p := by
      have h := Finsupp.mem_support_iff.mp hSupport
      omega
    have hDen : 0 < 1 - 1 / (p : Real) := by
      have h := (div_lt_one hpPos).mpr hpOne
      linarith
    have hS : 0 < (p : Real) ^ n.factorization p / (1 - 1 / (p : Real)) := by positivity
    have hV : 0 < 1 - (p : Real) ^ (-k) := by
      have hPower := Real.rpow_lt_rpow_of_exponent_lt hpOne (show -k < 0 by linarith)
      simp only [Real.rpow_zero] at hPower
      linarith
    have hC := lcmPowerLocalFactor_prime_pos k hk hPrime _ ha
    have hSP := Real.rpow_pos_of_pos hS k
    refine And.intro (mul_pos (mul_pos hSP hV) hC) ?_
    dsimp [f]
    rw [Real.log_mul (mul_pos hSP hV).ne' hC.ne',
      Real.log_mul hSP.ne' hV.ne', Real.log_rpow hS,
      Real.log_div (pow_pos hpPos _).ne' hDen.ne', Real.log_pow]
  have hProduct : lcmDivisorSum k hk n = n.primeFactors.prod f :=
    lcmDivisorSum_eq_normalized_product k hk n hn
  rw [hProduct, Real.log_prod (fun p hp => (hLocal p hp).1.ne')]
  have hSum := Finset.sum_congr rfl (fun p hp => (hLocal p hp).2)
  rw [hSum]
  simp only [mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib, <- Finset.mul_sum,
    sum_primeFactors_factorization_log n hn]


def lcmExponentDefect (n p : Nat) : Real :=
  (p : Real) ^ (-((n.factorization p : Real) + 1))

def lcmDefectSum (n : Nat) : Real :=
  n.primeFactors.sum (lcmExponentDefect n)

def lcmDefectRemainder (n : Nat) : Real :=
  4 * n.primeFactors.sum (fun p => lcmExponentDefect n p / (p : Real)) +
    32 * n.primeFactors.sum (fun p => (lcmExponentDefect n p) ^ 2)

/-- A lower bound for the actual Mobius-defined divisor sum, retaining
the full finite Euler factors and all exponent-dependent losses. -/
theorem lcmDivisorSum_log_lower
    (k : Real) (hk : 0 < k) (hkOne : 1 <= k) (hkTwo : k <= 2)
    (n : Nat) (hn : Not (n = 0))
    (hSmall : forall p, Membership.mem n.primeFactors p ->
      lcmExponentDefect n p <= 1 / 8) :
    k * Real.log (n : Real) -
      k * n.primeFactors.sum (fun p => Real.log (1 - 1 / (p : Real))) +
      n.primeFactors.sum (fun p => Real.log (1 - (p : Real) ^ (-k))) -
      k * lcmDefectSum n - lcmDefectRemainder n <=
        Real.log (lcmDivisorSum k hk n) := by
  have hpTwo (p : Nat) (hp : Membership.mem n.primeFactors p) : (2 : Real) <= p := by
    exact_mod_cast (Nat.mem_primeFactors.mp hp).1.two_le
  have hLocal := lcmPowerLocal_product_log_lower n.primeFactors
    (fun p : Nat => (p : Real)) n.factorization k hkOne hkTwo hpTwo hSmall
  have hNonzero (p : Nat) (hp : Membership.mem n.primeFactors p) :
      Not (lcmPowerLocalFactor (p : Real) (n.factorization p) k = 0) :=
    (lcmPowerLocalFactor_log_lower (p : Real) (hpTwo p hp)
      (n.factorization p) k hkOne hkTwo (hSmall p hp)).1.ne'
  rw [Real.log_prod hNonzero] at hLocal
  rw [lcmDivisorSum_log_identity k hk n hn]
  have hNamed :
      -k * lcmDefectSum n -
        4 * n.primeFactors.sum (fun p => lcmExponentDefect n p / (p : Real)) -
        32 * n.primeFactors.sum (fun p => (lcmExponentDefect n p) ^ 2) <=
          n.primeFactors.sum (fun p =>
            Real.log (lcmPowerLocalFactor (p : Real) (n.factorization p) k)) := hLocal
  unfold lcmDefectRemainder
  linarith only [hNamed]

end PrimeFactorOscillations

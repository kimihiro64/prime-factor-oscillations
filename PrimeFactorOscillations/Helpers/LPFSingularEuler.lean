/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.LPFSingularSeries

/-!
# Euler product for the actual singular coefficient

The additive Ramanujan sum equals the exact Mobius/divisor-weight Dirichlet
convolution. Pointwise division and pointwise squaring retain the zero-modulus
convention. The resulting coefficient is multiplicative, its higher prime
powers vanish, and its absolutely convergent prime-product limit is proved.
Positivity of that limit is a separate arithmetic consumer.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.LPF

noncomputable def lpfDivisorWeight (t : Nat) : ArithmeticFunction Complex where
  toFun d := if Dvd.dvd d t then (d : Complex) else 0
  map_zero' := by simp

theorem lpfDivisorWeight_apply (t d : Nat) :
    lpfDivisorWeight t d = if Dvd.dvd d t then (d : Complex) else 0 := rfl

theorem lpfDivisorWeight_multiplicative (t : Nat) :
    (lpfDivisorWeight t).IsMultiplicative := by
  apply ArithmeticFunction.IsMultiplicative.iff_ne_zero.mpr
  refine And.intro (by simp [lpfDivisorWeight]) ?_
  intro m n _ _ hCop
  by_cases hm : Dvd.dvd m t
  next =>
    by_cases hn : Dvd.dvd n t
    next =>
      have hmn := hCop.mul_dvd_of_dvd_of_dvd hm hn
      simp [lpfDivisorWeight, hm, hn, hmn, Nat.cast_mul]
    next =>
      have hmn : Not (Dvd.dvd (m * n) t) := by
        intro h
        exact hn (dvd_trans (dvd_mul_left n m) h)
      simp [lpfDivisorWeight, hm, hn, hmn]
  next =>
    have hmn : Not (Dvd.dvd (m * n) t) := by
      intro h
      exact hm (dvd_trans (dvd_mul_right m n) h)
    simp [lpfDivisorWeight, hm, hmn]

noncomputable def lpfRamanujanFunction (t : Nat) : ArithmeticFunction Complex :=
  (ArithmeticFunction.moebius : ArithmeticFunction Complex) * lpfDivisorWeight t

theorem lpfRamanujanFunction_multiplicative (t : Nat) :
    (lpfRamanujanFunction t).IsMultiplicative :=
  ArithmeticFunction.IsMultiplicative.mul
    ArithmeticFunction.isMultiplicative_moebius.intCast (lpfDivisorWeight_multiplicative t)

theorem lpfRamanujanFunction_eq_sum {q : Nat} [NeZero q] (t : Nat) :
    lpfRamanujanFunction t q = lpfRamanujanSum (q := q) t := by
  have hGcd : Not (Nat.gcd q t = 0) := by
    intro h
    exact (NeZero.ne q) (Nat.gcd_eq_zero_iff.mp h).1
  have hSet : q.divisors.filter (fun d => Dvd.dvd d t) = (Nat.gcd q t).divisors := by
    apply Finset.ext
    intro d
    simp only [Finset.mem_filter, Nat.mem_divisors]
    constructor
    next =>
      intro h
      exact And.intro (Nat.dvd_gcd h.1.1 h.2) hGcd
    next =>
      intro h
      have hd := Nat.dvd_gcd_iff.mp h.1
      exact And.intro (And.intro hd.1 (NeZero.ne q)) hd.2
  unfold lpfRamanujanFunction
  rw [ArithmeticFunction.mul_apply]
  rw [Nat.sum_divisorsAntidiagonal'
    (fun a b => ((ArithmeticFunction.moebius : ArithmeticFunction Complex) a) * lpfDivisorWeight t b)]
  simp only [ArithmeticFunction.intCoe_apply, lpfDivisorWeight_apply, mul_ite, mul_zero]
  rw [<- Finset.sum_filter, hSet, lpfRamanujanSum_divisors]
  apply Finset.sum_congr rfl
  intro d _
  ring

noncomputable def lpfTotientFunction : ArithmeticFunction Complex where
  toFun q := (q.totient : Complex)
  map_zero' := by simp

theorem lpfTotientFunction_multiplicative : lpfTotientFunction.IsMultiplicative := by
  apply ArithmeticFunction.IsMultiplicative.iff_ne_zero.mpr
  refine And.intro (by simp [lpfTotientFunction]) ?_
  intro m n _ _ hCop
  change ((m * n).totient : Complex) = (m.totient : Complex) * (n.totient : Complex)
  rw [Nat.totient_mul hCop, Nat.cast_mul]

noncomputable def lpfRationalFunction : ArithmeticFunction Complex :=
  (ArithmeticFunction.moebius : ArithmeticFunction Complex).pdiv lpfTotientFunction

theorem lpfRationalFunction_apply (q : Nat) : lpfRationalFunction q = lpfRationalCoefficient q := by
  rw [lpfRationalFunction, ArithmeticFunction.pdiv_apply, ArithmeticFunction.intCoe_apply]
  rfl

theorem lpfRationalFunction_multiplicative : lpfRationalFunction.IsMultiplicative :=
  ArithmeticFunction.IsMultiplicative.pdiv
    ArithmeticFunction.isMultiplicative_moebius.intCast lpfTotientFunction_multiplicative

noncomputable def lpfSingularFunction (t : Nat) : ArithmeticFunction Complex :=
  (lpfRationalFunction.ppow 2).pmul (lpfRamanujanFunction t)

theorem lpfSingularFunction_multiplicative (t : Nat) :
    (lpfSingularFunction t).IsMultiplicative :=
  ArithmeticFunction.IsMultiplicative.pmul
    lpfRationalFunction_multiplicative.ppow (lpfRamanujanFunction_multiplicative t)

theorem lpfSingularFunction_apply (q t : Nat) :
    lpfSingularFunction t q = lpfRamanujanCoefficient q t := by
  by_cases hq : q = 0
  next =>
    subst q
    rw [lpfRamanujanCoefficient_zero]
    simp
  next =>
    letI : NeZero q := NeZero.mk hq
    rw [lpfSingularFunction, ArithmeticFunction.pmul_apply,
      ArithmeticFunction.ppow_apply (by decide : 0 < 2), lpfRationalFunction_apply,
      lpfRamanujanFunction_eq_sum, lpfRamanujanCoefficient_eq]

theorem lpfRamanujanCoefficient_multiplicative (m n t : Nat) (hCop : Nat.Coprime m n) :
    lpfRamanujanCoefficient (m * n) t = lpfRamanujanCoefficient m t * lpfRamanujanCoefficient n t := by
  simpa only [lpfSingularFunction_apply] using
    (lpfSingularFunction_multiplicative t).map_mul_of_coprime hCop

theorem lpfRamanujanCoefficient_prime_power_zero (p e t : Nat)
    (hp : Nat.Prime p) (he : 2 <= e) : lpfRamanujanCoefficient (p ^ e) t = 0 := by
  have hPow : Not (p ^ e = 0) := pow_ne_zero e hp.ne_zero
  letI : NeZero (p ^ e) := NeZero.mk hPow
  have hMu := ArithmeticFunction.moebius_apply_prime_pow hp (by omega : Not (e = 0))
  rw [ite_eq_right (by omega : Not (e = 1))] at hMu
  rw [lpfRamanujanCoefficient_eq]
  simp [lpfRationalCoefficient, hMu]

theorem lpfRamanujanSum_prime {p : Nat} [NeZero p] (hp : Nat.Prime p) (t : Nat) :
    lpfRamanujanSum (q := p) t = if Dvd.dvd p t then (p : Complex) - 1 else -1 := by
  rw [lpfRamanujanSum_divisor_mask, hp.divisors]
  rw [Finset.sum_insert (by simp [Ne.symm hp.ne_one]), Finset.sum_singleton]
  by_cases hpt : Dvd.dvd p t <;>
    simp [hpt, hp.ne_zero, ArithmeticFunction.moebius_apply_prime hp, sub_eq_add_neg]

theorem lpfRamanujanCoefficient_prime (p t : Nat) (hp : Nat.Prime p) :
    lpfRamanujanCoefficient p t =
      (if Dvd.dvd p t then (p : Complex) - 1 else -1) / ((p : Complex) - 1) ^ 2 := by
  letI : NeZero p := NeZero.mk hp.ne_zero
  have hCast : ((p - 1 : Nat) : Complex) = (p : Complex) - 1 := by
    rw [Nat.cast_sub hp.one_lt.le, Nat.cast_one]
  have hDen : Not ((p : Complex) - 1 = 0) := by
    apply sub_ne_zero.mpr
    exact_mod_cast hp.ne_one
  rw [lpfRamanujanCoefficient_eq, lpfRamanujanSum_prime hp, lpfRationalCoefficient,
    ArithmeticFunction.moebius_apply_prime hp, Nat.totient_prime hp, hCast]
  by_cases hpt : Dvd.dvd p t <;> simp only [hpt, ite_true, ite_false] <;>
    field_simp <;> ring

theorem lpfRamanujanCoefficient_prime_power_tsum (p t : Nat) (hp : Nat.Prime p) :
    tsum (fun e : Nat => lpfRamanujanCoefficient (p ^ e) t) =
      1 + lpfRamanujanCoefficient p t := by
  calc
    _ = Finset.sum ({0, 1} : Finset Nat) (fun e => lpfRamanujanCoefficient (p ^ e) t) := by
      apply tsum_eq_sum
      intro e he
      have hE : 2 <= e := by simp only [Finset.mem_insert, Finset.mem_singleton] at he; omega
      exact lpfRamanujanCoefficient_prime_power_zero p e t hp hE
    _ = _ := by simp [lpfRamanujanCoefficient_one]

theorem lpfRamanujanCoefficient_norm_summable (t : Nat) (ht : 0 < t) :
    Summable (fun q => norm (lpfRamanujanCoefficient q t)) := by
  let S : Real := Finset.sum t.divisors (fun d => (d : Real))
  have hRes (q : Nat) : lpfDivisorResonance t q <= S := by
    apply Finset.sum_le_sum
    intro d _
    split_ifs <;> simp <;> positivity
  have hDom (q : Nat) : norm (lpfRamanujanCoefficient q t) <=
      4 * S / (q : Real) ^ (3 / 2 : Real) := by
    by_cases hq : q = 0
    next => subst q; simp [lpfRamanujanCoefficient_zero]
    next =>
      exact (norm_lpfRamanujanCoefficient_le q t (Nat.pos_of_ne_zero hq) ht).trans
        (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (hRes q) (by norm_num))
          (Real.rpow_nonneg (Nat.cast_nonneg q) _))
  have hBase : Summable (fun q : Nat => 1 / (q : Real) ^ (3 / 2 : Real)) := by
    simpa only [one_div] using
      (Real.summable_nat_rpow_inv.mpr (by norm_num : (1 : Real) < 3 / 2))
  have hMajorant : Summable (fun q : Nat => 4 * S / (q : Real) ^ (3 / 2 : Real)) := by
    simpa only [div_eq_mul_inv, mul_one, one_mul] using hBase.mul_left (4 * S)
  exact Summable.of_nonneg_of_le (fun q => norm_nonneg _) hDom hMajorant

theorem lpfSingularSeries_prime_product_limit (t : Nat) (ht : 0 < t) :
    Filter.Tendsto (fun R : Nat => Finset.prod (Nat.primesBelow R)
      (fun p => 1 + lpfRamanujanCoefficient p t)) Filter.atTop (nhds (lpfSingularSeries t)) := by
  have hNorm : Summable (fun q => norm (lpfSingularFunction t q)) := by
    simpa only [lpfSingularFunction_apply] using lpfRamanujanCoefficient_norm_summable t ht
  have hEuler := (lpfSingularFunction_multiplicative t).eulerProduct hNorm
  simp_rw [lpfSingularFunction_apply] at hEuler
  apply hEuler.congr'
  apply Filter.Eventually.of_forall
  intro R
  apply Finset.prod_congr rfl
  intro p hp
  exact lpfRamanujanCoefficient_prime_power_tsum p t (Nat.mem_primesBelow.mp hp).2

end PrimeFactorOscillations.LPF

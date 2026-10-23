/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.NumberTheory.ArithmeticFunction.Moebius

/-!
# Mobius exclusion and the least prime factor

For a prime divisor p of a nonzero natural n, the product R of the prime
factors of n below p records every exclusion needed for p to be the least
factor. The divisor sum of mu over R is the least-factor indicator. Multiplying
each divisor by p gives the corresponding signed expansion in the full moduli.

These are exact finite identities. They impose no cutoff on the moduli and
assert no averaged cancellation.
-/

namespace ArithmeticFunction

/-- The complete Mobius exclusion sum detects the least prime owner. -/
theorem sum_moebius_primeFactors_lt (n p : Nat) (hn0 : Not (n = 0))
    (hp : Nat.Prime p) (hpn : Dvd.dvd p n) :
    Finset.sum ((n.primeFactors.filter (fun q => q < p)).prod (fun q => q)).divisors
      (fun d => moebius d) = if n.minFac = p then (1 : Int) else 0 := by
  rw [<- coe_mul_zeta_apply, moebius_mul_coe_zeta]
  change (if (n.primeFactors.filter (fun q => q < p)).prod (fun q => q) = 1
    then (1 : Int) else 0) = if n.minFac = p then 1 else 0
  have hle : n.minFac <= p := Nat.minFac_le_of_dvd hp.two_le hpn
  by_cases hmin : n.minFac = p
  case pos =>
    have hempty : n.primeFactors.filter (fun q => q < p) = {} := by
      apply Finset.filter_eq_empty_iff.mpr
      intro q hq
      have hdata := Nat.mem_primeFactors.mp hq
      have hlow := Nat.minFac_le_of_dvd hdata.1.two_le hdata.2.1
      rw [hmin] at hlow
      exact Nat.not_lt_of_ge hlow
    simp [hempty, hmin]
  case neg =>
    have hn1 : Not (n = 1) := by
      intro h
      apply hp.not_dvd_one
      simpa only [h] using hpn
    have hlp : Nat.Prime n.minFac := Nat.minFac_prime hn1
    have hlt : n.minFac < p := lt_of_le_of_ne hle hmin
    have hdiv : Dvd.dvd n.minFac
        ((n.primeFactors.filter (fun q => q < p)).prod (fun q => q)) :=
      Finset.dvd_prod_of_mem (fun q : Nat => q) (by
        apply Finset.mem_filter.mpr
        exact And.intro
          (Nat.mem_primeFactors.mpr (And.intro hlp (And.intro (Nat.minFac_dvd n) hn0))) hlt)
    have hprod : Not ((n.primeFactors.filter (fun q => q < p)).prod (fun q => q) = 1) := by
      intro h
      apply hlp.not_dvd_one
      simpa only [h] using hdiv
    simp [hmin, hprod]

/-- Keeping the full product modulus gives the signed least-owner expansion. -/
theorem neg_sum_moebius_mul_primeFactors_lt (n p : Nat) (hn0 : Not (n = 0))
    (hp : Nat.Prime p) (hpn : Dvd.dvd p n) :
    -Finset.sum ((n.primeFactors.filter (fun q => q < p)).prod (fun q => q)).divisors
      (fun d => moebius (p * d)) = if n.minFac = p then (1 : Int) else 0 := by
  have hcop : Nat.Coprime p
      ((n.primeFactors.filter (fun q => q < p)).prod (fun q => q)) := by
    apply Nat.coprime_prod_right_iff.mpr
    intro q hq
    have hmem := Finset.mem_filter.mp hq
    have hprime := (Nat.mem_primeFactors.mp hmem.1).1
    apply hp.coprime_iff_not_dvd.mpr
    intro hd
    exact Nat.not_le_of_gt hmem.2 (Nat.le_of_dvd hprime.pos hd)
  have hterm : forall d, Membership.mem
      ((n.primeFactors.filter (fun q => q < p)).prod (fun q => q)).divisors d ->
      moebius (p * d) = -moebius d := by
    intro d hd
    have hpd := Nat.Coprime.of_dvd_right (Nat.mem_divisors.mp hd).1 hcop
    rw [isMultiplicative_moebius.map_mul_of_coprime hpd, moebius_apply_prime hp]
    simp
  calc
    -Finset.sum ((n.primeFactors.filter (fun q => q < p)).prod (fun q => q)).divisors
        (fun d => moebius (p * d)) =
        -Finset.sum ((n.primeFactors.filter (fun q => q < p)).prod (fun q => q)).divisors
          (fun d => -moebius d) := by
            congr 1
            exact Finset.sum_congr rfl hterm
    _ = Finset.sum ((n.primeFactors.filter (fun q => q < p)).prod (fun q => q)).divisors
          (fun d => moebius d) := by simp only [Finset.sum_neg_distrib, neg_neg]
    _ = if n.minFac = p then (1 : Int) else 0 :=
      sum_moebius_primeFactors_lt n p hn0 hp hpn


/-- A proper multiple first owned by p lies at or beyond the square of p. -/
theorem prime_owner_square_le (n p : Nat)
    (hpn : Dvd.dvd p n) (hproper : p < n) (howner : n.minFac = p) :
    p * p <= n := by
  choose m hm using hpn
  have hm2 : 2 <= m := by
    by_contra h
    have hm1 : m <= 1 := by omega
    have hnle : n <= p := by
      rw [hm]
      simpa using Nat.mul_le_mul_left p hm1
    omega
  have hmn : Dvd.dvd m n := by
    apply Exists.intro p
    simpa only [Nat.mul_comm] using hm
  have hmin := Nat.minFac_le_of_dvd hm2 hmn
  rw [howner] at hmin
  calc
    p * p <= p * m := Nat.mul_le_mul_left p hmin
    _ = n := hm.symm

/-- All earlier-wave overlaps cancel the new p-wave before its square. -/
theorem sum_moebius_primeFactors_lt_eq_zero_before_square (n p : Nat)
    (hn0 : Not (n = 0)) (hp : Nat.Prime p) (hpn : Dvd.dvd p n)
    (hproper : p < n) (hbefore : n < p * p) :
    Finset.sum ((n.primeFactors.filter (fun q => q < p)).prod (fun q => q)).divisors
      (fun d => moebius d) = (0 : Int) := by
  have howner : Not (n.minFac = p) := by
    intro heq
    exact Nat.not_lt_of_ge (prime_owner_square_le n p hpn hproper heq) hbefore
  rw [sum_moebius_primeFactors_lt n p hn0 hp hpn]
  simp only [howner, ite_false]

/-- The full signed product-modulus packet has the same exact cancellation. -/
theorem neg_sum_moebius_mul_primeFactors_lt_eq_zero_before_square (n p : Nat)
    (hn0 : Not (n = 0)) (hp : Nat.Prime p) (hpn : Dvd.dvd p n)
    (hproper : p < n) (hbefore : n < p * p) :
    -Finset.sum ((n.primeFactors.filter (fun q => q < p)).prod (fun q => q)).divisors
      (fun d => moebius (p * d)) = (0 : Int) := by
  have howner : Not (n.minFac = p) := by
    intro heq
    exact Nat.not_lt_of_ge (prime_owner_square_le n p hpn hproper heq) hbefore
  rw [neg_sum_moebius_mul_primeFactors_lt n p hn0 hp hpn]
  simp only [howner, ite_false]

/-- At the square of a prime, no earlier prime owns the return. -/
theorem prime_square_minFac (p : Nat) (hp : Nat.Prime p) :
    (p * p).minFac = p := by
  have hfour : 2 * 2 <= p * p := Nat.mul_le_mul hp.two_le hp.two_le
  have hn1 : Not (p * p = 1) := by omega
  have hqprime := Nat.minFac_prime hn1
  have hqdiv := Nat.minFac_dvd (p * p)
  have hqp : Dvd.dvd (p * p).minFac p := by
    cases hqprime.dvd_mul.mp hqdiv with
    | inl h => exact h
    | inr h => exact h
  cases (Nat.dvd_prime hp).mp hqp with
  | inl h => exact False.elim (hqprime.ne_one h)
  | inr h => exact h

end ArithmeticFunction

/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.OrderOfElement

/-!
# Fermat carriers of nested dyadic divisibility clocks

Every divisor r greater than two of 2^(2^j)+1 gives the same base-two
order 2^(j+1), even when r is composite. A selected prime factor therefore
detects exactly this dyadic exponent clock along the Mersenne values
2^n-1. Different labels give different selected prime carriers.
These clocks are nested; they are not independent prime-index events.
-/

set_option autoImplicit false
set_option Elab.async false

namespace Nat

/-- The exact order uses only the Fermat relation and r greater than two. -/
theorem fermat_divisor_order (j r : Nat) (hr : 2 < r)
    (hd : Dvd.dvd r (2 ^ (2 ^ j) + 1)) :
    orderOf (2 : ZMod r) = 2 ^ (j + 1) := by
  have : Fact (2 < r) := Fact.mk hr
  have hzero := (ZMod.natCast_eq_zero_iff (2 ^ (2 ^ j) + 1) r).mpr hd
  have hneg : (2 : ZMod r) ^ (2 ^ j) = -1 := by
    apply eq_neg_iff_add_eq_zero.mpr
    simpa only [Nat.cast_add, Nat.cast_pow, Nat.cast_one, Nat.cast_ofNat] using hzero
  apply orderOf_eq_prime_pow
  { rw [hneg]
    exact ZMod.neg_one_ne_one }
  { rw [pow_succ, pow_mul, hneg, neg_one_sq] }

/-- A Fermat divisor is a clock on the exponent, including exponent zero. -/
theorem fermat_divisor_mersenne_iff (j r n : Nat) (hr : 2 < r)
    (hd : Dvd.dvd r (2 ^ (2 ^ j) + 1)) :
    Dvd.dvd r (2 ^ n - 1) <-> Dvd.dvd (2 ^ (j + 1)) n := by
  calc
    Dvd.dvd r (2 ^ n - 1) <-> ((2 ^ n - 1 : Nat) : ZMod r) = 0 :=
      (ZMod.natCast_eq_zero_iff (2 ^ n - 1) r).symm
    _ <-> (2 : ZMod r) ^ n = 1 := by
      rw [Nat.cast_sub Nat.one_le_two_pow, Nat.cast_pow, Nat.cast_one,
        Nat.cast_ofNat, sub_eq_zero]
    _ <-> Dvd.dvd (2 ^ (j + 1)) n := by
      rw [<- orderOf_dvd_iff_pow_eq_one, fermat_divisor_order j r hr hd]

theorem prime_factor_fermat_two_lt (j r : Nat) (hr : Prime r)
    (hd : Dvd.dvd r (2 ^ (2 ^ j) + 1)) : 2 < r := by
  have hodd : Odd (2 ^ (2 ^ j) + 1) :=
    (even_two.pow_of_ne_zero (pow_ne_zero j (by decide : Not ((2 : Nat) = 0)))).add_one
  exact lt_of_le_of_ne hr.two_le (hodd.ne_two_of_dvd_nat hd).symm

/-- All prime factors of one Fermat number have the same exponent clock. -/
theorem prime_factor_fermat_mersenne_iff (j r n : Nat) (hr : Prime r)
    (hd : Dvd.dvd r (2 ^ (2 ^ j) + 1)) :
    Dvd.dvd r (2 ^ n - 1) <-> Dvd.dvd (2 ^ (j + 1)) n :=
  fermat_divisor_mersenne_iff j r n (prime_factor_fermat_two_lt j r hr hd) hd

/-- A deterministic prime carrier, without assuming the Fermat number prime. -/
def fermatPrimeCarrier (j : Nat) : Nat := (2 ^ (2 ^ j) + 1).minFac

theorem fermatPrimeCarrier_prime (j : Nat) : Prime (fermatPrimeCarrier j) := by
  have hpos : 0 < 2 ^ (2 ^ j) := Nat.pow_pos (by decide)
  exact Nat.minFac_prime (ne_of_gt (Nat.succ_lt_succ hpos))

theorem fermatPrimeCarrier_dvd (j : Nat) :
    Dvd.dvd (fermatPrimeCarrier j) (2 ^ (2 ^ j) + 1) :=
  Nat.minFac_dvd _

theorem fermatPrimeCarrier_two_lt (j : Nat) : 2 < fermatPrimeCarrier j :=
  prime_factor_fermat_two_lt j _ (fermatPrimeCarrier_prime j) (fermatPrimeCarrier_dvd j)

theorem fermatPrimeCarrier_order (j : Nat) :
    orderOf (2 : ZMod (fermatPrimeCarrier j)) = 2 ^ (j + 1) :=
  fermat_divisor_order j _ (fermatPrimeCarrier_two_lt j) (fermatPrimeCarrier_dvd j)

theorem fermatPrimeCarrier_mersenne_iff (j n : Nat) :
    Dvd.dvd (fermatPrimeCarrier j) (2 ^ n - 1) <-> Dvd.dvd (2 ^ (j + 1)) n :=
  fermat_divisor_mersenne_iff j _ n (fermatPrimeCarrier_two_lt j)
    (fermatPrimeCarrier_dvd j)

/-- Distinct dyadic order labels force distinct selected carrier primes. -/
theorem fermatPrimeCarrier_injective : Function.Injective fermatPrimeCarrier := by
  intro j k heq
  have horder := congrArg (fun r : Nat => orderOf (2 : ZMod r)) heq
  have hpow : 2 ^ (j + 1) = 2 ^ (k + 1) :=
    (fermatPrimeCarrier_order j).symm.trans (horder.trans (fermatPrimeCarrier_order k))
  exact Nat.add_right_cancel ((Nat.pow_right_injective (by decide : 2 <= 2)) hpow)

/-- The first Fermat carrier supplies the ordinary index-prime-two event. -/
theorem fermatPrimeCarrier_zero : fermatPrimeCarrier 0 = 3 := by
  have hp := fermatPrimeCarrier_prime 0
  have hd : Dvd.dvd (fermatPrimeCarrier 0) 3 := by
    simpa only [pow_zero, pow_one] using fermatPrimeCarrier_dvd 0
  exact (prime_dvd_prime_iff_eq hp (by decide)).mp hd

end Nat

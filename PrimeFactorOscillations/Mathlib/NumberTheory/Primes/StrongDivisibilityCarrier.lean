/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Data.Nat.Prime.Basic

/-!
# Prime-index carriers in strongly divisible sequences

Any nonunit divisor at a prime index of a normalized strongly divisible
sequence detects exactly the multiples of that index. Fibonacci values at
indices at least three provide deterministic, distinct prime carriers.
The finite marked observable is ordered by index labels, not carrier size.
-/

set_option autoImplicit false
set_option Elab.async false

namespace Nat

/-- A nonunit divisor at a prime index detects that index's divisibility clock. -/
theorem strongDivisibility_prime_index_dvd_iff (A : Nat -> Nat)
    (hone : A 1 = 1)
    (hgcd : forall m n, Nat.gcd (A m) (A n) = A (Nat.gcd m n))
    (l c n : Nat) (hl : Prime l) (hc : Not (c = 1)) (hcl : Dvd.dvd c (A l)) :
    Dvd.dvd c (A n) <-> Dvd.dvd l n := by
  constructor
  { intro hcn
    by_cases hln : Dvd.dvd l n
    { exact hln }
    have hcop : Nat.Coprime l n := hl.coprime_iff_not_dvd.mpr hln
    have hboth := Nat.dvd_gcd hcl hcn
    rw [hgcd l n, hcop.gcd_eq_one, hone] at hboth
    exact False.elim (hc (Nat.dvd_one.mp hboth)) }
  { intro hln
    have hdiv := Nat.gcd_dvd_right (A l) (A n)
    rw [hgcd l n, Nat.gcd_eq_left_iff_dvd.mpr hln] at hdiv
    exact dvd_trans hcl hdiv }

/-- The Fibonacci value at any index at least three exceeds one. -/
theorem one_lt_fib_of_three_le (l : Nat) (hl : 3 <= l) :
    1 < fib l := by
  have htwo : 2 < l := lt_of_lt_of_le (by decide : 2 < 3) hl
  simpa only [fib_two] using (fib_lt_fib (m := 2) (by decide)).mpr htwo

/-- A deterministic prime factor of the Fibonacci value at the label. -/
def fibonacciPrimeCarrier (l : Nat) : Nat := (fib l).minFac

theorem fibonacciPrimeCarrier_prime (l : Nat) (hl : 3 <= l) :
    Prime (fibonacciPrimeCarrier l) :=
  Nat.minFac_prime (ne_of_gt (one_lt_fib_of_three_le l hl))

theorem fibonacciPrimeCarrier_dvd (l : Nat) :
    Dvd.dvd (fibonacciPrimeCarrier l) (fib l) :=
  Nat.minFac_dvd (fib l)

/-- Every prime factor, not just the selected one, has the prime index as entry point. -/
theorem prime_dvd_fib_prime_index_iff (l c n : Nat) (hl : Prime l)
    (hc : Prime c) (hcl : Dvd.dvd c (fib l)) :
    Dvd.dvd c (fib n) <-> Dvd.dvd l n :=
  strongDivisibility_prime_index_dvd_iff fib (by simp)
    (fun m n => (fib_gcd m n).symm) l c n hl (ne_of_gt hc.one_lt) hcl

theorem fibonacciPrimeCarrier_dvd_iff (l n : Nat) (hl : Prime l) (hl3 : 3 <= l) :
    Dvd.dvd (fibonacciPrimeCarrier l) (fib n) <-> Dvd.dvd l n :=
  prime_dvd_fib_prime_index_iff l _ n hl (fibonacciPrimeCarrier_prime l hl3)
    (fibonacciPrimeCarrier_dvd l)

/-- Different admissible prime labels have different selected carrier primes. -/
theorem fibonacciPrimeCarrier_injective_on_primes (l m : Nat)
    (hl : Prime l) (hm : Prime m) (hl3 : 3 <= l) (_hm3 : 3 <= m)
    (heq : fibonacciPrimeCarrier l = fibonacciPrimeCarrier m) : l = m := by
  have hdiv : Dvd.dvd l m := (fibonacciPrimeCarrier_dvd_iff l m hl hl3).mp (by
    rw [heq]
    exact fibonacciPrimeCarrier_dvd m)
  exact (prime_dvd_prime_iff_eq hl hm).mp hdiv

/-- Exact equality of finite marked-factor counts, including the index zero. -/
theorem fibonacci_marked_count_eq (s : Finset Nat)
    (hs : forall l, Membership.mem s l -> And (Prime l) (3 <= l)) (n : Nat) :
    (s.filter (fun l => Dvd.dvd (fibonacciPrimeCarrier l) (fib n))).card =
      (s.filter (fun l => Dvd.dvd l n)).card := by
  classical
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro l hl
  exact fibonacciPrimeCarrier_dvd_iff l n (hs l hl).1 (hs l hl).2

/-- The entire finite joint observable is transported pointwise, with arbitrary marks. -/
theorem fibonacci_marked_product_eq {M : Type*} [CommMonoid M] (s : Finset Nat)
    (hs : forall l, Membership.mem s l -> And (Prime l) (3 <= l))
    (n : Nat) (z : Nat -> M) :
    s.prod (fun l => if Dvd.dvd (fibonacciPrimeCarrier l) (fib n) then z l else 1) =
      s.prod (fun l => if Dvd.dvd l n then z l else 1) := by
  classical
  apply Finset.prod_congr rfl
  intro l hl
  simp only [fibonacciPrimeCarrier_dvd_iff l n (hs l hl).1 (hs l hl).2]

end Nat

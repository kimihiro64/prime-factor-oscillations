/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import Lean.Elab.Tactic.Omega
import Mathlib.Data.Nat.Prime.Basic

/-!
# Weighted geometry of four odd primes

Beyond the exceptional prime three, four increasing primes have weighted
span at least twelve. Equality is precisely one of the two admissible
four-prime patterns with successive gaps (2,4,2) and (4,2,4).
-/

set_option autoImplicit false
set_option Elab.async false

namespace Nat

theorem Prime.mod_three_ne_zero_of_three_lt {p : Nat}
    (hp : Nat.Prime p) (hthree : 3 < p) : Not (p % 3 = 0) := by
  intro hmod
  have hd : Dvd.dvd 3 p := Nat.dvd_of_mod_eq_zero hmod
  have he := (hp.dvd_iff_eq (by decide : Not (3 = 1))).mp hd
  omega

theorem no_three_large_primes_in_two_step (p q r : Nat)
    (hp : Nat.Prime p) (hq : Nat.Prime q) (hr : Nat.Prime r)
    (hthree : 3 < p) (hpq : q = p + 2) (hqr : r = q + 2) : False := by
  have hm0 := hp.mod_three_ne_zero_of_three_lt hthree
  have hm1 := hq.mod_three_ne_zero_of_three_lt (by omega)
  have hm2 := hr.mod_three_ne_zero_of_three_lt (by omega)
  omega

theorem prime_quadruplet_weighted_span (p q r s : Nat)
    (hp : Nat.Prime p) (hq : Nat.Prime q) (hr : Nat.Prime r) (hs : Nat.Prime s)
    (hthree : 3 < p) (hpq : p < q) (hqr : q < r) (hrs : r < s) :
    p + q + 12 <= r + s := by
  have ho0 := hp.eq_two_or_odd
  have ho1 := hq.eq_two_or_odd
  have ho2 := hr.eq_two_or_odd
  have ho3 := hs.eq_two_or_odd
  have hleft : Not (q = p + 2 /\ r = q + 2) := by
    intro h
    exact no_three_large_primes_in_two_step p q r hp hq hr hthree h.1 h.2
  have hright : Not (r = q + 2 /\ s = r + 2) := by
    intro h
    exact no_three_large_primes_in_two_step q r s hq hr hs (by omega) h.1 h.2
  omega

theorem prime_quadruplet_weighted_span_eq_twelve_iff (p q r s : Nat)
    (hp : Nat.Prime p) (hq : Nat.Prime q) (hr : Nat.Prime r) (hs : Nat.Prime s)
    (hthree : 3 < p) (hpq : p < q) (hqr : q < r) (hrs : r < s) :
    r + s = p + q + 12 <->
      (q = p + 2 /\ r = p + 6 /\ s = p + 8) \/
        (q = p + 4 /\ r = p + 6 /\ s = p + 10) := by
  have ho0 := hp.eq_two_or_odd
  have ho1 := hq.eq_two_or_odd
  have ho2 := hr.eq_two_or_odd
  have ho3 := hs.eq_two_or_odd
  have hleft : Not (q = p + 2 /\ r = q + 2) := by
    intro h
    exact no_three_large_primes_in_two_step p q r hp hq hr hthree h.1 h.2
  have hright : Not (r = q + 2 /\ s = r + 2) := by
    intro h
    exact no_three_large_primes_in_two_step q r s hq hr hs (by omega) h.1 h.2
  omega

end Nat

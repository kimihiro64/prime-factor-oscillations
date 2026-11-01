/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.FiniteFieldNativeEndpointDivisors

/-!
# Positive prime-output certificates for unrestricted native lower rows

Distinct lower primes in a square lower row divide the opposite gaps.
Except for the explicitly excluded lower prime 2, this gives a positive
three-prime equation. A lower endpoint cutoff makes its coefficients range
over a fixed finite set, without imposing a short-gap condition.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.FiniteFieldIntegerSignature

theorem native_lower_square_cross_positive_output (n h m k : Nat)
    (hn : Nat.Prime n) (hnh : Nat.Prime (n + h))
    (hm : Nat.Prime m) (hmk : Nat.Prime (m + k))
    (hh : 0 < h) (hk : 0 < k) (hn2 : 2 < n) (hm2 : 2 < m)
    (hne : Not (n = m)) (hs : IsSquare (h * k * n * m)) :
    exists a b : Nat, And (0 < a) (And (0 < b) (And (1 < a * b)
      (And (h = m * a) (And (k = n * b)
        ((a * b - 1) * n + (n + h) = a * (m + k)))))) := by
  have hcop : Nat.Coprime m n := (Nat.coprime_primes hm hn).mpr (by omega)
  have hmn : Not (Dvd.dvd m n) := hm.coprime_iff_not_dvd.mp hcop
  have hnm : Not (Dvd.dvd n m) := hn.coprime_iff_not_dvd.mp hcop.symm
  have hs' : IsSquare (k * h * m * n) := by
    simpa only [mul_assoc, mul_comm, mul_left_comm] using hs
  have hmh : Dvd.dvd m h :=
    (hm.dvd_mul.mp
      ((native_square_cross_rows_endpoint_divisors n h m k hm hmk hk).1 hs)).resolve_right hmn
  have hnk : Dvd.dvd n k :=
    (hn.dvd_mul.mp
      ((native_square_cross_rows_endpoint_divisors m k n h hn hnh hh).1 hs')).resolve_right hnm
  let a := Classical.choose hmh
  let b := Classical.choose hnk
  have ha : h = m * a := Classical.choose_spec hmh
  have hb : k = n * b := Classical.choose_spec hnk
  have ha0 : 0 < a := by
    by_contra hnot
    have hz : a = 0 := by omega
    have hzero : h = 0 := by rw [ha, hz, Nat.mul_zero]
    omega
  have hb0 : 0 < b := by
    by_contra hnot
    have hz : b = 0 := by omega
    have hzero : k = 0 := by rw [hb, hz, Nat.mul_zero]
    omega
  have hab : 1 < a * b := by
    by_contra hnot
    have ha1 : 1 <= a := by omega
    have hb1 : 1 <= b := by omega
    have ha_le : a <= a * b := by
      simpa only [Nat.mul_one] using Nat.mul_le_mul_left a hb1
    have hb_le : b <= a * b := by
      simpa only [Nat.one_mul] using Nat.mul_le_mul_right b ha1
    have haOne : a = 1 := by omega
    have hhm : h = m := by simpa only [haOne, Nat.mul_one] using ha
    have hnpar := hn.eq_two_or_odd
    have hmpar := hm.eq_two_or_odd
    have hqpar := hnh.eq_two_or_odd
    omega
  refine Exists.intro a (Exists.intro b
    (And.intro ha0 (And.intro hb0 (And.intro hab
      (And.intro ha (And.intro hb ?_))))))
  have hsub : a * b - 1 + 1 = a * b := by omega
  calc
    (a * b - 1) * n + (n + h) = (a * b - 1 + 1) * n + h := by ring
    _ = a * b * n + h := by rw [hsub]
    _ = a * (m + k) := by rw [ha, hb]; ring

theorem native_lower_square_cross_bounded_positive_output
    (n h m k J Y : Nat)
    (hn : Nat.Prime n) (hnh : Nat.Prime (n + h))
    (hm : Nat.Prime m) (hmk : Nat.Prime (m + k))
    (hh : 0 < h) (hk : 0 < k) (hn2 : 2 < n) (hm2 : 2 < m)
    (hne : Not (n = m)) (hs : IsSquare (h * k * n * m))
    (hny : n + h <= Y) (hmy : m + k <= Y)
    (hJn : Y < J * n) (hJm : Y < J * m) :
    exists a b : Nat, And (0 < a) (And (a < J)
      (And (0 < b) (And (b < J) (And (1 < a * b)
        ((a * b - 1) * n + (n + h) = a * (m + k)))))) := by
  have cert := native_lower_square_cross_positive_output
    n h m k hn hnh hm hmk hh hk hn2 hm2 hne hs
  cases cert with
  | intro a rest =>
    cases rest with
    | intro b spec =>
      have ha : h = m * a := spec.2.2.2.1
      have hb : k = n * b := spec.2.2.2.2.1
      have haJ : a < J := by
        by_contra hnot
        have hja : J <= a := by omega
        have hmul : m * J <= m * a := Nat.mul_le_mul_left m hja
        rw [<- ha] at hmul
        have hcomm : m * J = J * m := Nat.mul_comm m J
        omega
      have hbJ : b < J := by
        by_contra hnot
        have hjb : J <= b := by omega
        have hmul : n * J <= n * b := Nat.mul_le_mul_left n hjb
        rw [<- hb] at hmul
        have hcomm : n * J = J * n := Nat.mul_comm n J
        omega
      exact Exists.intro a (Exists.intro b
        (And.intro spec.1 (And.intro haJ
          (And.intro spec.2.1 (And.intro hbJ
            (And.intro spec.2.2.1 spec.2.2.2.2.2))))))

end PrimeFactorOscillations.FiniteFieldIntegerSignature

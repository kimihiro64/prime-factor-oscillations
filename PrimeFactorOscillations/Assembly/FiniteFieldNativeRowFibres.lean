/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.FiniteFieldNativeEndpointDivisors

/-!
# Endpoint recovery from native squareclass rows

The lower row recovers the lower prime when both gaps are short. The upper
row always recovers the upper prime. These are the fixed-endpoint constraints
for counting row fibres in height-bounded native agreement packings.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.FiniteFieldIntegerSignature

theorem native_square_rows_recover_endpoints (n h m k : Nat)
    (hn : Nat.Prime n) (hnh : Nat.Prime (n + h))
    (hm : Nat.Prime m) (hmk : Nat.Prime (m + k))
    (hh : 0 < h) (hk : 0 < k) :
    And
      (h < n -> k < m -> IsSquare (h * k * n * m) -> n = m)
      (IsSquare (h * k * (n + h) * (m + k)) -> n + h = m + k) := by
  have hforward := native_square_cross_rows_endpoint_divisors n h m k hm hmk hk
  have hbackward := native_square_cross_rows_endpoint_divisors m k n h hn hnh hh
  constructor
  . intro hhn hkm hs
    have hs' : IsSquare (k * h * m * n) := by
      simpa only [mul_assoc, mul_comm, mul_left_comm] using hs
    have hmDiv := hforward.1 hs
    have hnDiv := hbackward.1 hs'
    have hmn : m <= n := by
      rcases hm.dvd_mul.mp hmDiv with hd | hd
      . exact (Nat.le_of_dvd hh hd).trans hhn.le
      . exact Nat.le_of_dvd hn.pos hd
    have hnm : n <= m := by
      rcases hn.dvd_mul.mp hnDiv with hd | hd
      . exact (Nat.le_of_dvd hk hd).trans hkm.le
      . exact Nat.le_of_dvd hm.pos hd
    exact Nat.le_antisymm hnm hmn
  . intro hs
    have hs' : IsSquare (k * h * (m + k) * (n + h)) := by
      simpa only [mul_assoc, mul_comm, mul_left_comm] using hs
    have hrDiv := hforward.2 hs
    have hqDiv := hbackward.2 hs'
    have hrq : m + k <= n + h := by
      rcases hmk.dvd_mul.mp hrDiv with hd | hd
      . have hle := Nat.le_of_dvd hh hd
        omega
      . exact Nat.le_of_dvd hnh.pos hd
    have hqr : n + h <= m + k := by
      rcases hnh.dvd_mul.mp hqDiv with hd | hd
      . have hle := Nat.le_of_dvd hk hd
        omega
      . exact Nat.le_of_dvd hmk.pos hd
    exact Nat.le_antisymm hqr hrq

end PrimeFactorOscillations.FiniteFieldIntegerSignature

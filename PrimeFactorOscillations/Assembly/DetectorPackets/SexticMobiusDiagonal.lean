/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Assembly.DetectorPackets.LowKernelQuotientTransport

/-!
# SexticMobiusDiagonal

Maintained extraction of completed detector/packet proof components.
All original theorem hypotheses and retained proof bodies are preserved.
This module alone asserts no improved zero-free boundary.
-/

set_option autoImplicit false
set_option Elab.async false

/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

/-!
# Exact signed local diagonal for the quadratic marked sextic quotient

At one prime, d is the squarefree Mobius exponent, m is the squarefree
mark exponent, and n is the plain numerator exponent. Before reflection
the phase is chi^(n+5*d+3*m). Neutrality forces n=d+3*m+6*h.
Thus the diagonal retains the negative Mobius factor 1-B*A and gains
the marked factor A^3, with its complete finite truncation remainder.

This identifies a local arithmetic diagonal. It neither asserts that
the off-diagonal is small nor expands a reciprocal on a moved contour.
The denominator 1-A^6 and its possible continued pole must be retained.
-/

set_option maxHeartbeats 800000

noncomputable section
namespace OAI.SevenEighths.SexticMobiusDiagonal

theorem neutral_exponents (n d m : Nat) (hd : d <= 1) (hm : m <= 1) :
    Dvd.dvd 6 (n+5*d+3*m) <->
      exists h : Nat, n=d+3*m+6*h := by
  constructor
  . intro h
    have hmod := Nat.mod_eq_zero_of_dvd h
    have hbase : d+3*m <= n := by omega
    refine Exists.intro ((n-(d+3*m))/6) ?_
    have hdiv := Nat.mod_add_div (n-(d+3*m)) 6
    omega
  . intro h
    choose k hk using h
    apply Nat.dvd_of_mod_eq_zero
    omega

def block (A B : Complex) (m H : Nat) : Complex :=
  (Finset.range H).sum fun h =>
    A^(3*m+6*h)-B*A^(1+3*m+6*h)

def full (A B : Complex) (m : Nat) : Complex :=
  A^(3*m)*(1-B*A)/(1-A^6)

theorem block_factor (A B : Complex) (m H : Nat) :
    block A B m H =
      A^(3*m)*(1-B*A)*((Finset.range H).sum fun h => (A^6)^h) := by
  unfold block
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro h _
  simp only [pow_add, pow_mul, pow_one]
  ring

theorem finite_diagonal (A B : Complex) (m H : Nat) :
    (1-A^6)*block A B m H =
      A^(3*m)*(1-B*A)*(1-(A^6)^H) := by
  rw [block_factor]
  calc
    _ = A^(3*m)*(1-B*A)*
        (((Finset.range H).sum fun h => (A^6)^h)*(1-A^6)) := by ring
    _ = _ := by rw [geom_sum_mul_neg]

theorem truncation_remainder (A B : Complex) (m H : Nat)
    (hA : Not (1-A^6=0)) :
    full A B m - block A B m H = full A B m*(A^6)^H := by
  have he := finite_diagonal A B m H
  unfold full
  field_simp [hA]
  linear_combination -he

theorem diagonal_hasSum (A B : Complex) (m : Nat) (hA : norm (A^6) < 1) :
    HasSum (fun h : Nat => A^(3*m+6*h)-B*A^(1+3*m+6*h)) (full A B m) := by
  have hg := HasSum.mul_left (A^(3*m)*(1-B*A))
    (hasSum_geometric_of_norm_lt_one hA)
  have hf (h : Nat) :
      A^(3*m+6*h)-B*A^(1+3*m+6*h) =
        (A^(3*m)*(1-B*A))*(A^6)^h := by
    simp only [pow_add, pow_mul, pow_one]
    ring
  simpa only [hf, full, div_eq_mul_inv] using hg

end OAI.SevenEighths.SexticMobiusDiagonal

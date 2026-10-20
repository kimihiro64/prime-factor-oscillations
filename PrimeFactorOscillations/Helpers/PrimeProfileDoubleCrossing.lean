/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Helpers.PrimeProfileCutoffRigidity
import PrimeFactorOscillations.Mathlib.Combinatorics.TwoBoundaryTransport
import PrimeFactorOscillations.Mathlib.NumberTheory.Primes.WeightedQuadruplet

/-!
# The complete normalized cost of two prime-coordinate crossings

The signed two-boundary comparison is applied to the actual compensated
logarithmic weights. A common middle-prime normalization retains the full
weighted four-prime span, uniformly over arbitrary positive probes.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

open Filter
open scoped Topology

namespace PrimeFactorOscillations.PrimeProfileRigidity

theorem two_pairLogDefects_le_prime_prefixDefect
    (e : Equiv.Perm Nat) (t : Real) (ht : 0 < t) (k : Nat)
    (hm : 2 <= Finset.prefixDisplacement e (k + 2)) :
    Real.pairLogDefect t (PrimeFactorUnimodality.primeAt k : Real)
        (PrimeFactorUnimodality.primeAt (k + 2) : Real) +
      Real.pairLogDefect t (PrimeFactorUnimodality.primeAt (k + 1) : Real)
        (PrimeFactorUnimodality.primeAt (k + 3) : Real) <=
      Finset.prefixDefect (primeLogWeight t) e (k + 2) := by
  have hb := Finset.two_boundary_cost_le_prefixDefect
    (primeLogWeight t) (primeLogWeight_strictMono t ht).monotone e k hm
  change primeLogWeight t (k + 2) - primeLogWeight t k +
    (primeLogWeight t (k + 3) - primeLogWeight t (k + 1)) <= _
  linarith only [hb]

theorem weighted_span_le_normalized_two_crossing
    (e : Equiv.Perm Nat) (t : Nat -> Real) (k : Nat) (ht : 0 < t (k + 1))
    (hm : 2 <= Finset.prefixDisplacement e (k + 2)) :
    (((PrimeFactorUnimodality.primeAt (k + 2) : Real) - PrimeFactorUnimodality.primeAt k) +
      ((PrimeFactorUnimodality.primeAt (k + 3) : Real) -
        PrimeFactorUnimodality.primeAt (k + 1))) *
        ((PrimeFactorUnimodality.primeAt (k + 1) : Real) /
          PrimeFactorUnimodality.primeAt (k + 3)) ^ 2 <=
      normalizedPrimePrefixDefect e t (k + 1) := by
  let p0 : Real := PrimeFactorUnimodality.primeAt k
  let p1 : Real := PrimeFactorUnimodality.primeAt (k + 1)
  let p2 : Real := PrimeFactorUnimodality.primeAt (k + 2)
  let p3 : Real := PrimeFactorUnimodality.primeAt (k + 3)
  let T : Real := t (k + 1)
  have hp0 : 0 < p0 := by
    dsimp only [p0]
    exact_mod_cast (PrimeFactorUnimodality.prime_primeAt k).pos
  have hp1 : 0 < p1 := by
    dsimp only [p1]
    exact_mod_cast (PrimeFactorUnimodality.prime_primeAt (k + 1)).pos
  have hp2 : 0 < p2 := by
    dsimp only [p2]
    exact_mod_cast (PrimeFactorUnimodality.prime_primeAt (k + 2)).pos
  have hp3 : 0 < p3 := by
    dsimp only [p3]
    exact_mod_cast (PrimeFactorUnimodality.prime_primeAt (k + 3)).pos
  have h01 : p0 <= p1 := by
    dsimp only [p0, p1]
    exact_mod_cast PrimeFactorUnimodality.primeAt_strictMono.monotone (show k <= k + 1 by omega)
  have h02 : p0 <= p2 := by
    dsimp only [p0, p2]
    exact_mod_cast PrimeFactorUnimodality.primeAt_strictMono.monotone (show k <= k + 2 by omega)
  have h13 : p1 <= p3 := by
    dsimp only [p1, p3]
    exact_mod_cast PrimeFactorUnimodality.primeAt_strictMono.monotone (show k + 1 <= k + 3 by omega)
  have h23 : p2 <= p3 := by
    dsimp only [p2, p3]
    exact_mod_cast PrimeFactorUnimodality.primeAt_strictMono.monotone (show k + 2 <= k + 3 by omega)
  have hfirst := Real.gap_mul_reference_ratio_sq_le_normalized_pairLogDefect
    T p0 p2 p1 ht hp0 h02 h01
  have hsecond := Real.gap_mul_ratio_sq_le_normalized_pairLogDefect T p1 p3 ht hp1 h13
  have hratio : p1 / p3 <= p1 / p2 :=
    div_le_div_of_nonneg_left hp1.le hp2 h23
  have hsquare : (p1 / p3) ^ 2 <= (p1 / p2) ^ 2 := by
    simpa only [pow_two] using
      mul_le_mul hratio hratio (div_nonneg hp1.le hp3.le) (div_nonneg hp1.le hp2.le)
  have hfirst' := (mul_le_mul_of_nonneg_left hsquare (sub_nonneg.mpr h02)).trans hfirst
  have hpair := two_pairLogDefects_le_prime_prefixDefect e T ht k hm
  have hnorm : 0 <= p1 ^ 2 * (p1 + T) / T ^ 2 := by positivity
  have hfull := mul_le_mul_of_nonneg_left hpair hnorm
  change ((p2 - p0) + (p3 - p1)) * (p1 / p3) ^ 2 <=
    p1 ^ 2 * (p1 + T) / T ^ 2 * Finset.prefixDefect (primeLogWeight T) e (k + 2)
  nlinarith only [hfirst', hsecond, hfull]

/-- The weighted span at the middle cut of four consecutive primes. -/
def primeWeightedSpan (k : Nat) : Real :=
  ((PrimeFactorUnimodality.primeAt (k + 2) : Real) - PrimeFactorUnimodality.primeAt k) +
    ((PrimeFactorUnimodality.primeAt (k + 3) : Real) -
      PrimeFactorUnimodality.primeAt (k + 1))

theorem twelve_le_primeWeightedSpan (k : Nat)
    (hthree : 3 < PrimeFactorUnimodality.primeAt k) :
    (12 : Real) <= primeWeightedSpan k := by
  have hb := Nat.prime_quadruplet_weighted_span
    (PrimeFactorUnimodality.primeAt k) (PrimeFactorUnimodality.primeAt (k + 1))
    (PrimeFactorUnimodality.primeAt (k + 2)) (PrimeFactorUnimodality.primeAt (k + 3))
    (PrimeFactorUnimodality.prime_primeAt k)
    (PrimeFactorUnimodality.prime_primeAt (k + 1))
    (PrimeFactorUnimodality.prime_primeAt (k + 2))
    (PrimeFactorUnimodality.prime_primeAt (k + 3)) hthree
    (PrimeFactorUnimodality.primeAt_strictMono (by omega))
    (PrimeFactorUnimodality.primeAt_strictMono (by omega))
    (PrimeFactorUnimodality.primeAt_strictMono (by omega))
  have hc : (PrimeFactorUnimodality.primeAt k : Real) +
      PrimeFactorUnimodality.primeAt (k + 1) + 12 <=
      (PrimeFactorUnimodality.primeAt (k + 2) : Real) +
        PrimeFactorUnimodality.primeAt (k + 3) := by exact_mod_cast hb
  unfold primeWeightedSpan
  linarith only [hc]

theorem primeWeightedSpan_eq_twelve_iff (k : Nat)
    (hthree : 3 < PrimeFactorUnimodality.primeAt k) :
    primeWeightedSpan k = 12 <->
      (PrimeFactorUnimodality.primeAt (k + 1) = PrimeFactorUnimodality.primeAt k + 2 /\
        PrimeFactorUnimodality.primeAt (k + 2) = PrimeFactorUnimodality.primeAt k + 6 /\
        PrimeFactorUnimodality.primeAt (k + 3) = PrimeFactorUnimodality.primeAt k + 8) \/
      (PrimeFactorUnimodality.primeAt (k + 1) = PrimeFactorUnimodality.primeAt k + 4 /\
        PrimeFactorUnimodality.primeAt (k + 2) = PrimeFactorUnimodality.primeAt k + 6 /\
        PrimeFactorUnimodality.primeAt (k + 3) = PrimeFactorUnimodality.primeAt k + 10) := by
  have hb := Nat.prime_quadruplet_weighted_span_eq_twelve_iff
    (PrimeFactorUnimodality.primeAt k) (PrimeFactorUnimodality.primeAt (k + 1))
    (PrimeFactorUnimodality.primeAt (k + 2)) (PrimeFactorUnimodality.primeAt (k + 3))
    (PrimeFactorUnimodality.prime_primeAt k)
    (PrimeFactorUnimodality.prime_primeAt (k + 1))
    (PrimeFactorUnimodality.prime_primeAt (k + 2))
    (PrimeFactorUnimodality.prime_primeAt (k + 3)) hthree
    (PrimeFactorUnimodality.primeAt_strictMono (by omega))
    (PrimeFactorUnimodality.primeAt_strictMono (by omega))
    (PrimeFactorUnimodality.primeAt_strictMono (by omega))
  constructor
  . intro h
    apply hb.mp
    have hc : (PrimeFactorUnimodality.primeAt (k + 2) : Real) +
        PrimeFactorUnimodality.primeAt (k + 3) =
        (PrimeFactorUnimodality.primeAt k : Real) +
          PrimeFactorUnimodality.primeAt (k + 1) + 12 := by
      unfold primeWeightedSpan at h
      linarith only [h]
    exact_mod_cast hc
  . intro h
    have hn := hb.mpr h
    have hc : (PrimeFactorUnimodality.primeAt (k + 2) : Real) +
        PrimeFactorUnimodality.primeAt (k + 3) =
        (PrimeFactorUnimodality.primeAt k : Real) +
          PrimeFactorUnimodality.primeAt (k + 1) + 12 := by exact_mod_cast hn
    unfold primeWeightedSpan
    linarith only [hc]

theorem normalized_two_crossing_ge_twelve
    (e : Equiv.Perm Nat) (t : Nat -> Real) (k : Nat)
    (ht : 0 < t (k + 1)) (hthree : 3 < PrimeFactorUnimodality.primeAt k)
    (hm : 2 <= Finset.prefixDisplacement e (k + 2)) :
    12 * ((PrimeFactorUnimodality.primeAt (k + 1) : Real) /
      PrimeFactorUnimodality.primeAt (k + 3)) ^ 2 <=
        normalizedPrimePrefixDefect e t (k + 1) := by
  have hb := mul_le_mul_of_nonneg_right (twelve_le_primeWeightedSpan k hthree)
    (sq_nonneg ((PrimeFactorUnimodality.primeAt (k + 1) : Real) /
      PrimeFactorUnimodality.primeAt (k + 3)))
  exact hb.trans (weighted_span_le_normalized_two_crossing e t k ht hm)

/-- The eventual cutoff is independent of the permutation and positive probes. -/
theorem eventual_uniform_two_crossing_lower (eps : Real) (heps : 0 < eps) :
    exists N : Nat, forall k : Nat, N <= k ->
      forall (e : Equiv.Perm Nat) (t : Nat -> Real),
        0 < t (k + 1) -> 2 <= Finset.prefixDisplacement e (k + 2) ->
          12 - eps <= normalizedPrimePrefixDefect e t (k + 1) := by
  have hcost : Tendsto (fun k : Nat =>
      12 * ((PrimeFactorUnimodality.primeAt (k + 1) : Real) /
        PrimeFactorUnimodality.primeAt (k + 3)) ^ 2) atTop (nhds 12) := by
    simpa only [one_pow, mul_one] using
      ((tendsto_primeAt_shift_div_shift 3 1).pow 2).const_mul (12 : Real)
  have hsmall := hcost.eventually
    (lt_mem_nhds (show (12 : Real) - eps < 12 by linarith only [heps]))
  have hprime : Tendsto PrimeFactorUnimodality.primeAt atTop atTop :=
    PrimeFactorUnimodality.primeAt_strictMono.tendsto_atTop
  have hlarge := hprime.eventually (eventually_gt_atTop 3)
  have hall : Filter.Eventually (fun k : Nat =>
      forall (e : Equiv.Perm Nat) (t : Nat -> Real),
        0 < t (k + 1) -> 2 <= Finset.prefixDisplacement e (k + 2) ->
          12 - eps <= normalizedPrimePrefixDefect e t (k + 1)) atTop := by
    filter_upwards [hsmall, hlarge] with k hk hpk
    intro e t ht hm
    exact (le_of_lt hk).trans (normalized_two_crossing_ge_twelve e t k ht hpk hm)
  exact eventually_atTop.mp hall

theorem two_crossing_defect_arbitrarily_close_to_twelve
    (e : Equiv.Perm Nat) (t : Nat -> Real) (ht : forall n, 0 < t n)
    (hcross : forall N : Nat, exists k : Nat,
      N <= k /\ 2 <= Finset.prefixDisplacement e (k + 2)) :
    forall eps : Real, 0 < eps -> forall N : Nat,
      exists k : Nat, N <= k /\
        12 - eps <= normalizedPrimePrefixDefect e t (k + 1) := by
  intro eps heps N
  have hevent := eventual_uniform_two_crossing_lower eps heps
  let M := Classical.choose hevent
  have hM : forall k : Nat, M <= k ->
      forall (e : Equiv.Perm Nat) (t : Nat -> Real),
        0 < t (k + 1) -> 2 <= Finset.prefixDisplacement e (k + 2) ->
          12 - eps <= normalizedPrimePrefixDefect e t (k + 1) :=
    Classical.choose_spec hevent
  let k := Classical.choose (hcross (max N M))
  have hk : max N M <= k /\ 2 <= Finset.prefixDisplacement e (k + 2) :=
    Classical.choose_spec (hcross (max N M))
  exact Exists.intro k (And.intro ((le_max_left N M).trans hk.1)
    (hM k ((le_max_right N M).trans hk.1) e t (ht (k + 1)) hk.2))

theorem eventually_width_le_one_of_eventual_defect_le
    (e : Equiv.Perm Nat) (t : Nat -> Real) (ht : forall n, 0 < t n)
    (C : Real) (hC : C < 12)
    (hupper : Filter.Eventually (fun k : Nat =>
      normalizedPrimePrefixDefect e t (k + 1) <= C) atTop) :
    Filter.Eventually (fun k : Nat => Finset.prefixDisplacement e (k + 2) <= 1) atTop := by
  have heps : 0 < (12 - C) / 2 := by linarith only [hC]
  have hevent := eventual_uniform_two_crossing_lower ((12 - C) / 2) heps
  let N := Classical.choose hevent
  have hN : forall k : Nat, N <= k ->
      forall (e : Equiv.Perm Nat) (t : Nat -> Real),
        0 < t (k + 1) -> 2 <= Finset.prefixDisplacement e (k + 2) ->
          12 - (12 - C) / 2 <= normalizedPrimePrefixDefect e t (k + 1) :=
    Classical.choose_spec hevent
  filter_upwards [hupper, eventually_ge_atTop N] with k hk hNk
  by_contra hn
  have hm : 2 <= Finset.prefixDisplacement e (k + 2) := by omega
  have hlo := hN k hNk e t (ht (k + 1)) hm
  linarith only [hlo, hk, hC]

end PrimeFactorOscillations.PrimeProfileRigidity

/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Helpers.PrimeProfileDoubleCrossing

/-!
# Recovering four-prime patterns from a probability-profile cost ceiling

The two families have offsets (0,2,6,8) and (0,4,6,10), with prime anchor
greater than three. Windows may overlap; the inverse uses every crossing.
An eventual ceiling strictly below fourteen forces one of these patterns
at every sufficiently late double crossing. No prime-pattern supply is
assumed or proved by this conditional inverse.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

open Filter
open scoped Topology

namespace PrimeFactorOscillations.PrimeProfileRigidity

def IsShortPrimeQuadruplet (k : Nat) : Prop :=
  3 < PrimeFactorUnimodality.primeAt k /\
    ((PrimeFactorUnimodality.primeAt (k + 1) = PrimeFactorUnimodality.primeAt k + 2 /\
      PrimeFactorUnimodality.primeAt (k + 2) = PrimeFactorUnimodality.primeAt k + 6 /\
      PrimeFactorUnimodality.primeAt (k + 3) = PrimeFactorUnimodality.primeAt k + 8) \/
    (PrimeFactorUnimodality.primeAt (k + 1) = PrimeFactorUnimodality.primeAt k + 4 /\
      PrimeFactorUnimodality.primeAt (k + 2) = PrimeFactorUnimodality.primeAt k + 6 /\
      PrimeFactorUnimodality.primeAt (k + 3) = PrimeFactorUnimodality.primeAt k + 10))

theorem primeWeightedSpan_eq_twelve_or_fourteen_le (k : Nat)
    (hthree : 3 < PrimeFactorUnimodality.primeAt k) :
    primeWeightedSpan k = 12 \/ (14 : Real) <= primeWeightedSpan k := by
  have hlo := twelve_le_primeWeightedSpan k hthree
  have hcast : (PrimeFactorUnimodality.primeAt k : Real) +
      PrimeFactorUnimodality.primeAt (k + 1) + 12 <=
      (PrimeFactorUnimodality.primeAt (k + 2) : Real) +
        PrimeFactorUnimodality.primeAt (k + 3) := by
    unfold primeWeightedSpan at hlo
    linarith only [hlo]
  have hnat : PrimeFactorUnimodality.primeAt k +
      PrimeFactorUnimodality.primeAt (k + 1) + 12 <=
      PrimeFactorUnimodality.primeAt (k + 2) +
        PrimeFactorUnimodality.primeAt (k + 3) := by exact_mod_cast hcast
  have ho0 := (PrimeFactorUnimodality.prime_primeAt k).eq_two_or_odd
  have ho1 := (PrimeFactorUnimodality.prime_primeAt (k + 1)).eq_two_or_odd
  have ho2 := (PrimeFactorUnimodality.prime_primeAt (k + 2)).eq_two_or_odd
  have ho3 := (PrimeFactorUnimodality.prime_primeAt (k + 3)).eq_two_or_odd
  have h01 : PrimeFactorUnimodality.primeAt k < PrimeFactorUnimodality.primeAt (k + 1) :=
    PrimeFactorUnimodality.primeAt_strictMono (by omega)
  have h12 : PrimeFactorUnimodality.primeAt (k + 1) <
      PrimeFactorUnimodality.primeAt (k + 2) :=
    PrimeFactorUnimodality.primeAt_strictMono (by omega)
  have h23 : PrimeFactorUnimodality.primeAt (k + 2) <
      PrimeFactorUnimodality.primeAt (k + 3) :=
    PrimeFactorUnimodality.primeAt_strictMono (by omega)
  have hgap : PrimeFactorUnimodality.primeAt (k + 2) +
        PrimeFactorUnimodality.primeAt (k + 3) =
        PrimeFactorUnimodality.primeAt k + PrimeFactorUnimodality.primeAt (k + 1) + 12 \/
      PrimeFactorUnimodality.primeAt k + PrimeFactorUnimodality.primeAt (k + 1) + 14 <=
        PrimeFactorUnimodality.primeAt (k + 2) +
          PrimeFactorUnimodality.primeAt (k + 3) := by omega
  cases hgap with
  | inl h =>
    apply Or.inl
    have hc : (PrimeFactorUnimodality.primeAt (k + 2) : Real) +
        PrimeFactorUnimodality.primeAt (k + 3) =
        (PrimeFactorUnimodality.primeAt k : Real) +
          PrimeFactorUnimodality.primeAt (k + 1) + 12 := by exact_mod_cast h
    unfold primeWeightedSpan
    linarith only [hc]
  | inr h =>
    apply Or.inr
    have hc : (PrimeFactorUnimodality.primeAt k : Real) +
        PrimeFactorUnimodality.primeAt (k + 1) + 14 <=
        (PrimeFactorUnimodality.primeAt (k + 2) : Real) +
          PrimeFactorUnimodality.primeAt (k + 3) := by exact_mod_cast h
    unfold primeWeightedSpan
    linarith only [hc]

theorem eventually_quadruplet_of_eventual_defect_le
    (e : Equiv.Perm Nat) (t : Nat -> Real) (ht : forall n, 0 < t n)
    (C : Real) (hC : C < 14)
    (hupper : Filter.Eventually (fun k : Nat =>
      normalizedPrimePrefixDefect e t (k + 1) <= C) atTop) :
    Filter.Eventually (fun k : Nat =>
      2 <= Finset.prefixDisplacement e (k + 2) -> IsShortPrimeQuadruplet k) atTop := by
  have hcost : Tendsto (fun k : Nat =>
      14 * ((PrimeFactorUnimodality.primeAt (k + 1) : Real) /
        PrimeFactorUnimodality.primeAt (k + 3)) ^ 2) atTop (nhds 14) := by
    simpa only [one_pow, mul_one] using
      ((tendsto_primeAt_shift_div_shift 3 1).pow 2).const_mul (14 : Real)
  have hlargeCost := hcost.eventually (lt_mem_nhds hC)
  have hprime : Tendsto PrimeFactorUnimodality.primeAt atTop atTop :=
    PrimeFactorUnimodality.primeAt_strictMono.tendsto_atTop
  have hlargePrime := hprime.eventually (eventually_gt_atTop 3)
  filter_upwards [hupper, hlargeCost, hlargePrime] with k hk hcostk hpk
  intro hm
  apply And.intro hpk
  apply (primeWeightedSpan_eq_twelve_iff k hpk).mp
  cases primeWeightedSpan_eq_twelve_or_fourteen_le k hpk with
  | inl heq => exact heq
  | inr hfourteen =>
    have hlo := mul_le_mul_of_nonneg_right hfourteen
      (sq_nonneg ((PrimeFactorUnimodality.primeAt (k + 1) : Real) /
        PrimeFactorUnimodality.primeAt (k + 3)))
    have hfull := hlo.trans (weighted_span_le_normalized_two_crossing e t k (ht _) hm)
    linarith only [hk, hcostk, hfull]

theorem recurrent_quadruplet_of_infinite_double_crossings
    (e : Equiv.Perm Nat) (t : Nat -> Real) (ht : forall n, 0 < t n)
    (C : Real) (hC : C < 14)
    (hupper : Filter.Eventually (fun k : Nat =>
      normalizedPrimePrefixDefect e t (k + 1) <= C) atTop)
    (hcross : forall N : Nat, exists k : Nat,
      N <= k /\ 2 <= Finset.prefixDisplacement e (k + 2)) :
    forall N : Nat, exists k : Nat, N <= k /\ IsShortPrimeQuadruplet k := by
  have hevent := eventually_atTop.mp
    (eventually_quadruplet_of_eventual_defect_le e t ht C hC hupper)
  let M := Classical.choose hevent
  have hM : forall k : Nat, M <= k ->
      2 <= Finset.prefixDisplacement e (k + 2) -> IsShortPrimeQuadruplet k :=
    Classical.choose_spec hevent
  intro N
  let k := Classical.choose (hcross (max N M))
  have hk : max N M <= k /\ 2 <= Finset.prefixDisplacement e (k + 2) :=
    Classical.choose_spec (hcross (max N M))
  exact Exists.intro k (And.intro ((le_max_left N M).trans hk.1)
    (hM k ((le_max_right N M).trans hk.1) hk.2))

end PrimeFactorOscillations.PrimeProfileRigidity

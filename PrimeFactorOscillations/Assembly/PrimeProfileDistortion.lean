/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Assembly.PrimeProfileZeroHoles

/-!
# Universal distortion below an eventual prime-gap floor

Every infinite rearrangement crosses infinitely many prefixes. The full
signed boundary cost retains the actual gap and tends to that gap uniformly
over all positive adaptive probes. Zero holes instead have divergent cost.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

open Filter
open scoped Topology

namespace PrimeFactorOscillations.PrimeProfileRigidity

private theorem exists_displaced_prefix_above (e : Equiv.Perm Nat)
    (hinf : Not (exists N : Nat, forall n, N <= n -> e n = n)) (M : Nat) :
    exists n : Nat, M <= n /\
      Not ((Finset.range (n + 1)).image e = Finset.range (n + 1)) := by
  classical
  by_contra hn
  have hprefix : forall n, M <= n ->
      (Finset.range (n + 1)).image e = Finset.range (n + 1) := by
    intro n hMn
    by_contra he
    exact hn (Exists.intro n (And.intro hMn he))
  apply hinf
  refine Exists.intro (M + 1) ?_
  intro n hn
  have h0 := hprefix (n - 1) (by omega)
  have he : n - 1 + 1 = n := by omega
  rw [he] at h0
  exact Finset.perm_apply_eq_of_image_range_eq e n h0 (hprefix n (by omega))

/-- Each displaced prefix pays its full normalized adjacent-gap cost. -/
theorem gap_ratio_sq_le_normalized_defect (e : Equiv.Perm Nat)
    (t : Nat -> Real) (n : Nat) (ht : 0 < t n)
    (hcross : Not ((Finset.range (n + 1)).image e = Finset.range (n + 1))) :
    ((PrimeFactorUnimodality.primeAt (n + 1) : Real) -
        (PrimeFactorUnimodality.primeAt n : Real)) *
      ((PrimeFactorUnimodality.primeAt n : Real) /
        (PrimeFactorUnimodality.primeAt (n + 1) : Real)) ^ 2 <=
      normalizedPrimePrefixDefect e t n := by
  have hp : (0 : Real) < PrimeFactorUnimodality.primeAt n := by
    exact_mod_cast (PrimeFactorUnimodality.prime_primeAt n).pos
  have hpq : (PrimeFactorUnimodality.primeAt n : Real) <=
      (PrimeFactorUnimodality.primeAt (n + 1) : Real) := by
    exact_mod_cast (PrimeFactorUnimodality.primeAt_strictMono (Nat.lt_succ_self n)).le
  have hc : (1 : Real) <= Finset.prefixDisplacement e (n + 1) := by
    have hn : Not (Finset.prefixDisplacement e (n + 1) = 0) := by
      intro hz
      exact hcross ((Finset.prefixDisplacement_eq_zero_iff e (n + 1)).mp hz)
    exact_mod_cast (show 1 <= Finset.prefixDisplacement e (n + 1) by omega)
  have hw := (primeLogWeight_strictMono (t n) ht).monotone
  have hg : 0 <= primeLogWeight (t n) (n + 1) - primeLogWeight (t n) n :=
    sub_nonneg.mpr (hw (Nat.le_succ n))
  have hb := Finset.prefixDisplacement_mul_gap_le_prefixDefect
    (primeLogWeight (t n)) hw e n
  have hm := mul_le_mul_of_nonneg_right hc hg
  have hd : primeLogWeight (t n) (n + 1) - primeLogWeight (t n) n <=
      Finset.prefixDefect (primeLogWeight (t n)) e (n + 1) := by
    linarith only [hb, hm]
  have hnorm : 0 <= (PrimeFactorUnimodality.primeAt n : Real) ^ 2 *
      ((PrimeFactorUnimodality.primeAt n : Real) + t n) / (t n) ^ 2 := by positivity
  have hsharp := Real.gap_mul_ratio_sq_le_normalized_pairLogDefect (t n)
    (PrimeFactorUnimodality.primeAt n : Real)
    (PrimeFactorUnimodality.primeAt (n + 1) : Real) ht hp hpq
  apply hsharp.trans
  exact mul_le_mul_of_nonneg_left hd hnorm

/-- Every infinite permutation has normalized defects arbitrarily close to
any independently supplied eventual prime-gap floor. -/
theorem arbitrarily_large_defect_of_eventual_gap_floor
    (e : Equiv.Perm Nat) (hinf : Not (exists N : Nat, forall n, N <= n -> e n = n))
    (h : Nat)
    (hmin : exists Q : Nat, forall n : Nat,
      Q <= PrimeFactorUnimodality.primeAt n ->
        PrimeFactorUnimodality.primeAt n + h <= PrimeFactorUnimodality.primeAt (n + 1))
    (t : Nat -> Real) (ht : forall n, 0 < t n) :
    forall eps : Real, 0 < eps -> forall N : Nat,
      exists n : Nat, N <= n /\
        (h : Real) - eps <= normalizedPrimePrefixDefect e t n := by
  intro eps heps N
  have hratio : Tendsto (fun n : Nat =>
      (PrimeFactorUnimodality.primeAt n : Real) /
        (PrimeFactorUnimodality.primeAt (n + 1) : Real)) atTop (nhds 1) := by
    simpa only [Nat.add_zero] using tendsto_primeAt_shift_div_shift 1 0
  have hlimit : Tendsto (fun n : Nat => (h : Real) *
      ((PrimeFactorUnimodality.primeAt n : Real) /
        (PrimeFactorUnimodality.primeAt (n + 1) : Real)) ^ 2) atTop (nhds (h : Real)) := by
    simpa only [one_pow, mul_one] using
      (tendsto_const_nhds.mul (hratio.pow 2))
  have hnear := hlimit.eventually (lt_mem_nhds (sub_lt_self (h : Real) heps))
  let Q := Classical.choose hmin
  have hQ : forall n : Nat, Q <= PrimeFactorUnimodality.primeAt n ->
      PrimeFactorUnimodality.primeAt n + h <= PrimeFactorUnimodality.primeAt (n + 1) :=
    Classical.choose_spec hmin
  have hgood := hnear.and (eventually_ge_atTop Q)
  let M := Classical.choose (eventually_atTop.mp hgood)
  have hM : forall n : Nat, M <= n ->
      (h : Real) - eps < (h : Real) *
        ((PrimeFactorUnimodality.primeAt n : Real) /
          (PrimeFactorUnimodality.primeAt (n + 1) : Real)) ^ 2 /\ Q <= n :=
    Classical.choose_spec (eventually_atTop.mp hgood)
  have hex := exists_displaced_prefix_above e hinf (max N M)
  let n := Classical.choose hex
  have hn : max N M <= n /\
      Not ((Finset.range (n + 1)).image e = Finset.range (n + 1)) := Classical.choose_spec hex
  have hdata := hM n ((le_max_right N M).trans hn.1)
  have hgap := hQ n (hdata.2.trans (PrimeFactorUnimodality.primeAt_strictMono.id_le n))
  have hgapR : (h : Real) <= (PrimeFactorUnimodality.primeAt (n + 1) : Real) -
      (PrimeFactorUnimodality.primeAt n : Real) := by
    have hcR : (PrimeFactorUnimodality.primeAt n : Real) + (h : Real) <=
        (PrimeFactorUnimodality.primeAt (n + 1) : Real) := by exact_mod_cast hgap
    linarith only [hcR]
  have hmul := mul_le_mul_of_nonneg_right hgapR
    (sq_nonneg ((PrimeFactorUnimodality.primeAt n : Real) /
      (PrimeFactorUnimodality.primeAt (n + 1) : Real)))
  exact Exists.intro n (And.intro ((le_max_left N M).trans hn.1)
    (hdata.1.le.trans (hmul.trans (gap_ratio_sq_le_normalized_defect e t n (ht n) hn.2))))

private theorem normalized_defect_eq_of_perm (a t : Nat -> Real) (e : Equiv.Perm Nat)
    (he : forall n, a n = reciprocalPrimeProbability (e n)) (n : Nat) :
    normalizedProbabilityPrefixDefect a t n = normalizedPrimePrefixDefect e t n := by
  unfold normalizedProbabilityPrefixDefect normalizedPrimePrefixDefect Finset.prefixDefect
  congr 2
  apply Finset.sum_congr rfl
  intro i hi
  rw [he i]
  simp only [primeLogWeight, reciprocalPrimeProbability, Real.bernoulliLogProfile, mul_one_div]

/-- Universal lower distortion throughout the entire same-profile class,
including zero holes and arbitrary positive adaptive probes. -/
theorem profile_defect_arbitrarily_close_to_gap_floor
    (a : Nat -> Real) (ha : forall n, 0 <= a n) (ha1 : forall n, a n <= 1)
    (hsa : Summable (fun n => (a n) ^ 2))
    (heq : Complex.canonicalBernoulliProfile a =
      Complex.canonicalBernoulliProfile reciprocalPrimeProbability)
    (hfinite : Not (exists N : Nat, exists e : Equiv.Perm Nat,
      (forall n, N <= n -> e n = n) /\
        forall n, a n = reciprocalPrimeProbability (e n)))
    (h : Nat)
    (hmin : exists Q : Nat, forall n : Nat,
      Q <= PrimeFactorUnimodality.primeAt n ->
        PrimeFactorUnimodality.primeAt n + h <= PrimeFactorUnimodality.primeAt (n + 1))
    (t : Nat -> Real) (ht : forall n, 0 < t n) :
    forall eps : Real, 0 < eps -> forall N : Nat,
      exists n : Nat, N <= n /\
        (h : Real) - eps <= normalizedProbabilityPrefixDefect a t n := by
  classical
  by_cases hpos : forall n, 0 < a n
  . have hh := exists_prime_perm_of_positive_profile_eq a hpos ha1 hsa heq
    let e := Classical.choose hh
    have he : forall n, a n = reciprocalPrimeProbability (e n) := Classical.choose_spec hh
    have hinf : Not (exists N : Nat, forall n, N <= n -> e n = n) := by
      intro hh
      exact hfinite (Exists.intro (Classical.choose hh)
        (Exists.intro e (And.intro (Classical.choose_spec hh) he)))
    intro eps heps N
    have hx := arbitrarily_large_defect_of_eventual_gap_floor e hinf h hmin t ht eps heps N
    let n := Classical.choose hx
    have hn := Classical.choose_spec hx
    exact Exists.intro n (And.intro hn.1 (by
      rw [normalized_defect_eq_of_perm a t e he n]
      exact hn.2))
  . have hzex : exists i : Nat, a i = 0 := by
      by_contra hn
      apply hpos
      intro i
      apply lt_of_le_of_ne (ha i)
      intro he
      exact hn (Exists.intro i he.symm)
    let i := Classical.choose hzex
    have hz : a i = 0 := Classical.choose_spec hzex
    intro eps heps N
    let m := Classical.choose (exists_nat_gt (4 * (h : Real)))
    have hm : 4 * (h : Real) < m := Classical.choose_spec (exists_nat_gt (4 * (h : Real)))
    let n := max N (max i m)
    have hnN : N <= n := le_max_left _ _
    have hni : i <= n := (le_max_left i m).trans (le_max_right N (max i m))
    have hnm : m <= n := (le_max_right i m).trans (le_max_right N (max i m))
    have hpNat : m <= PrimeFactorUnimodality.primeAt n :=
      hnm.trans (PrimeFactorUnimodality.primeAt_strictMono.id_le n)
    have hp : (m : Real) <= PrimeFactorUnimodality.primeAt n := by exact_mod_cast hpNat
    have hb := quarter_prime_le_normalized_defect_of_zero a ha ha1 hsa heq t i n hz hni (ht n)
    exact Exists.intro n (And.intro hnN (by linarith only [hb, hm, hp, heps]))

end PrimeFactorOscillations.PrimeProfileRigidity

/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Helpers.PrimeProfileInverseAsymptotics
import PrimeFactorOscillations.Mathlib.NumberTheory.Primes.Translation

/-!
# Arithmetic rigidity of matched reciprocal prime tails

A convergent integer-valued difference is eventually constant. A nonzero
fixed index shift between all late primes would therefore give an eventual
positive prime translation, excluded by the proved translation theorem.
Combined with reciprocal asymptotics, this identifies both scale and intercept.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

open Filter

private theorem eventually_constant_of_intCast_tendsto
    (f : Nat -> Int) (c : Real)
    (hf : Tendsto (fun n => (f n : Real)) atTop (nhds c)) :
    exists N, forall n, N <= n -> f n = f N := by
  have hclose : Filter.Eventually (fun n =>
      c - 1 / 4 < (f n : Real) /\ (f n : Real) < c + 1 / 4) atTop :=
    (hf.eventually (lt_mem_nhds (by linarith : c - 1 / 4 < c))).and
      (hf.eventually (gt_mem_nhds (by linarith : c < c + 1 / 4)))
  have hex := eventually_atTop.mp hclose
  let N := Classical.choose hex
  have hN := Classical.choose_spec hex N le_rfl
  refine Exists.intro N ?_
  intro n hn
  have hnclose := Classical.choose_spec hex n hn
  have hloR : (-1 : Real) < (f n : Real) - (f N : Real) := by
    linarith [hnclose.1, hN.2]
  have hhiR : (f n : Real) - (f N : Real) < 1 := by
    linarith [hnclose.2, hN.1]
  have hlo : (-1 : Int) < f n - f N := by exact_mod_cast hloR
  have hhi : f n - f N < 1 := by exact_mod_cast hhiR
  omega

private theorem not_tendsto_prime_difference_of_lt (A B : Nat) (hAB : A < B)
    (c : Real)
    (hlim : Tendsto (fun n : Nat =>
      (PrimeFactorUnimodality.primeAt (n + B) : Real) -
        (PrimeFactorUnimodality.primeAt (n + A) : Real)) atTop (nhds c)) : False := by
  let f : Nat -> Int := fun n =>
    (PrimeFactorUnimodality.primeAt (n + B) : Int) -
      (PrimeFactorUnimodality.primeAt (n + A) : Int)
  have hf : Tendsto (fun n => (f n : Real)) atTop (nhds c) := by
    simpa only [f, Int.cast_sub, Int.cast_natCast] using hlim
  have hex := eventually_constant_of_intCast_tendsto f c hf
  let N := Classical.choose hex
  have hconstant := Classical.choose_spec hex
  let C := PrimeFactorUnimodality.primeAt (N + B) -
    PrimeFactorUnimodality.primeAt (N + A)
  have hbase : PrimeFactorUnimodality.primeAt (N + A) <
      PrimeFactorUnimodality.primeAt (N + B) :=
    PrimeFactorUnimodality.primeAt_strictMono (Nat.add_lt_add_left hAB N)
  have hC : 0 < C := Nat.sub_pos_of_lt hbase
  have heq : forall n, N <= n ->
      PrimeFactorUnimodality.primeAt (n + B) =
        PrimeFactorUnimodality.primeAt (n + A) + C := by
    intro n hn
    have hnconst := hconstant n hn
    change (PrimeFactorUnimodality.primeAt (n + B) : Int) -
        (PrimeFactorUnimodality.primeAt (n + A) : Int) =
      (PrimeFactorUnimodality.primeAt (N + B) : Int) -
        (PrimeFactorUnimodality.primeAt (N + A) : Int) at hnconst
    have hCeq : PrimeFactorUnimodality.primeAt (N + B) =
        PrimeFactorUnimodality.primeAt (N + A) + C :=
      (Nat.add_sub_of_le hbase.le).symm
    omega
  apply Nat.no_eventual_positive_prime_period
    (PrimeFactorUnimodality.primeAt (N + A)) C hC
  intro p hpN hp
  let j := Nat.count Nat.Prime p
  have hj : PrimeFactorUnimodality.primeAt j = p := Nat.nth_count hp
  have hindex : N + A <= j := by
    by_contra hn
    have hbad := PrimeFactorUnimodality.primeAt_strictMono (Nat.lt_of_not_ge hn)
    rw [hj] at hbad
    exact not_lt_of_ge hpN hbad
  let n := j - A
  have hn : N <= n := by dsimp [n]; omega
  have hna : n + A = j := by dsimp [n]; omega
  have hprime := PrimeFactorUnimodality.prime_primeAt (n + B)
  rw [heq n hn, hna, hj] at hprime
  exact hprime

/-- A finite limiting difference forces the two prime-index shifts to agree. -/
theorem prime_shifts_eq_of_difference_tendsto (A B : Nat) (c : Real)
    (hlim : Tendsto (fun n : Nat =>
      (PrimeFactorUnimodality.primeAt (n + B) : Real) -
        (PrimeFactorUnimodality.primeAt (n + A) : Real)) atTop (nhds c)) :
    A = B := by
  apply le_antisymm
  . by_contra hn
    have hBA : B < A := Nat.lt_of_not_ge hn
    have hneg : Tendsto (fun n : Nat =>
        (PrimeFactorUnimodality.primeAt (n + A) : Real) -
          (PrimeFactorUnimodality.primeAt (n + B) : Real)) atTop (nhds (-c)) := by
      apply hlim.neg.congr'
      exact Eventually.of_forall (fun _ => by ring)
    exact not_tendsto_prime_difference_of_lt B A hBA (-c) hneg
  . by_contra hn
    exact not_tendsto_prime_difference_of_lt A B (Nat.lt_of_not_ge hn) c hlim

/-- Matching reciprocal prime tails determine the scale, intercept and index shift. -/
theorem profile_parameters_eq_of_tail_match
    (a b : Nat -> Real) (A B : Nat) (nu1 nu2 c1 c2 : Real)
    (hnu1 : 0 < nu1) (hnu2 : 0 < nu2)
    (hmatch : forall n, a (n + A) = b (n + B))
    (ha : Tendsto (fun n : Nat =>
      1 / a n - (PrimeFactorUnimodality.primeAt n : Real) / nu1 - c1)
        atTop (nhds 0))
    (hb : Tendsto (fun n : Nat =>
      1 / b n - (PrimeFactorUnimodality.primeAt n : Real) / nu2 - c2)
        atTop (nhds 0)) :
    nu1 = nu2 /\ c1 = c2 /\ A = B := by
  have hscale := profile_scale_eq_of_tail_match
    a b A B nu1 nu2 c1 c2 hnu1 hnu2 hmatch ha hb
  have hb' : Tendsto (fun n : Nat =>
      1 / b n - (PrimeFactorUnimodality.primeAt n : Real) / nu1 - c2)
        atTop (nhds 0) := by
    rw [hscale]
    exact hb
  have hdiff := tendsto_prime_shift_difference_of_tail_match
    a b A B nu1 c1 c2 hnu1 hmatch ha hb'
  have hshift := prime_shifts_eq_of_difference_tendsto A B (nu1 * (c1 - c2)) hdiff
  have hconstant : Tendsto (fun _ : Nat => (0 : Real)) atTop
      (nhds (nu1 * (c1 - c2))) := by
    apply hdiff.congr'
    exact Eventually.of_forall (fun _ => by rw [hshift]; ring)
  have hzero : nu1 * (c1 - c2) = 0 :=
    tendsto_nhds_unique hconstant tendsto_const_nhds
  have hintercept : c1 = c2 :=
    sub_eq_zero.mp ((mul_eq_zero.mp hzero).resolve_left (ne_of_gt hnu1))
  exact And.intro hscale (And.intro hintercept hshift)

end PrimeFactorOscillations

/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Tactic.Linarith
import PrimeFactorOscillations.Mathlib.NumberTheory.ArithmeticFunction.LeastPrimeOwner
import PrimeFactorOscillations.Proof.PrimeClassDeletion.PrimeReturnWave

/-!
# The deterministic future source fixed by the actual prime prefix

There is no random origin, independence hypothesis or full-period average.
Both the weighted source and its two-time return overlaps are retained.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.PrimeClassDeletion

noncomputable def primeReturnHit (p n : Nat) : Real := by
  classical
  exact if Dvd.dvd p n then 1 else 0

noncomputable def pastPrimeOpening (Y n : Nat) : Real :=
  ((Finset.Icc 2 Y).filter Nat.Prime).prod (fun p => 1 - primeReturnHit p n)

/-- The actual earlier primes decide every opening up to the square
of the known prefix. -/
theorem prime_iff_no_past_prime_divisor (Y n : Nat)
    (hY : 1 <= Y) (hYn : Y < n) (hnY : n <= Y * Y) :
    Nat.Prime n <-> (forall p : Nat, Nat.Prime p -> p <= Y ->
      Not (Dvd.dvd p n)) := by
  constructor
  case mp =>
    intro hn p hp hpY hpn
    cases (Nat.dvd_prime hn).mp hpn with
    | inl h => exact hp.ne_one h
    | inr h => omega
  case mpr =>
    intro hnone
    by_contra hn
    have hn1 : Not (n = 1) := by omega
    have hq := Nat.minFac_prime hn1
    have hqdvd := Nat.minFac_dvd n
    have hqle : n.minFac <= n :=
      Nat.le_of_dvd (by omega : 0 < n) hqdvd
    have hqne : Not (n.minFac = n) := by
      intro heq
      rw [heq] at hq
      exact hn hq
    have hqlt : n.minFac < n := by omega
    have hsq := ArithmeticFunction.prime_owner_square_le
      n n.minFac hqdvd hqlt rfl
    have hqY : n.minFac <= Y := by nlinarith only [hsq, hnY]
    exact hnone n.minFac hq hqY hqdvd

theorem pastPrimeOpening_eq_prime_indicator (Y n : Nat)
    (hY : 1 <= Y) (hYn : Y < n) (hnY : n <= Y * Y) :
    pastPrimeOpening Y n = if Nat.Prime n then 1 else 0 := by
  classical
  by_cases hn : Nat.Prime n
  case pos =>
    rw [ite_eq_left hn]
    unfold pastPrimeOpening
    apply Finset.prod_eq_one
    intro p hp
    have hpdata := Finset.mem_filter.mp hp
    have hpY := (Finset.mem_Icc.mp hpdata.1).2
    have hnot := (prime_iff_no_past_prime_divisor Y n hY hYn hnY).mp hn
      p hpdata.2 hpY
    simp [primeReturnHit, hnot]
  case neg =>
    rw [ite_eq_right hn]
    have hn1 : Not (n = 1) := by omega
    have hq := Nat.minFac_prime hn1
    have hqdvd := Nat.minFac_dvd n
    have hqle : n.minFac <= n :=
      Nat.le_of_dvd (by omega : 0 < n) hqdvd
    have hqne : Not (n.minFac = n) := by
      intro heq
      rw [heq] at hq
      exact hn hq
    have hqlt : n.minFac < n := by omega
    have hsq := ArithmeticFunction.prime_owner_square_le
      n n.minFac hqdvd hqlt rfl
    have hqY : n.minFac <= Y := by nlinarith only [hsq, hnY]
    have hmem : Membership.mem ((Finset.Icc 2 Y).filter Nat.Prime) n.minFac :=
      Finset.mem_filter.mpr (And.intro
        (Finset.mem_Icc.mpr (And.intro hq.two_le hqY)) hq)
    unfold pastPrimeOpening
    apply Finset.prod_eq_zero hmem
    simp [primeReturnHit, hqdvd]

/-- The two-time mixed return term is retained before any estimate. -/
theorem pastPrimeOpening_two_time (Y n m : Nat) :
    pastPrimeOpening Y n * pastPrimeOpening Y m =
      ((Finset.Icc 2 Y).filter Nat.Prime).prod
        (fun p => 1 - primeReturnHit p n - primeReturnHit p m +
          primeReturnHit p n * primeReturnHit p m) := by
  unfold pastPrimeOpening
  rw [<- Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro p _
  ring

/-- An exact finite source identity; the same fixed mask occurs at
every future integer, with all prime-wave overlaps included. -/
theorem theta_future_eq_past_prime_mask (Y T : Nat)
    (hY : 1 <= Y) (hYT : Y <= T) (hTY : T <= Y * Y) :
    Chebyshev.theta (T : Real) - Chebyshev.theta (Y : Real) =
      (Finset.Ioc Y T).sum
        (fun n => Real.log (n : Real) * pastPrimeOpening Y n) := by
  have hsplit : Chebyshev.theta (T : Real) =
      Chebyshev.theta (Y : Real) +
        (Finset.Ioc Y T).sum primeWaveBirth := by
    induction T, hYT using Nat.le_induction with
    | base => simp
    | succ T hYT ih =>
        have ih' := ih ((Nat.le_succ T).trans hTY)
        rw [primeWaveTheta_nat_succ, ih', Finset.sum_Ioc_succ_top hYT]
        ring
  have hsum : (Finset.Ioc Y T).sum primeWaveBirth =
      (Finset.Ioc Y T).sum
        (fun n => Real.log (n : Real) * pastPrimeOpening Y n) := by
    apply Finset.sum_congr rfl
    intro n hn
    have hnt := Finset.mem_Ioc.mp hn
    rw [pastPrimeOpening_eq_prime_indicator Y n hY hnt.1 (hnt.2.trans hTY)]
    by_cases hp : Nat.Prime n <;> simp [primeWaveBirth, hp]
  rw [hsum] at hsplit
  linarith only [hsplit]

/-- The exact signed consumer for the actual x-theta(x) wave. -/
theorem primeWaveHeadroom_future_past_mask (Y T : Nat)
    (hY : 1 <= Y) (hYT : Y <= T) (hTY : T <= Y * Y) :
    primeWaveHeadroom (T : Real) - primeWaveHeadroom (Y : Real) =
      ((T : Real) - (Y : Real)) -
        (Finset.Ioc Y T).sum
          (fun n => Real.log (n : Real) * pastPrimeOpening Y n) := by
  have hsource := theta_future_eq_past_prime_mask Y T hY hYT hTY
  unfold primeWaveHeadroom
  linarith only [hsource]

noncomputable def properPrimeReturnHit (p n : Nat) : Real :=
  if p < n then primeReturnHit p n else 0

noncomputable def pastProperPrimeOpening (Y n : Nat) : Real :=
  ((Finset.Icc 2 Y).filter Nat.Prime).prod
    (fun p => 1 - properPrimeReturnHit p n)

/-- The proper-return support retains past prime births instead of
incorrectly treating a birth as its own return. -/
theorem pastProperPrimeOpening_eq_prime_indicator (Y n : Nat)
    (_hY : 1 <= Y) (hn : 2 <= n) (hnY : n <= Y * Y) :
    pastProperPrimeOpening Y n = if Nat.Prime n then 1 else 0 := by
  classical
  by_cases hprime : Nat.Prime n
  case pos =>
    rw [ite_eq_left hprime]
    unfold pastProperPrimeOpening
    apply Finset.prod_eq_one
    intro p hp
    have hpprime := (Finset.mem_filter.mp hp).2
    by_cases hpn : p < n
    case pos =>
      have hnot : Not (Dvd.dvd p n) := by
        intro hdiv
        cases (Nat.dvd_prime hprime).mp hdiv with
        | inl h => exact hpprime.ne_one h
        | inr h => omega
      simp [properPrimeReturnHit, primeReturnHit, hpn, hnot]
    case neg =>
      simp [properPrimeReturnHit, hpn]
  case neg =>
    rw [ite_eq_right hprime]
    have hn1 : Not (n = 1) := by omega
    have hq := Nat.minFac_prime hn1
    have hqdvd := Nat.minFac_dvd n
    have hqle : n.minFac <= n := Nat.le_of_dvd (by omega : 0 < n) hqdvd
    have hqne : Not (n.minFac = n) := by
      intro heq
      rw [heq] at hq
      exact hprime hq
    have hqlt : n.minFac < n := by omega
    have hsq := ArithmeticFunction.prime_owner_square_le
      n n.minFac hqdvd hqlt rfl
    have hqY : n.minFac <= Y := by nlinarith only [hsq, hnY]
    have hmem : Membership.mem ((Finset.Icc 2 Y).filter Nat.Prime) n.minFac :=
      Finset.mem_filter.mpr (And.intro
        (Finset.mem_Icc.mpr (And.intro hq.two_le hqY)) hq)
    unfold pastProperPrimeOpening
    apply Finset.prod_eq_zero hmem
    simp [properPrimeReturnHit, primeReturnHit, hqlt, hqdvd]

/-- Past births and future openings have different return supports.
The past birth's own prime factor is retained in the FUTURE slot. -/
theorem pastBirth_futureOpening_two_time (Y a n : Nat) :
    pastProperPrimeOpening Y a * pastPrimeOpening Y n =
      ((Finset.Icc 2 Y).filter Nat.Prime).prod
        (fun p => 1 - properPrimeReturnHit p a - primeReturnHit p n +
          properPrimeReturnHit p a * primeReturnHit p n) := by
  unfold pastProperPrimeOpening pastPrimeOpening
  rw [<- Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro p _
  ring

/-- After the square-root cutoff has already been sieved, extra past
prime factors add no new future openings on that square horizon.
This concerns the opening indicator, not the logarithmic return energy. -/
theorem pastPrimeOpening_cutoff_stability (H Y n : Nat)
    (hH : 1 <= H) (hHY : H <= Y) (hYn : Y < n)
    (hnH : n <= H * H) :
    pastPrimeOpening Y n = pastPrimeOpening H n := by
  have hY : 1 <= Y := hH.trans hHY
  have hnY : n <= Y * Y := by
    nlinarith only [hHY, hnH]
  rw [pastPrimeOpening_eq_prime_indicator Y n hY hYn hnY,
    pastPrimeOpening_eq_prime_indicator H n hH (hHY.trans_lt hYn) hnH]

end PrimeFactorOscillations.PrimeClassDeletion


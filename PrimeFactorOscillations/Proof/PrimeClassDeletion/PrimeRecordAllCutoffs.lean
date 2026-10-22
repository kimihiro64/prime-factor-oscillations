/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Proof.PrimeClassDeletion.PrimeRecordEnergyBounds

/-! # From strict record-prime energy bounds to every real cutoff

Positive running records are attained at strict jumps, including ties
after a previous record. The finite initial record value is retained in
the final uniform constant. The energy bound is an independent hypothesis.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.PrimeClassDeletion

open PrimeFactorUnimodality
open PrimeFactorOscillations.PrimeClassSampling

theorem clockRecord_monotone (e : Nat -> Real) : Monotone (clockRecord e) := by
  apply monotone_nat_of_le_succ
  intro n
  exact le_max_left _ _

theorem clockRecord_positive_attained (e : Nat -> Real) (n : Nat)
    (hpos : 0 < clockRecord e n) :
    exists i : Nat, And (i < n) (And (0 < clockRecordIncrement e i)
      (And (clockRecord e (i + 1) = clockRecord e n) (e i = clockRecord e n))) := by
  revert hpos
  induction n with
  | zero =>
      intro hpos
      exact False.elim ((lt_irrefl (0 : Real)) hpos)
  | succ n ih =>
      intro hpos
      by_cases h : clockRecord e n < e n
      case pos =>
        have hnext : clockRecord e (n + 1) = e n := max_eq_right h.le
        refine Exists.intro n (And.intro (Nat.lt_succ_self n)
          (And.intro ?_ (And.intro rfl hnext.symm)))
        change 0 < clockRecord e (n + 1) - clockRecord e n
        rw [hnext]
        exact sub_pos.mpr h
      case neg =>
        have hnext : clockRecord e (n + 1) = clockRecord e n :=
          max_eq_left (le_of_not_gt h)
        have hprev : 0 < clockRecord e n := by simpa only [hnext] using hpos
        choose i hi using ih hprev
        exact Exists.intro i (And.intro (hi.1.trans (Nat.lt_succ_self n))
          (And.intro hi.2.1 (And.intro (hi.2.2.1.trans hnext.symm)
            (hi.2.2.2.trans hnext.symm))))

theorem primeRecord_positive_attained (x : Real) (hx : 2 <= x)
    (hpos : 0 < greedyPrimeRegulatorReal x) :
    exists p : Nat, And (Nat.Prime p) (And ((p : Real) <= x)
      (And (0 < primeRecordJump p)
        (And (greedyPrimeRegulatorReal (p : Real) = greedyPrimeRegulatorReal x)
          (greedyPrimeRegulatorReal (p : Real) =
            primeClassThetaReal Set.univ (p : Real) - (p : Real))))) := by
  choose i hi using clockRecord_positive_attained primeClockError
    (primeCutoffLength (Nat.floor x)) hpos
  let p := primeAt i
  have hp : Nat.Prime p := prime_primeAt i
  have hpX : p <= Nat.floor x := (primeAt_le_cutoff_iff i (Nat.floor x)).mpr hi.1
  have hpR : (p : Real) <= x :=
    (Nat.cast_le.mpr hpX).trans (Nat.floor_le (by linarith only [hx]))
  have hvalue : greedyPrimeRegulatorReal (p : Real) = greedyPrimeRegulatorReal x := by
    change greedyPrimeRegulator (Nat.floor (p : Real)) = _
    rw [Nat.floor_natCast]
    change greedyPrimeRegulator (primeAt i) = _
    rw [greedyPrimeRegulator_at_primeAt]
    exact hi.2.2.1
  have herror : primeClockError i =
      primeClassThetaReal Set.univ (p : Real) - (p : Real) := by
    simpa only [primeClassThetaReal, Nat.floor_natCast, p] using primeClockError_eq_theta i
  have hjump : 0 < primeRecordJump p := by
    simpa only [primeRecordJump, p, primeCount_primeAt] using hi.2.1
  exact Exists.intro p (And.intro hp (And.intro hpR (And.intro hjump
    (And.intro hvalue (hvalue.trans (hi.2.2.2.symm.trans herror))))))

theorem primeRecordEnergy_all_cutoff_bound (a K X0 : Real) (ha : 0 < a)
    (hK : 0 <= K) (hX0 : 2 <= X0)
    (hsource : forall p : Nat, Nat.Prime p -> X0 <= (p : Real) ->
      0 < primeRecordJump p -> primeRecordSignedEnergy (p : Real) <=
        K * (p : Real) ^ (2 * a))
    (x : Real) (hx : 2 <= x) :
    greedyPrimeRegulatorReal x <=
      (greedyPrimeRegulatorReal X0 + (1 / a + Real.sqrt (2 * K))) * x ^ a := by
  let B := 1 / a + Real.sqrt (2 * K)
  change greedyPrimeRegulatorReal x <= (greedyPrimeRegulatorReal X0 + B) * x ^ a
  have hB : 0 <= B := add_nonneg (div_nonneg zero_le_one ha.le) (Real.sqrt_nonneg _)
  have hbase : 0 <= greedyPrimeRegulatorReal X0 :=
    clockRecord_nonneg primeClockError (primeCutoffLength (Nat.floor X0))
  have hy : 0 <= x ^ a := Real.rpow_nonneg (by linarith only [hx]) a
  have hy1 : 1 <= x ^ a := Real.one_le_rpow (by linarith only [hx]) ha.le
  by_cases hzero : greedyPrimeRegulatorReal x = 0
  case pos =>
    rw [hzero]
    exact mul_nonneg (add_nonneg hbase hB) hy
  case neg =>
    have hnonneg : 0 <= greedyPrimeRegulatorReal x :=
      clockRecord_nonneg primeClockError (primeCutoffLength (Nat.floor x))
    have hpos : 0 < greedyPrimeRegulatorReal x :=
      lt_of_le_of_ne hnonneg (fun hz => hzero hz.symm)
    choose p hp using primeRecord_positive_attained x hx hpos
    have hvalue := hp.2.2.2.1
    by_cases hlarge : X0 <= (p : Real)
    case pos =>
      have hroot := primeRecordEnergy_power_bound_explicit (p : Real) a K
        (hX0.trans hlarge) ha hK hp.2.2.2.2 (hsource p hp.1 hlarge hp.2.2.1)
      rw [hvalue] at hroot
      have hpow : (p : Real) ^ a <= x ^ a :=
        Real.rpow_le_rpow (Nat.cast_nonneg p) hp.2.1 ha.le
      have hmain : greedyPrimeRegulatorReal x <= B * x ^ a :=
        hroot.trans (mul_le_mul_of_nonneg_left hpow hB)
      have hextra : 0 <= greedyPrimeRegulatorReal X0 * x ^ a := mul_nonneg hbase hy
      nlinarith only [hmain, hextra]
    case neg =>
      have hpX0 : p <= Nat.floor X0 := Nat.le_floor (le_of_lt (lt_of_not_ge hlarge))
      have hn : primeCutoffLength p <= primeCutoffLength (Nat.floor X0) :=
        Nat.count_monotone Nat.Prime (Nat.add_le_add_right hpX0 1)
      have hsmall : greedyPrimeRegulatorReal x <= greedyPrimeRegulatorReal X0 := by
        rw [<- hvalue]
        change greedyPrimeRegulator (Nat.floor (p : Real)) <= _
        rw [Nat.floor_natCast]
        exact clockRecord_monotone primeClockError hn
      have hscaled : greedyPrimeRegulatorReal X0 * 1 <=
          greedyPrimeRegulatorReal X0 * x ^ a := mul_le_mul_of_nonneg_left hy1 hbase
      have hextra : 0 <= B * x ^ a := mul_nonneg hB hy
      nlinarith only [hsmall, hscaled, hextra]

end PrimeFactorOscillations.PrimeClassDeletion

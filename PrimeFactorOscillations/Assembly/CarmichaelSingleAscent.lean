/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.CarmichaelPastPrimeModuli
import PrimeFactorOscillations.Helpers.SinglePairAscentCriterion

/-!
# A single Carmichael-weighted prime pair detects RH at smooth conductors

The original normalized return-correlation weight is evaluated at one actual
localized prime. Smoothness keeps that prime a unit at unrestricted conductor
size. The complete signed excess is bounded above by a constant iff RH holds.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

open Filter PrimeFactorUnimodality

def carmichaelSingleAscentExcess (H : Nat) (a q : Nat -> Nat)
    [forall X, NeZero (q X)] (S : Nat -> Finset Nat.Primes) (X : Nat) : Real :=
  carmichaelPrimeWeight (q X) (S X) (primeAt (a X)) *
    localAscentPairExcess H X (a X)

theorem carmichaelSingleAscentWeight_ge_half_eventually
    (H : Nat) (a : Nat -> Nat) (hs : LocalAscentLocator H a)
    (q : Nat -> Nat) [forall X, NeZero (q X)]
    (S : Nat -> Finset Nat.Primes)
    (hDiv : forall X, forall l : S X,
      Dvd.dvd (l.val : Nat) (Monoid.exponent (Units (ZMod (q X)))))
    (hOdd : forall X, forall l : S X, Not ((l.val : Nat) = 2))
    (hSmooth : Filter.Eventually (fun X : Nat => Nat.largestPrimeFactor (q X) <= X) atTop) :
    Filter.Eventually (fun X : Nat =>
      (1 / 2 : Real) <= carmichaelPrimeWeight (q X) (S X) (primeAt (a X))) atTop := by
  filter_upwards [hs, hSmooth] with X hPair hQ
  have hLow : X < primeAt (a X) := by
    have hNat : X <= primeAt (a X) - 1 := by exact_mod_cast hPair.2.2.1
    have hp := (prime_primeAt (a X)).two_le
    omega
  have hUnit := Nat.isUnit_largestPrimeFactor_of_le_cutoff
    (N := q X) (n := primeAt (a X)) (y := X)
    (prime_primeAt (a X)).pos hQ
    (by simpa only [Nat.largestPrimeFactor_of_prime (prime_primeAt (a X))] using hLow)
  have hActual : IsUnit (primeAt (a X) : ZMod (q X)) := by
    simpa only [Nat.largestPrimeFactor_of_prime (prime_primeAt (a X))] using hUnit
  have hCoprime := (ZMod.isUnit_iff_coprime _ _).mp hActual
  exact carmichaelPrimeWeight_ge_half (q X) (S X) (hDiv X) (hOdd X) _ hCoprime

theorem carmichaelSingleAscentExcess_unbounded_of_not_RH
    (H : Nat) (a : Nat -> Nat) (hs : LocalAscentLocator H a)
    (q : Nat -> Nat) [forall X, NeZero (q X)]
    (S : Nat -> Finset Nat.Primes)
    (hDiv : forall X, forall l : S X,
      Dvd.dvd (l.val : Nat) (Monoid.exponent (Units (ZMod (q X)))))
    (hOdd : forall X, forall l : S X, Not ((l.val : Nat) = 2))
    (hSmooth : Filter.Eventually (fun X : Nat => Nat.largestPrimeFactor (q X) <= X) atTop)
    (hNotRH : Not RiemannHypothesis) (C X0 : Real) :
    exists n : Nat, X0 < (n : Real) /\ C < carmichaelSingleAscentExcess H a q S n := by
  simpa only [carmichaelSingleAscentExcess] using
    singleWeightedAscent_unbounded_of_not_RH H a hs
      (fun X => carmichaelPrimeWeight (q X) (S X) (primeAt (a X))) (carmichaelSingleAscentWeight_ge_half_eventually H a hs q S hDiv hOdd hSmooth) hNotRH C X0

theorem riemannHypothesis_iff_eventually_carmichaelSingleAscent_bounded
    (H : Nat) (a : Nat -> Nat) (hs : LocalAscentLocator H a)
    (q : Nat -> Nat) [forall X, NeZero (q X)]
    (S : Nat -> Finset Nat.Primes)
    (hDiv : forall X, forall l : S X,
      Dvd.dvd (l.val : Nat) (Monoid.exponent (Units (ZMod (q X)))))
    (hOdd : forall X, forall l : S X, Not ((l.val : Nat) = 2))
    (hSmooth : Filter.Eventually (fun X : Nat => Nat.largestPrimeFactor (q X) <= X) atTop) :
    RiemannHypothesis <->
      exists C : Real, Filter.Eventually (fun X : Nat =>
        carmichaelSingleAscentExcess H a q S X <= C) atTop := by
  simpa only [carmichaelSingleAscentExcess] using
    riemannHypothesis_iff_eventually_singleWeightedAscent_bounded H a hs
      (fun X => carmichaelPrimeWeight (q X) (S X) (primeAt (a X))) (carmichaelSingleAscentWeight_ge_half_eventually H a hs q S hDiv hOdd hSmooth)

theorem riemannHypothesis_iff_eventually_carmichaelSingleAscent_nonpos
    (H : Nat) (a : Nat -> Nat) (hs : LocalAscentLocator H a)
    (q : Nat -> Nat) [forall X, NeZero (q X)]
    (S : Nat -> Finset Nat.Primes)
    (hDiv : forall X, forall l : S X,
      Dvd.dvd (l.val : Nat) (Monoid.exponent (Units (ZMod (q X)))))
    (hOdd : forall X, forall l : S X, Not ((l.val : Nat) = 2))
    (hSmooth : Filter.Eventually (fun X : Nat => Nat.largestPrimeFactor (q X) <= X) atTop) :
    RiemannHypothesis <->
      Filter.Eventually (fun X : Nat =>
        carmichaelSingleAscentExcess H a q S X <= 0) atTop := by
  simpa only [carmichaelSingleAscentExcess] using
    riemannHypothesis_iff_eventually_singleWeightedAscent_nonpos H a hs
      (fun X => carmichaelPrimeWeight (q X) (S X) (primeAt (a X))) (carmichaelSingleAscentWeight_ge_half_eventually H a hs q S hDiv hOdd hSmooth)

end PrimeFactorOscillations

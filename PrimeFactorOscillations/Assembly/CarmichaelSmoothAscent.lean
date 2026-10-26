/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.CarmichaelAscentCriterion
import PrimeFactorOscillations.Helpers.UniformWeightedAscentCriterion
import PrimeFactorOscillations.Mathlib.NumberTheory.SmoothNumbers.ResidueSupport

/-!
# Carmichael ascent criteria at unrestricted smooth conductors

The existing largest-prime-factor residue support theorem makes every
selected future prime a unit modulo an X-smooth conductor. The entire native
return kernel is retained. There is no modulus-size bound, no exchange of
sampling limits, and no replacement of the signed observable.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

open Filter PrimeFactorUnimodality

theorem carmichaelLocalAscent_coprime_eventually_of_smooth
    (H : Nat) (m : Nat -> Nat) (a : (X : Nat) -> Fin (m X) -> Nat)
    (hs : LocalAscentSampling H m a)
    (q : Nat -> Nat) [forall X, NeZero (q X)]
    (hSmooth : Filter.Eventually (fun X : Nat => Nat.largestPrimeFactor (q X) <= X) atTop) :
    Filter.Eventually (fun X : Nat => forall i,
      Nat.Coprime (primeAt (a X i)) (q X)) atTop := by
  filter_upwards [hs.2, hSmooth] with X hPair hQ
  intro i
  have hLow : X < primeAt (a X i) := by
    have hNat : X <= primeAt (a X i) - 1 := by exact_mod_cast (hPair.2 i).2.2.1
    have hp := (prime_primeAt (a X i)).two_le
    omega
  have hUnit := Nat.isUnit_largestPrimeFactor_of_le_cutoff
    (N := q X) (n := primeAt (a X i)) (y := X)
    (prime_primeAt (a X i)).pos hQ
    (by simpa only [Nat.largestPrimeFactor_of_prime (prime_primeAt (a X i))] using hLow)
  have hActual : IsUnit (primeAt (a X i) : ZMod (q X)) := by
    simpa only [Nat.largestPrimeFactor_of_prime (prime_primeAt (a X i))] using hUnit
  exact (ZMod.isUnit_iff_coprime _ _).mp hActual

theorem carmichaelLocalAscentWeight_ge_half_eventually_of_smooth
    (H : Nat) (m : Nat -> Nat) (a : (X : Nat) -> Fin (m X) -> Nat)
    (hs : LocalAscentSampling H m a)
    (q : Nat -> Nat) [forall X, NeZero (q X)]
    (S : Nat -> Finset Nat.Primes)
    (hDiv : forall X, forall l : S X,
      Dvd.dvd (l.val : Nat) (Monoid.exponent (Units (ZMod (q X)))))
    (hOdd : forall X, forall l : S X, Not ((l.val : Nat) = 2))
    (hSmooth : Filter.Eventually (fun X : Nat => Nat.largestPrimeFactor (q X) <= X) atTop) :
    Filter.Eventually (fun X : Nat => forall i,
      (1 / 2 : Real) <= carmichaelLocalAscentWeight m a q S X i) atTop := by
  filter_upwards [carmichaelLocalAscent_coprime_eventually_of_smooth H m a hs q hSmooth] with X hX
  intro i
  exact carmichaelPrimeWeight_ge_half (q X) (S X) (hDiv X) (hOdd X) _ (hX i)

theorem carmichaelSmoothAscentExcess_common_lower_eventually
    (H : Nat) (m : Nat -> Nat) (a : (X : Nat) -> Fin (m X) -> Nat)
    (hs : LocalAscentSampling H m a)
    (q : Nat -> Nat) [forall X, NeZero (q X)]
    (S : Nat -> Finset Nat.Primes)
    (hDiv : forall X, forall l : S X,
      Dvd.dvd (l.val : Nat) (Monoid.exponent (Units (ZMod (q X)))))
    (hOdd : forall X, forall l : S X, Not ((l.val : Nat) = 2))
    (hSmooth : Filter.Eventually (fun X : Nat => Nat.largestPrimeFactor (q X) <= X) atTop) :
    Filter.Eventually (fun X : Nat => forall B : Real, 0 <= B ->
      (forall i, B <= localAscentPairExcess H X (a X i)) ->
      (m X : Real) * B / 2 <= carmichaelLocalAscentExcess H m a q S X) atTop := by
  filter_upwards [carmichaelLocalAscentWeight_ge_half_eventually_of_smooth
    H m a hs q S hDiv hOdd hSmooth] with X hX
  intro B hB hPoint
  exact weightedLocalAscentExcess_lower_of_half_le H m a _ X hX B hB hPoint

theorem carmichaelSmoothAscentExcess_unbounded_of_not_RH
    (H : Nat) (m : Nat -> Nat) (a : (X : Nat) -> Fin (m X) -> Nat)
    (hs : LocalAscentSampling H m a)
    (q : Nat -> Nat) [forall X, NeZero (q X)]
    (S : Nat -> Finset Nat.Primes)
    (hDiv : forall X, forall l : S X,
      Dvd.dvd (l.val : Nat) (Monoid.exponent (Units (ZMod (q X)))))
    (hOdd : forall X, forall l : S X, Not ((l.val : Nat) = 2))
    (hSmooth : Filter.Eventually (fun X : Nat => Nat.largestPrimeFactor (q X) <= X) atTop)
    (hNotRH : Not RiemannHypothesis) (C X0 : Real) (hC : 0 < C) :
    exists n : Nat, X0 < (n : Real) /\
      C * (n : Real) ^ (7 / 10 : Real) < carmichaelLocalAscentExcess H m a q S n :=
  positiveWeightedLocalAscentExcess_unbounded_of_not_RH H m a hs _
    (carmichaelLocalAscentWeight_ge_half_eventually_of_smooth H m a hs q S hDiv hOdd hSmooth)
    hNotRH C X0 hC

theorem riemannHypothesis_iff_eventually_carmichaelSmoothAscent_nonpos
    (H : Nat) (m : Nat -> Nat) (a : (X : Nat) -> Fin (m X) -> Nat)
    (hs : LocalAscentSampling H m a)
    (q : Nat -> Nat) [forall X, NeZero (q X)]
    (S : Nat -> Finset Nat.Primes)
    (hDiv : forall X, forall l : S X,
      Dvd.dvd (l.val : Nat) (Monoid.exponent (Units (ZMod (q X)))))
    (hOdd : forall X, forall l : S X, Not ((l.val : Nat) = 2))
    (hSmooth : Filter.Eventually (fun X : Nat => Nat.largestPrimeFactor (q X) <= X) atTop) :
    RiemannHypothesis <-> Filter.Eventually
      (fun X : Nat => carmichaelLocalAscentExcess H m a q S X <= 0) atTop :=
  riemannHypothesis_iff_eventually_positiveWeightedAscent_nonpos H m a hs _
    (carmichaelLocalAscentWeight_ge_half_eventually_of_smooth H m a hs q S hDiv hOdd hSmooth)

theorem riemannHypothesis_iff_eventually_carmichaelSmoothAscent_power_upper
    (H : Nat) (m : Nat -> Nat) (a : (X : Nat) -> Fin (m X) -> Nat)
    (hs : LocalAscentSampling H m a)
    (q : Nat -> Nat) [forall X, NeZero (q X)]
    (S : Nat -> Finset Nat.Primes)
    (hDiv : forall X, forall l : S X,
      Dvd.dvd (l.val : Nat) (Monoid.exponent (Units (ZMod (q X)))))
    (hOdd : forall X, forall l : S X, Not ((l.val : Nat) = 2))
    (hSmooth : Filter.Eventually (fun X : Nat => Nat.largestPrimeFactor (q X) <= X) atTop) :
    RiemannHypothesis <->
      exists C : Real, 0 < C /\ Filter.Eventually (fun X : Nat =>
        carmichaelLocalAscentExcess H m a q S X <= C * (X : Real) ^ (7 / 10 : Real)) atTop :=
  riemannHypothesis_iff_eventually_positiveWeightedAscent_power_upper H m a hs _
    (carmichaelLocalAscentWeight_ge_half_eventually_of_smooth H m a hs q S hDiv hOdd hSmooth)

end PrimeFactorOscillations

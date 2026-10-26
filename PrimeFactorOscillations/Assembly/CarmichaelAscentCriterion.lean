/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.CarmichaelCorrelationFloor
import PrimeFactorOscillations.Helpers.WeightedLocalizedAscentCriterion

/-!
# Local ascent RH criteria with varying native Carmichael return weights

The group, modulus and odd return packet may change at every cutoff. The
native unit correlation is extended by zero on nonunits. A modulus budget
discards at most half the actual selected prime witnesses; the pointwise
correlation floor preserves the rest without a progression-density premise.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

open Filter PrimeFactorUnimodality CarmichaelCorrelation CarmichaelCorrelationFloor

def carmichaelPrimeWeight (c : Nat) [NeZero c]
    (S : Finset Nat.Primes) (p : Nat) : Real := by
  classical
  exact if h : Nat.Coprime p c then
    kernel (vacancyWeight (G := Units (ZMod c)) (Monoid.exponent (Units (ZMod c))) S)
      (ZMod.unitOfCoprime p h)
    else 0

theorem carmichaelPrimeWeight_nonneg (c : Nat) [NeZero c]
    (S : Finset Nat.Primes)
    (hDiv : forall l : S, Dvd.dvd (l.val : Nat) (Monoid.exponent (Units (ZMod c))))
    (hOdd : forall l : S, Not ((l.val : Nat) = 2)) (p : Nat) :
    0 <= carmichaelPrimeWeight c S p := by
  classical
  unfold carmichaelPrimeWeight
  split_ifs with h
  . exact (by norm_num : (0 : Real) <= 1 / 2).trans
      (canonical_odd_kernel_ge_half S hDiv hOdd (ZMod.unitOfCoprime p h))
  . exact le_rfl

theorem carmichaelPrimeWeight_ge_half (c : Nat) [NeZero c]
    (S : Finset Nat.Primes)
    (hDiv : forall l : S, Dvd.dvd (l.val : Nat) (Monoid.exponent (Units (ZMod c))))
    (hOdd : forall l : S, Not ((l.val : Nat) = 2)) (p : Nat)
    (hp : Nat.Coprime p c) :
    (1 / 2 : Real) <= carmichaelPrimeWeight c S p := by
  classical
  simp only [carmichaelPrimeWeight, dite_eq_left hp]
  exact canonical_odd_kernel_ge_half S hDiv hOdd (ZMod.unitOfCoprime p hp)

theorem carmichaelPrimeWeight_eq_zero_of_not_coprime (c : Nat) [NeZero c]
    (S : Finset Nat.Primes) (p : Nat) (hp : Not (Nat.Coprime p c)) :
    carmichaelPrimeWeight c S p = 0 := by
  classical
  simp only [carmichaelPrimeWeight, dite_eq_right hp]

def carmichaelLocalAscentWeight (m : Nat -> Nat)
    (a : (X : Nat) -> Fin (m X) -> Nat)
    (q : Nat -> Nat) [forall X, NeZero (q X)]
    (S : Nat -> Finset Nat.Primes) (X : Nat) (i : Fin (m X)) : Real :=
  carmichaelPrimeWeight (q X) (S X) (primeAt (a X i))

def carmichaelLocalAscentExcess (H : Nat) (m : Nat -> Nat)
    (a : (X : Nat) -> Fin (m X) -> Nat)
    (q : Nat -> Nat) [forall X, NeZero (q X)]
    (S : Nat -> Finset Nat.Primes) (X : Nat) : Real :=
  weightedLocalAscentExcess H m a (carmichaelLocalAscentWeight m a q S) X

theorem carmichaelLocalAscent_unit_weights (m : Nat -> Nat)
    (a : (X : Nat) -> Fin (m X) -> Nat)
    (q : Nat -> Nat) [forall X, NeZero (q X)]
    (S : Nat -> Finset Nat.Primes)
    (hDiv : forall X, forall l : S X,
      Dvd.dvd (l.val : Nat) (Monoid.exponent (Units (ZMod (q X)))))
    (hOdd : forall X, forall l : S X, Not ((l.val : Nat) = 2)) :
    LocalAscentUnitWeights m a q (carmichaelLocalAscentWeight m a q S) := by
  intro X i
  exact And.intro (carmichaelPrimeWeight_nonneg (q X) (S X) (hDiv X) (hOdd X) _)
    (fun hp => carmichaelPrimeWeight_ge_half (q X) (S X) (hDiv X) (hOdd X) _ hp)

theorem carmichaelLocalAscentExcess_unbounded_of_not_RH
    (H : Nat) (m : Nat -> Nat) (a : (X : Nat) -> Fin (m X) -> Nat)
    (hs : LocalAscentSampling H m a)
    (q : Nat -> Nat) [forall X, NeZero (q X)]
    (S : Nat -> Finset Nat.Primes)
    (hDiv : forall X, forall l : S X,
      Dvd.dvd (l.val : Nat) (Monoid.exponent (Units (ZMod (q X)))))
    (hOdd : forall X, forall l : S X, Not ((l.val : Nat) = 2))
    (hBudget : Filter.Eventually (fun X : Nat => q X <= X ^ (m X / 2)) atTop)
    (hNotRH : Not RiemannHypothesis) (C X0 : Real) (hC : 0 < C) :
    exists n : Nat, X0 < (n : Real) /\
      C * (n : Real) ^ (7 / 10 : Real) < carmichaelLocalAscentExcess H m a q S n := by
  have hQ : Filter.Eventually (fun X : Nat =>
      And (0 < q X) (q X <= X ^ (m X / 2))) atTop := by
    filter_upwards [hBudget] with X hX
    exact And.intro (Nat.pos_of_ne_zero (NeZero.ne (q X))) hX
  exact weightedLocalAscentExcess_unbounded_of_not_RH H m a hs q _
    (carmichaelLocalAscent_unit_weights m a q S hDiv hOdd) hQ hNotRH C X0 hC

theorem riemannHypothesis_iff_eventually_carmichaelLocalAscentExcess_nonpos
    (H : Nat) (m : Nat -> Nat) (a : (X : Nat) -> Fin (m X) -> Nat)
    (hs : LocalAscentSampling H m a)
    (q : Nat -> Nat) [forall X, NeZero (q X)]
    (S : Nat -> Finset Nat.Primes)
    (hDiv : forall X, forall l : S X,
      Dvd.dvd (l.val : Nat) (Monoid.exponent (Units (ZMod (q X)))))
    (hOdd : forall X, forall l : S X, Not ((l.val : Nat) = 2))
    (hBudget : Filter.Eventually (fun X : Nat => q X <= X ^ (m X / 2)) atTop) :
    RiemannHypothesis <-> Filter.Eventually
      (fun X : Nat => carmichaelLocalAscentExcess H m a q S X <= 0) atTop := by
  have hQ : Filter.Eventually (fun X : Nat =>
      And (0 < q X) (q X <= X ^ (m X / 2))) atTop := by
    filter_upwards [hBudget] with X hX
    exact And.intro (Nat.pos_of_ne_zero (NeZero.ne (q X))) hX
  exact riemannHypothesis_iff_eventually_weightedLocalAscentExcess_nonpos H m a hs q _
    (carmichaelLocalAscent_unit_weights m a q S hDiv hOdd) hQ

theorem riemannHypothesis_iff_eventually_carmichaelLocalAscentExcess_power_upper
    (H : Nat) (m : Nat -> Nat) (a : (X : Nat) -> Fin (m X) -> Nat)
    (hs : LocalAscentSampling H m a)
    (q : Nat -> Nat) [forall X, NeZero (q X)]
    (S : Nat -> Finset Nat.Primes)
    (hDiv : forall X, forall l : S X,
      Dvd.dvd (l.val : Nat) (Monoid.exponent (Units (ZMod (q X)))))
    (hOdd : forall X, forall l : S X, Not ((l.val : Nat) = 2))
    (hBudget : Filter.Eventually (fun X : Nat => q X <= X ^ (m X / 2)) atTop) :
    RiemannHypothesis <->
      exists C : Real, 0 < C /\ Filter.Eventually (fun X : Nat =>
        carmichaelLocalAscentExcess H m a q S X <= C * (X : Real) ^ (7 / 10 : Real)) atTop := by
  have hQ : Filter.Eventually (fun X : Nat =>
      And (0 < q X) (q X <= X ^ (m X / 2))) atTop := by
    filter_upwards [hBudget] with X hX
    exact And.intro (Nat.pos_of_ne_zero (NeZero.ne (q X))) hX
  exact riemannHypothesis_iff_eventually_weightedLocalAscentExcess_power_upper H m a hs q _
    (carmichaelLocalAscent_unit_weights m a q S hDiv hOdd) hQ

end PrimeFactorOscillations

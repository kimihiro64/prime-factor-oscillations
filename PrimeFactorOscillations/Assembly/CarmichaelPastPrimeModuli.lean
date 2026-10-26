/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.NumberTheory.Primorial
import PrimeFactorOscillations.Assembly.CarmichaelSmoothAscent

/-!
# All-past-prime Carmichael probes

Arbitrary powers of the factorial and primorial are actual smooth conductors.
The exponent may vary without any growth restriction. Both RH criteria use
the original native correlation and the original local ascent sampling.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

open Filter

def carmichaelFactorialModulus (e : Nat -> Nat) (X : Nat) : Nat :=
  (Nat.factorial X) ^ e X

def carmichaelPrimorialModulus (e : Nat -> Nat) (X : Nat) : Nat :=
  (_root_.primorial X) ^ e X

instance carmichaelFactorialModulus_neZero (e : Nat -> Nat) (X : Nat) :
    NeZero (carmichaelFactorialModulus e X) :=
  NeZero.mk (ne_of_gt (pow_pos (Nat.factorial_pos X) (e X)))

instance carmichaelPrimorialModulus_neZero (e : Nat -> Nat) (X : Nat) :
    NeZero (carmichaelPrimorialModulus e X) :=
  NeZero.mk (ne_of_gt (pow_pos (_root_.primorial_pos X) (e X)))

theorem carmichaelFactorialModulus_smooth_eventually (e : Nat -> Nat) :
    Filter.Eventually (fun X : Nat =>
      Nat.largestPrimeFactor (carmichaelFactorialModulus e X) <= X) atTop := by
  filter_upwards [eventually_ge_atTop (1 : Nat)] with X hX
  apply (Nat.largestPrimeFactor_le_iff _ _).mpr
  refine And.intro hX ?_
  intro p hp
  have hPrime := (Nat.mem_primeFactors.mp hp).1
  have hDiv : Dvd.dvd p ((Nat.factorial X) ^ e X) := (Nat.mem_primeFactors.mp hp).2.1
  exact (Nat.Prime.dvd_factorial hPrime).mp (hPrime.dvd_of_dvd_pow hDiv)

theorem carmichaelPrimorialModulus_smooth_eventually (e : Nat -> Nat) :
    Filter.Eventually (fun X : Nat =>
      Nat.largestPrimeFactor (carmichaelPrimorialModulus e X) <= X) atTop := by
  filter_upwards [eventually_ge_atTop (1 : Nat)] with X hX
  apply (Nat.largestPrimeFactor_le_iff _ _).mpr
  refine And.intro hX ?_
  intro p hp
  have hPrime := (Nat.mem_primeFactors.mp hp).1
  have hDiv : Dvd.dvd p ((_root_.primorial X) ^ e X) := (Nat.mem_primeFactors.mp hp).2.1
  exact hPrime.dvd_primorial_iff.mp (hPrime.dvd_of_dvd_pow hDiv)

theorem riemannHypothesis_iff_eventually_factorialCarmichaelAscent_nonpos
    (H : Nat) (m : Nat -> Nat) (a : (X : Nat) -> Fin (m X) -> Nat)
    (hs : LocalAscentSampling H m a) (e : Nat -> Nat)
    (S : Nat -> Finset Nat.Primes)
    (hDiv : forall X, forall l : S X,
      Dvd.dvd (l.val : Nat)
        (Monoid.exponent (Units (ZMod (carmichaelFactorialModulus e X)))))
    (hOdd : forall X, forall l : S X, Not ((l.val : Nat) = 2)) :
    RiemannHypothesis <-> Filter.Eventually (fun X : Nat =>
      carmichaelLocalAscentExcess H m a (carmichaelFactorialModulus e) S X <= 0) atTop :=
  riemannHypothesis_iff_eventually_carmichaelSmoothAscent_nonpos H m a hs
    (carmichaelFactorialModulus e) S hDiv hOdd (carmichaelFactorialModulus_smooth_eventually e)

theorem riemannHypothesis_iff_eventually_factorialCarmichaelAscent_power_upper
    (H : Nat) (m : Nat -> Nat) (a : (X : Nat) -> Fin (m X) -> Nat)
    (hs : LocalAscentSampling H m a) (e : Nat -> Nat)
    (S : Nat -> Finset Nat.Primes)
    (hDiv : forall X, forall l : S X,
      Dvd.dvd (l.val : Nat)
        (Monoid.exponent (Units (ZMod (carmichaelFactorialModulus e X)))))
    (hOdd : forall X, forall l : S X, Not ((l.val : Nat) = 2)) :
    RiemannHypothesis <->
      exists C : Real, 0 < C /\ Filter.Eventually (fun X : Nat =>
        carmichaelLocalAscentExcess H m a (carmichaelFactorialModulus e) S X <=
          C * (X : Real) ^ (7 / 10 : Real)) atTop :=
  riemannHypothesis_iff_eventually_carmichaelSmoothAscent_power_upper H m a hs
    (carmichaelFactorialModulus e) S hDiv hOdd (carmichaelFactorialModulus_smooth_eventually e)

theorem riemannHypothesis_iff_eventually_primorialCarmichaelAscent_nonpos
    (H : Nat) (m : Nat -> Nat) (a : (X : Nat) -> Fin (m X) -> Nat)
    (hs : LocalAscentSampling H m a) (e : Nat -> Nat)
    (S : Nat -> Finset Nat.Primes)
    (hDiv : forall X, forall l : S X,
      Dvd.dvd (l.val : Nat)
        (Monoid.exponent (Units (ZMod (carmichaelPrimorialModulus e X)))))
    (hOdd : forall X, forall l : S X, Not ((l.val : Nat) = 2)) :
    RiemannHypothesis <-> Filter.Eventually (fun X : Nat =>
      carmichaelLocalAscentExcess H m a (carmichaelPrimorialModulus e) S X <= 0) atTop :=
  riemannHypothesis_iff_eventually_carmichaelSmoothAscent_nonpos H m a hs
    (carmichaelPrimorialModulus e) S hDiv hOdd (carmichaelPrimorialModulus_smooth_eventually e)

theorem riemannHypothesis_iff_eventually_primorialCarmichaelAscent_power_upper
    (H : Nat) (m : Nat -> Nat) (a : (X : Nat) -> Fin (m X) -> Nat)
    (hs : LocalAscentSampling H m a) (e : Nat -> Nat)
    (S : Nat -> Finset Nat.Primes)
    (hDiv : forall X, forall l : S X,
      Dvd.dvd (l.val : Nat)
        (Monoid.exponent (Units (ZMod (carmichaelPrimorialModulus e X)))))
    (hOdd : forall X, forall l : S X, Not ((l.val : Nat) = 2)) :
    RiemannHypothesis <->
      exists C : Real, 0 < C /\ Filter.Eventually (fun X : Nat =>
        carmichaelLocalAscentExcess H m a (carmichaelPrimorialModulus e) S X <=
          C * (X : Real) ^ (7 / 10 : Real)) atTop :=
  riemannHypothesis_iff_eventually_carmichaelSmoothAscent_power_upper H m a hs
    (carmichaelPrimorialModulus e) S hDiv hOdd (carmichaelPrimorialModulus_smooth_eventually e)

end PrimeFactorOscillations

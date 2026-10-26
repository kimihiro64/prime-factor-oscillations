/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.SinglePairAscentWindow

/-!
# Bounded-error RH criteria from a single localized prime pair

An eventual positive lower weight preserves both the sign criterion and the
constant-upper-bound criterion. No count growth or independence is used.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

open Filter

theorem singleWeightedAscent_nonpos_eventually_of_RH
    (H : Nat) (a : Nat -> Nat) (hs : LocalAscentLocator H a)
    (w : Nat -> Real)
    (hw : Filter.Eventually (fun X : Nat => (1 / 2 : Real) <= w X) atTop)
    (hRH : RiemannHypothesis) :
    Filter.Eventually (fun X : Nat => w X * localAscentPairExcess H X (a X) <= 0) atTop := by
  filter_upwards [singleAscentPairExcess_nonpos_eventually_of_RH H a hs hRH, hw]
    with X hD hW
  exact mul_nonpos_of_nonneg_of_nonpos (by linarith) hD

theorem singleWeightedAscent_unbounded_of_not_RH
    (H : Nat) (a : Nat -> Nat) (hs : LocalAscentLocator H a)
    (w : Nat -> Real)
    (hw : Filter.Eventually (fun X : Nat => (1 / 2 : Real) <= w X) atTop)
    (hNotRH : Not RiemannHypothesis) (C X0 : Real) :
    exists n : Nat, X0 < (n : Real) /\ C < w n * localAscentPairExcess H n (a n) := by
  choose N hN using eventually_atTop.mp hw
  choose n hn hD using singleAscentPairExcess_unbounded_of_not_RH H a hs hNotRH
    (2 * max C 0 + 1) (max X0 (N : Real))
  have hnN : N <= n := by
    have hh := (le_max_right X0 (N : Real)).trans hn.le
    exact_mod_cast hh
  have hNonneg : 0 <= localAscentPairExcess H n (a n) := by
    have hh := le_max_right C (0 : Real)
    linarith
  have hWeight := mul_le_mul_of_nonneg_right (hN n hnN) hNonneg
  refine Exists.intro n (And.intro ((le_max_left _ _).trans_lt hn) ?_)
  linarith [le_max_left C (0 : Real)]

theorem riemannHypothesis_iff_eventually_singleWeightedAscent_bounded
    (H : Nat) (a : Nat -> Nat) (hs : LocalAscentLocator H a)
    (w : Nat -> Real)
    (hw : Filter.Eventually (fun X : Nat => (1 / 2 : Real) <= w X) atTop) :
    RiemannHypothesis <->
      exists C : Real, Filter.Eventually (fun X : Nat =>
        w X * localAscentPairExcess H X (a X) <= C) atTop := by
  constructor
  . intro hRH
    exact Exists.intro 0 (singleWeightedAscent_nonpos_eventually_of_RH H a hs w hw hRH)
  . intro hUpper
    choose C hC using hUpper
    choose N hN using eventually_atTop.mp hC
    by_contra hNotRH
    choose n hn hD using singleWeightedAscent_unbounded_of_not_RH H a hs w hw hNotRH C N
    have hnN : N <= n := by exact_mod_cast hn.le
    exact (not_lt_of_ge (hN n hnN)) hD

theorem riemannHypothesis_iff_eventually_singleWeightedAscent_nonpos
    (H : Nat) (a : Nat -> Nat) (hs : LocalAscentLocator H a)
    (w : Nat -> Real)
    (hw : Filter.Eventually (fun X : Nat => (1 / 2 : Real) <= w X) atTop) :
    RiemannHypothesis <->
      Filter.Eventually (fun X : Nat =>
        w X * localAscentPairExcess H X (a X) <= 0) atTop := by
  constructor
  . exact singleWeightedAscent_nonpos_eventually_of_RH H a hs w hw
  . intro hUpper
    exact (riemannHypothesis_iff_eventually_singleWeightedAscent_bounded H a hs w hw).mpr
      (Exists.intro 0 hUpper)

theorem riemannHypothesis_iff_eventually_singleAscent_bounded
    (H : Nat) (a : Nat -> Nat) (hs : LocalAscentLocator H a) :
    RiemannHypothesis <->
      exists C : Real, Filter.Eventually (fun X : Nat =>
        localAscentPairExcess H X (a X) <= C) atTop := by
  simpa only [one_mul] using
    riemannHypothesis_iff_eventually_singleWeightedAscent_bounded H a hs (fun _ => 1)
      (Filter.Eventually.of_forall (fun _ => by norm_num))

theorem riemannHypothesis_iff_eventually_singleAscent_nonpos
    (H : Nat) (a : Nat -> Nat) (hs : LocalAscentLocator H a) :
    RiemannHypothesis <->
      Filter.Eventually (fun X : Nat => localAscentPairExcess H X (a X) <= 0) atTop := by
  simpa only [one_mul] using
    riemannHypothesis_iff_eventually_singleWeightedAscent_nonpos H a hs (fun _ => 1)
      (Filter.Eventually.of_forall (fun _ => by norm_num))

end PrimeFactorOscillations

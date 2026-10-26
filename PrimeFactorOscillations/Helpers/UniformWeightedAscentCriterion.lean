/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.WeightedLocalizedAscentCriterion

/-!
# Positive local ascent weights without any modulus-size budget

Only an eventual lower floor on the actual weights is needed. The common
signed excursion and every grid rounding loss are inherited from the proved
pointwise window. No modification of the observable or conductor estimate
is introduced.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

open Filter

theorem weightedLocalAscentExcess_lower_of_half_le
    (H : Nat) (m : Nat -> Nat) (a : (X : Nat) -> Fin (m X) -> Nat)
    (w : (X : Nat) -> Fin (m X) -> Real) (X : Nat)
    (hw : forall i, (1 / 2 : Real) <= w X i) (B : Real) (hB : 0 <= B)
    (hPoint : forall i, B <= localAscentPairExcess H X (a X i)) :
    (m X : Real) * B / 2 <= weightedLocalAscentExcess H m a w X := by
  calc
    (m X : Real) * B / 2 = Finset.univ.sum
        (fun _ : Fin (m X) => (1 / 2 : Real) * B) := by
      simp [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm]
    _ <= _ := by
      apply Finset.sum_le_sum
      intro i _
      have hw0 : 0 <= w X i := (by norm_num : (0 : Real) <= 1 / 2).trans (hw i)
      exact (mul_le_mul_of_nonneg_right (hw i) hB).trans
        (mul_le_mul_of_nonneg_left (hPoint i) hw0)

theorem positiveWeightedLocalAscentExcess_unbounded_of_not_RH
    (H : Nat) (m : Nat -> Nat) (a : (X : Nat) -> Fin (m X) -> Nat)
    (hs : LocalAscentSampling H m a)
    (w : (X : Nat) -> Fin (m X) -> Real)
    (hw : Filter.Eventually (fun X : Nat => forall i, (1 / 2 : Real) <= w X i) atTop)
    (hNotRH : Not RiemannHypothesis) (C X0 : Real) (hC : 0 < C) :
    exists n : Nat, X0 < (n : Real) /\
      C * (n : Real) ^ (7 / 10 : Real) < weightedLocalAscentExcess H m a w n := by
  choose N hN using eventually_atTop.mp hw
  choose n hn B hB hAmp hPoint using localAscentPairExcess_common_large_window_of_not_RH
    H m a hs hNotRH (2 * C) (max X0 (N : Real)) (by positivity)
  have hnN : N <= n := by
    have h := (le_max_right X0 (N : Real)).trans hn.le
    exact_mod_cast h
  have hLower := weightedLocalAscentExcess_lower_of_half_le H m a w n (hN n hnN) B hB hPoint
  refine Exists.intro n (And.intro ((le_max_left _ _).trans_lt hn) ?_)
  linarith

theorem riemannHypothesis_iff_eventually_positiveWeightedAscent_nonpos
    (H : Nat) (m : Nat -> Nat) (a : (X : Nat) -> Fin (m X) -> Nat)
    (hs : LocalAscentSampling H m a)
    (w : (X : Nat) -> Fin (m X) -> Real)
    (hw : Filter.Eventually (fun X : Nat => forall i, (1 / 2 : Real) <= w X i) atTop) :
    RiemannHypothesis <->
      Filter.Eventually (fun X : Nat => weightedLocalAscentExcess H m a w X <= 0) atTop := by
  constructor
  . intro hRH
    filter_upwards [hw, localAscentPairExcess_nonpos_eventually_of_RH H m a hs hRH] with X hW hX
    apply Finset.sum_nonpos
    intro i _
    have hw0 : 0 <= w X i := (by norm_num : (0 : Real) <= 1 / 2).trans (hW i)
    exact mul_nonpos_of_nonneg_of_nonpos hw0 (hX i)
  . intro hEvent
    by_contra hNotRH
    choose N hN using eventually_atTop.mp hEvent
    choose n hn hEx using positiveWeightedLocalAscentExcess_unbounded_of_not_RH
      H m a hs w hw hNotRH 1 (N : Real) (by norm_num)
    have hnN : N <= n := by exact_mod_cast hn.le
    have hNon : 0 <= (n : Real) ^ (7 / 10 : Real) := Real.rpow_nonneg (Nat.cast_nonneg _) _
    linarith [hN n hnN]

theorem riemannHypothesis_iff_eventually_positiveWeightedAscent_power_upper
    (H : Nat) (m : Nat -> Nat) (a : (X : Nat) -> Fin (m X) -> Nat)
    (hs : LocalAscentSampling H m a)
    (w : (X : Nat) -> Fin (m X) -> Real)
    (hw : Filter.Eventually (fun X : Nat => forall i, (1 / 2 : Real) <= w X i) atTop) :
    RiemannHypothesis <->
      exists C : Real, 0 < C /\ Filter.Eventually (fun X : Nat =>
        weightedLocalAscentExcess H m a w X <= C * (X : Real) ^ (7 / 10 : Real)) atTop := by
  constructor
  . intro hRH
    have hEvent := (riemannHypothesis_iff_eventually_positiveWeightedAscent_nonpos H m a hs w hw).mp hRH
    refine Exists.intro 1 (And.intro (by norm_num) ?_)
    filter_upwards [hEvent] with X hX
    have hNon : 0 <= (X : Real) ^ (7 / 10 : Real) := Real.rpow_nonneg (Nat.cast_nonneg _) _
    linarith
  . intro h
    choose C hC hEvent using h
    by_contra hNotRH
    choose N hN using eventually_atTop.mp hEvent
    choose n hn hEx using positiveWeightedLocalAscentExcess_unbounded_of_not_RH
      H m a hs w hw hNotRH C (N : Real) hC
    have hnN : N <= n := by exact_mod_cast hn.le
    exact (not_lt_of_ge (hN n hnN)) hEx

end PrimeFactorOscillations

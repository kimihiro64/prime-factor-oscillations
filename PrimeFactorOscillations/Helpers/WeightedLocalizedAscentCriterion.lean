/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.AscentModulusBudget
import PrimeFactorOscillations.Helpers.LocalizedAscentPointwise

/-!
# Weighted local ascent criteria with moving moduli

Nonnegative weights bounded below by one half on unit witnesses preserve the
pointwise bad-zero excursion. Moduli as large as X^(m(X)/2) discard at most
half the distinct actual witness primes. The full signed grid excess is used.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

open Filter PrimeFactorUnimodality

def weightedLocalAscentExcess (H : Nat) (m : Nat -> Nat)
    (a : (X : Nat) -> Fin (m X) -> Nat)
    (w : (X : Nat) -> Fin (m X) -> Real) (X : Nat) : Real :=
  Finset.univ.sum (fun i => w X i * localAscentPairExcess H X (a X i))

def LocalAscentUnitWeights (m : Nat -> Nat)
    (a : (X : Nat) -> Fin (m X) -> Nat) (q : Nat -> Nat)
    (w : (X : Nat) -> Fin (m X) -> Real) : Prop :=
  forall X i, And (0 <= w X i)
    (Nat.Coprime (primeAt (a X i)) (q X) -> (1 / 2 : Real) <= w X i)

theorem localAscent_unit_weight_mass_lower (m : Nat -> Nat)
    (a : (X : Nat) -> Fin (m X) -> Nat) (q : Nat -> Nat)
    (w : (X : Nat) -> Fin (m X) -> Real)
    (hw : LocalAscentUnitWeights m a q w) (X : Nat)
    (hCount : (m X : Real) / 2 <= (localAscentUnitIndices m a X (q X)).card) :
    (m X : Real) / 4 <= Finset.univ.sum (w X) := by
  classical
  let T := localAscentUnitIndices m a X (q X)
  have hMass : (T.card : Real) / 2 <= Finset.univ.sum (w X) := by
    calc
      _ = T.sum (fun _ => (1 / 2 : Real)) := by simp [div_eq_mul_inv]
      _ <= _ := by
        change (Finset.univ.filter
          (fun i : Fin (m X) => Nat.Coprime (primeAt (a X i)) (q X))).sum
            (fun _ => (1 / 2 : Real)) <= _
        rw [Finset.sum_filter]
        apply Finset.sum_le_sum
        intro i _
        split_ifs with hi
        . exact (hw X i).2 hi
        . exact (hw X i).1
  change (m X : Real) / 2 <= (T.card : Real) at hCount
  linarith

theorem weightedLocalAscentExcess_common_lower
    (H : Nat) (m : Nat -> Nat) (a : (X : Nat) -> Fin (m X) -> Nat)
    (q : Nat -> Nat) (w : (X : Nat) -> Fin (m X) -> Real)
    (hw : LocalAscentUnitWeights m a q w) (X : Nat)
    (hCount : (m X : Real) / 2 <= (localAscentUnitIndices m a X (q X)).card)
    (B : Real) (hB : 0 <= B)
    (hPoint : forall i, B <= localAscentPairExcess H X (a X i)) :
    (m X : Real) * B / 4 <= weightedLocalAscentExcess H m a w X := by
  have hMass := localAscent_unit_weight_mass_lower m a q w hw X hCount
  have hGain (i : Fin (m X)) :
      B * w X i <= w X i * localAscentPairExcess H X (a X i) := by
    simpa only [mul_comm B (w X i)] using
      mul_le_mul_of_nonneg_left (hPoint i) (hw X i).1
  calc
    (m X : Real) * B / 4 = B * ((m X : Real) / 4) := by ring
    _ <= B * Finset.univ.sum (w X) := mul_le_mul_of_nonneg_left hMass hB
    _ = Finset.univ.sum (fun i => B * w X i) := Finset.mul_sum _ _ _
    _ <= _ := Finset.sum_le_sum (fun i _ => hGain i)

theorem weightedLocalAscentExcess_nonpos_eventually_of_RH
    (H : Nat) (m : Nat -> Nat) (a : (X : Nat) -> Fin (m X) -> Nat)
    (hs : LocalAscentSampling H m a)
    (q : Nat -> Nat) (w : (X : Nat) -> Fin (m X) -> Real)
    (hw : LocalAscentUnitWeights m a q w) (hRH : RiemannHypothesis) :
    Filter.Eventually (fun X : Nat => weightedLocalAscentExcess H m a w X <= 0) atTop := by
  filter_upwards [localAscentPairExcess_nonpos_eventually_of_RH H m a hs hRH] with X hX
  exact Finset.sum_nonpos (fun i _ => mul_nonpos_of_nonneg_of_nonpos (hw X i).1 (hX i))

theorem weightedLocalAscentExcess_unbounded_of_not_RH
    (H : Nat) (m : Nat -> Nat) (a : (X : Nat) -> Fin (m X) -> Nat)
    (hs : LocalAscentSampling H m a)
    (q : Nat -> Nat) (w : (X : Nat) -> Fin (m X) -> Real)
    (hw : LocalAscentUnitWeights m a q w)
    (hBudget : Filter.Eventually (fun X : Nat =>
      And (0 < q X) (q X <= X ^ (m X / 2))) atTop)
    (hNotRH : Not RiemannHypothesis) (C X0 : Real) (hC : 0 < C) :
    exists n : Nat, X0 < (n : Real) /\
      C * (n : Real) ^ (7 / 10 : Real) < weightedLocalAscentExcess H m a w n := by
  have hCounts : Filter.Eventually (fun X : Nat =>
      (m X : Real) / 2 <= (localAscentUnitIndices m a X (q X)).card) atTop := by
    filter_upwards [hs.2, hBudget, eventually_ge_atTop (2 : Nat)] with X hPair hQ hX
    have hLow (i : Fin (m X)) : X <= primeAt (a X i) := by
      have hNat : X <= primeAt (a X i) - 1 := by exact_mod_cast (hPair.2 i).2.2.1
      omega
    exact localAscent_unit_count_ge_half m a X (q X) hX hQ.1 hPair.1 hLow hQ.2
  choose N hN using eventually_atTop.mp hCounts
  choose n hn B hB hAmp hPoint using localAscentPairExcess_common_large_window_of_not_RH
    H m a hs hNotRH (4 * C) (max X0 (N : Real)) (by positivity)
  have hnN : N <= n := by
    have h := (le_max_right X0 (N : Real)).trans hn.le
    exact_mod_cast h
  have hLower := weightedLocalAscentExcess_common_lower H m a q w hw n (hN n hnN) B hB hPoint
  refine Exists.intro n (And.intro ((le_max_left _ _).trans_lt hn) ?_)
  linarith

theorem riemannHypothesis_iff_eventually_weightedLocalAscentExcess_nonpos
    (H : Nat) (m : Nat -> Nat) (a : (X : Nat) -> Fin (m X) -> Nat)
    (hs : LocalAscentSampling H m a)
    (q : Nat -> Nat) (w : (X : Nat) -> Fin (m X) -> Real)
    (hw : LocalAscentUnitWeights m a q w)
    (hBudget : Filter.Eventually (fun X : Nat =>
      And (0 < q X) (q X <= X ^ (m X / 2))) atTop) :
    RiemannHypothesis <->
      Filter.Eventually (fun X : Nat => weightedLocalAscentExcess H m a w X <= 0) atTop := by
  constructor
  . exact weightedLocalAscentExcess_nonpos_eventually_of_RH H m a hs q w hw
  . intro hEvent
    by_contra hNotRH
    choose N hN using eventually_atTop.mp hEvent
    choose n hn hEx using weightedLocalAscentExcess_unbounded_of_not_RH
      H m a hs q w hw hBudget hNotRH 1 (N : Real) (by norm_num)
    have hnN : N <= n := by exact_mod_cast hn.le
    have hNon : 0 <= (n : Real) ^ (7 / 10 : Real) := Real.rpow_nonneg (Nat.cast_nonneg _) _
    linarith [hN n hnN]

theorem riemannHypothesis_iff_eventually_weightedLocalAscentExcess_power_upper
    (H : Nat) (m : Nat -> Nat) (a : (X : Nat) -> Fin (m X) -> Nat)
    (hs : LocalAscentSampling H m a)
    (q : Nat -> Nat) (w : (X : Nat) -> Fin (m X) -> Real)
    (hw : LocalAscentUnitWeights m a q w)
    (hBudget : Filter.Eventually (fun X : Nat =>
      And (0 < q X) (q X <= X ^ (m X / 2))) atTop) :
    RiemannHypothesis <->
      exists C : Real, 0 < C /\ Filter.Eventually (fun X : Nat =>
        weightedLocalAscentExcess H m a w X <= C * (X : Real) ^ (7 / 10 : Real)) atTop := by
  constructor
  . intro hRH
    refine Exists.intro 1 (And.intro (by norm_num) ?_)
    filter_upwards [weightedLocalAscentExcess_nonpos_eventually_of_RH H m a hs q w hw hRH] with X hX
    have hNon : 0 <= (X : Real) ^ (7 / 10 : Real) := Real.rpow_nonneg (Nat.cast_nonneg _) _
    linarith
  . intro h
    choose C hC hEvent using h
    by_contra hNotRH
    choose N hN using eventually_atTop.mp hEvent
    choose n hn hEx using weightedLocalAscentExcess_unbounded_of_not_RH
      H m a hs q w hw hBudget hNotRH C (N : Real) hC
    have hnN : N <= n := by exact_mod_cast hn.le
    exact (not_lt_of_ge (hN n hnN)) hEx

end PrimeFactorOscillations

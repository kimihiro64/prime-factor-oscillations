/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Assembly.DetectorPackets.GaussianTwoDiagonal
import PrimeFactorOscillations.Helpers.UniformCarrierCoefficients

/-!
# CarrierIndexedAdmission

Maintained extraction of completed detector/packet proof components.
All original theorem hypotheses and retained proof bodies are preserved.
This module alone asserts no improved zero-free boundary.
-/

set_option autoImplicit false
set_option Elab.async false

/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

/-!
# Actual probability admission for indexed amplified packets

The cutoff is (height i)^4, with a separate admissible single-prime mark
for each indexed coefficient. The uniform constant precedes the index
types, heights, coefficients, rows, kernels and amplifier scale.
No arithmetic moment estimate or zero-free hypothesis is assumed.
-/


noncomputable section
namespace PrimeFactorOscillations.UniformCarrier.IndexedAdmission

theorem exists_uniform_point_observations :
    exists n0 : Nat, exists C : Real, 100 <= n0 /\ 0 < C /\
      forall d : Nat, 2 <= d ->
      forall n : Nat, n0 <= n ->
      forall c : Complex, forall hc : norm c <= (n : Real),
      exists O : CoefficientObservation d n c hc,
        norm (O.value - c) <= C / (n : Real) ^ (d - 1) := by
  classical
  choose n0 C hn0 hC hData using exists_probability_coefficients
  refine Exists.intro n0 (Exists.intro C (And.intro hn0 (And.intro hC ?_)))
  intro d hd n hn c hc
  let target : Nat -> Complex := fun m => if m = n then c else 0
  have hTarget : forall m : Nat, norm (target m) <= (m : Real) := by
    intro m
    by_cases hm : m = n
    . subst m
      simpa only [target, if_pos rfl] using hc
    . simp only [target, if_neg hm, norm_zero]
      exact Nat.cast_nonneg m
  choose a hError hObserved hSmall using hData d hd target hTarget
  choose O hO using hObserved n hn
  have hnz : Not (n = 0) := by omega
  have hErr := hError n hnz
  rw [hO] at hErr
  have hTransport : forall (v w : Complex) (hv : norm v <= (n : Real))
      (hw : norm w <= (n : Real)), v = w ->
      forall V : CoefficientObservation d n v hv,
      exists W : CoefficientObservation d n w hw, W.value = V.value := by
    intro v w hv hw heq V
    subst w
    exact Exists.intro V rfl
  have hAt : target n = c := by simp only [target, if_pos rfl]
  choose W hW using hTransport (target n) c (hTarget n) hc hAt O
  refine Exists.intro W ?_
  rw [hW, <- hAt]
  exact hErr

theorem exists_uniform_indexed_amplified_observations :
    exists n0 : Nat, exists C : Real, 100 <= n0 /\ 0 < C /\
      forall (I R : Type) (rows : Finset R) (s : Finset I)
        (height : I -> Nat) (a : I -> Complex)
        (ha : forall i, norm (a i) <= (height i : Real))
        (K : R -> I -> Complex) (P : R -> Complex)
        (D Y Crows Ccols Camp : Real),
      0 < D -> 0 <= Y -> 0 <= Crows -> 0 <= Ccols -> 0 <= Camp ->
      (forall i, Membership.mem s i -> n0 <= height i) ->
      (forall i, Membership.mem s i -> D <= (height i : Real)) ->
      (s.card : Real) <= Ccols * D ->
      (rows.card : Real) <= Crows * D ^ 4 ->
      (forall r, Membership.mem rows r ->
        forall i, Membership.mem s i -> norm (K r i) <= 1) ->
      (forall r, Membership.mem rows r -> norm (P r) <= Camp * Y) ->
      exists f : I -> Complex,
        (forall i, Membership.mem s i ->
          exists O : CoefficientObservation 4 (height i) (a i) (ha i),
            f i = O.value) /\
        (forall i, Membership.mem s i ->
          norm (f i - a i) <= C / D ^ 3) /\
        AmplifiedMoment.energy rows s f K P <=
          2 * AmplifiedMoment.energy rows s a K P +
            2 * Crows * Ccols ^ 2 * Camp ^ 2 * C ^ 2 * Y ^ 2 := by
  classical
  choose n0 C hn0 hC hPoint using exists_uniform_point_observations
  refine Exists.intro n0 (Exists.intro C (And.intro hn0 (And.intro hC ?_)))
  intro I R rows s height a ha K P D Y Crows Ccols Camp
    hD hY hRows hCols hAmp hLarge hLower hS hT hK hP
  have hPoints : forall i, Membership.mem s i ->
      exists O : CoefficientObservation 4 (height i) (a i) (ha i),
        norm (O.value - a i) <= C / (height i : Real) ^ 3 := by
    intro i hi
    simpa only [Nat.reduceSub] using
      hPoint 4 (by norm_num) (height i) (hLarge i hi) (a i) (ha i)
  choose O hO using hPoints
  let f : I -> Complex := fun i =>
    if hi : Membership.mem s i then (O i hi).value else a i
  have hObserved : forall i, Membership.mem s i ->
      exists W : CoefficientObservation 4 (height i) (a i) (ha i),
        f i = W.value := by
    intro i hi
    exact Exists.intro (O i hi) (by simp only [f, dif_pos hi])
  have hError : forall i, Membership.mem s i ->
      norm (f i - a i) <= C / D ^ 3 := by
    intro i hi
    simp only [f, dif_pos hi]
    have hPow : D ^ 3 <= (height i : Real) ^ 3 := by
      gcongr
      exact hLower i hi
    exact (hO i hi).trans
      (div_le_div_of_nonneg_left hC.le (pow_pos hD 3) hPow)
  refine Exists.intro f (And.intro hObserved (And.intro hError ?_))
  exact GaussianTwoDiagonal.carrier_quartic_arbitrary_amplifier
    rows s a f K P D Y Crows Ccols Camp C
    hD hY hRows hCols hAmp hC.le hS hT hError hK hP

end PrimeFactorOscillations.UniformCarrier.IndexedAdmission


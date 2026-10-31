/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.FiniteFieldIntegerNativeReturn

/-!
# Quantitative separation of native integer-pair probability profiles

The actual local weights have a naturally scaled squared distance.
Its exact trace identity retains all six correlations. The existing full
signed estimate then gives a uniform lower bound tending to twice log two,
including all shared-endpoint cases and the existing least-gap frames.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace PrimeFactorOscillations.FiniteFieldIntegerSignature
open Filter IntegerQuadraticCharacter
open FiniteFieldIntegerWindowTransfer FiniteFieldIntegerCharacter
open FiniteFieldIntegerGapWindows PrimeProfileRigidity

def integerNativeWeight (n h p : Nat) : Real :=
  if hp : Nat.Prime p then
    letI : Fact (Nat.Prime p) := Fact.mk hp
    FiniteField.traceFreePairWeight (n : ZMod p) (h : ZMod p)
  else 0

def nativeWeightEnergy (n h m k Y X : Nat) : Real :=
  ((Finset.Ico Y X).filter Nat.Prime).sum (fun p =>
    (((p : Real) - 3) ^ 2 / (p : Real)) *
      (integerNativeWeight n h p - integerNativeWeight m k p) ^ 2)

def nativeMetricDefect (C : Real) (Q : Nat) : Real :=
  2 * (2 * PrimeFactorUnimodality.mertensErrorConstant / Real.log (preciseCore Q : Real)) +
    10 * relativeError C Q

theorem native_weight_scaled_difference (n h m k p : Nat) [Fact (Nat.Prime p)]
    (hn : Nat.Prime n) (hnh : Nat.Prime (n + h))
    (hm : Nat.Prime m) (hmk : Nat.Prime (m + k))
    (hp5 : 5 <= p) (hpn : p < n) (hpm : p < m) :
    ((p : Real) - 3) *
      (FiniteField.traceFreePairWeight (n : ZMod p) (h : ZMod p) -
        FiniteField.traceFreePairWeight (m : ZMod p) (k : ZMod p)) =
      nativeTrace n h p - nativeTrace m k p := by
  have hmod (P : Nat) (hP : Nat.Prime P) (hpP : p < P) :
      Not ((P : ZMod p) = 0) := by
    intro hz
    have hd := (ZMod.natCast_eq_zero_iff P p).mp hz
    cases (Nat.dvd_prime hP).mp hd with
    | inl he => exact (show Nat.Prime p from Fact.out).ne_one he
    | inr he => omega
  have hn0 := hmod n hn hpn
  have hnh0 := hmod (n + h) hnh (by omega)
  have hm0 := hmod m hm hpm
  have hmk0 := hmod (m + k) hmk (by omega)
  have hnneg : Not ((n : ZMod p) = -(h : ZMod p)) := by
    intro he
    apply hnh0
    simp only [Nat.cast_add, he, neg_add_cancel]
  have hmneg : Not ((m : ZMod p) = -(k : ZMod p)) := by
    intro he
    apply hmk0
    simp only [Nat.cast_add, he, neg_add_cancel]
  have hsN := FiniteField.QuadraticPairTwistEuler.traceFreePairWeight_scalar
    (n : ZMod p) (h : ZMod p) hn0 hnneg
  have hsM := FiniteField.QuadraticPairTwistEuler.traceFreePairWeight_scalar
    (m : ZMod p) (k : ZMod p) hm0 hmneg
  have hden : Not ((p : Real) - 3 = 0) := by
    have hpR : (5 : Real) <= p := by exact_mod_cast hp5
    linarith only [hpR]
  have htrace (s d : Nat) : nativeTrace s d p =
      FiniteField.QuadraticPairTwistEuler.characterA (s : ZMod p) (d : ZMod p) +
        FiniteField.QuadraticPairTwistEuler.characterB (s : ZMod p) (d : ZMod p) := by
    have ha := congrArg Complex.re (integer_characterA d s p (by omega))
    have hb := congrArg Complex.re (integer_characterB d s p (by omega))
    simp only [Complex.ofReal_re] at ha hb
    unfold nativeTrace
    rw [<- ha, <- hb]
  rw [hsN, hsM, htrace n h, htrace m k]
  simp only [ZMod.card]
  field_simp [hden]
  ring

theorem native_weight_energy_eq_trace (n h m k Y X : Nat)
    (hn : Nat.Prime n) (hnh : Nat.Prime (n + h))
    (hm : Nat.Prime m) (hmk : Nat.Prime (m + k))
    (hY : 5 <= Y) (hXn : X <= n) (hXm : X <= m) :
    nativeWeightEnergy n h m k Y X = nativeTraceEnergy n h m k Y X := by
  classical
  unfold nativeWeightEnergy nativeTraceEnergy
  apply Finset.sum_congr rfl
  intro p hp
  have hdata := Finset.mem_filter.mp hp
  have hband := Finset.mem_Ico.mp hdata.1
  have : Fact (Nat.Prime p) := Fact.mk hdata.2
  have hs := native_weight_scaled_difference n h m k p hn hnh hm hmk
    (by omega) (by omega) (by omega)
  simp only [integerNativeWeight, dite_eq_left hdata.2]
  rw [<- hs]
  ring

theorem native_metric_defect_tendsto_zero (C : Real) :
    Tendsto (nativeMetricDefect C) atTop (nhds 0) := by
  have hK : Tendsto (fun Q : Nat => (preciseCore Q : Real)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp precise_core_tendsto_atTop
  have hi := tendsto_inv_atTop_zero.comp (Real.tendsto_log_atTop.comp hK)
  have he : Tendsto (fun Q : Nat =>
      2 * PrimeFactorUnimodality.mertensErrorConstant / Real.log (preciseCore Q : Real)) atTop (nhds 0) := by
    simpa only [Function.comp_apply, div_eq_mul_inv, mul_zero] using
      hi.const_mul (2 * PrimeFactorUnimodality.mertensErrorConstant)
  have hd := (he.const_mul 2).add ((relative_error_tendsto_zero C).const_mul 10)
  change Tendsto (fun Q : Nat =>
    2 * (2 * PrimeFactorUnimodality.mertensErrorConstant / Real.log (preciseCore Q : Real)) +
      10 * relativeError C Q) atTop (nhds 0)
  simpa only [mul_zero, zero_add] using hd

theorem exists_uniform_native_metric_lower :
    exists C : Real, And (0 < C)
      (forall H : Nat, 0 < H -> Filter.Eventually (fun Q : Nat =>
        forall n m h k : Nat,
          Nat.Prime n -> Nat.Prime (n + h) -> Nat.Prime m -> Nat.Prime (m + k) ->
          0 < h -> 0 < k -> h <= H -> k <= H ->
          Q < n -> Q < m -> n + h <= Q * Q -> m + k <= Q * Q ->
          Not (And (n = m) (h = k)) ->
          2 * Real.log 2 - nativeMetricDefect C Q <=
            nativeWeightEnergy n h m k (preciseCore Q + 1)
              (preciseCore Q * preciseCore Q + 1)) atTop) := by
  classical
  choose C hCpos hC using exists_native_trace_energy_lower
  refine Exists.intro C (And.intro hCpos ?_)
  intro H hH
  have hfit : Filter.Eventually (fun Q : Nat =>
      6 <= Q /\ 1 <= Real.log (Q : Real) /\
        1 <= Real.log (Real.log (Q : Real)) /\ preciseCore Q <= Q) atTop :=
    eventually_atTop.mpr eventually_precise_core_fits
  filter_upwards [precise_core_tendsto_atTop.eventually_ge_atTop (max H 4),
    eventually_precise_core_square_fits, hfit, eventually_ge_atTop H]
    with Q hK hband hfitQ hHQ
  intro n m h k hn hnh hm hmk hh hk hhH hkH hQn hQm hnQ hmQ hneq
  have hYX : preciseCore Q + 1 < preciseCore Q * preciseCore Q + 1 := by
    have hfour : 4 <= preciseCore Q := (le_max_right H 4).trans hK
    nlinarith only [hfour]
  have hlower := hC H (Q * Q) n m h k (preciseCore Q + 1)
    (preciseCore Q * preciseCore Q + 1) hn hnh hm hmk hh hk hhH hkH
    (by omega) (by omega) hYX (by omega) (by omega) hnQ hmQ hneq
  have hcost := signature_uniform_cost_le C hCpos.le H Q hH hHQ
    (by omega) hfitQ.2.1
  have hmass := reciprocal_square_band_lower (preciseCore Q) (by omega)
  rw [native_weight_energy_eq_trace n h m k _ _ hn hnh hm hmk
    (by omega) (by omega) (by omega)]
  unfold nativeMetricDefect
  linarith only [hlower, hcost, hmass]

theorem eventually_native_weight_metric_separation (H : Nat) (hH : 0 < H)
    (eta : Real) (heta : 0 < eta) :
    Filter.Eventually (fun Q : Nat =>
      forall n m h k : Nat,
        Nat.Prime n -> Nat.Prime (n + h) -> Nat.Prime m -> Nat.Prime (m + k) ->
        0 < h -> 0 < k -> h <= H -> k <= H ->
        Q < n -> Q < m -> n + h <= Q * Q -> m + k <= Q * Q ->
        Not (And (n = m) (h = k)) ->
        2 * Real.log 2 - eta <= nativeWeightEnergy n h m k (preciseCore Q + 1)
          (preciseCore Q * preciseCore Q + 1)) atTop := by
  choose C hCpos hC using exists_uniform_native_metric_lower
  filter_upwards [hC H hH,
    (native_metric_defect_tendsto_zero C).eventually (Iio_mem_nhds heta)]
    with Q hQ hd
  intro n m h k hn hnh hm hmk hh hk hhH hkH hQn hQm hnQ hmQ hneq
  have he := hQ n m h k hn hnh hm hmk hh hk hhH hkH hQn hQm hnQ hmQ hneq
  linarith only [he, hd]

theorem eventually_native_metric_pair_rigidity (H : Nat) (hH : 0 < H) :
    Filter.Eventually (fun Q : Nat =>
      forall n m h k : Nat,
        Nat.Prime n -> Nat.Prime (n + h) -> Nat.Prime m -> Nat.Prime (m + k) ->
        0 < h -> 0 < k -> h <= H -> k <= H ->
        Q < n -> Q < m -> n + h <= Q * Q -> m + k <= Q * Q ->
        nativeWeightEnergy n h m k (preciseCore Q + 1)
          (preciseCore Q * preciseCore Q + 1) < Real.log 2 ->
        And (n = m) (h = k)) atTop := by
  filter_upwards [eventually_native_weight_metric_separation H hH
    (Real.log 2) (Real.log_pos (by norm_num))] with Q hQ
  intro n m h k hn hnh hm hmk hh hk hhH hkH hQn hQm hnQ hmQ hdist
  by_contra hneq
  have he := hQ n m h k hn hnh hm hmk hh hk hhH hkH hQn hQm hnQ hmQ hneq
  linarith only [he, hdist]

theorem unbounded_least_gap_native_metric_frames (R : Nat) :
    exists Q i : Nat, And (R <= Q) (And (leastGapFrame Q i)
      (forall m k : Nat, Nat.Prime m -> Nat.Prime (m + k) ->
        0 < k -> k <= leastRecurringPrimeGap -> Q < m -> m + k <= Q * Q ->
        nativeWeightEnergy (Q + 1) leastRecurringPrimeGap m k (preciseCore Q + 1)
          (preciseCore Q * preciseCore Q + 1) < Real.log 2 ->
        And (m = Q + 1) (k = leastRecurringPrimeGap))) := by
  have hH : 0 < leastRecurringPrimeGap := by
    have hh := two_le_leastRecurringPrimeGap
    omega
  choose Q0 hQ0 using eventually_atTop.mp
    (eventually_native_metric_pair_rigidity leastRecurringPrimeGap hH)
  choose Q i hRQ hf using unbounded_least_gap_positive_windows (max R Q0)
  have hQge : Q0 <= Q := (le_max_right _ _).trans hRQ
  have hRge : R <= Q := (le_max_left _ _).trans hRQ
  refine Exists.intro Q (Exists.intro i (And.intro hRge (And.intro hf ?_)))
  intro m k hm hmk hk hkH hQm hmQ hdist
  have hn : Nat.Prime (Q + 1) := by
    rw [<- hf.2.2.2.2.2.1]
    exact PrimeFactorUnimodality.prime_primeAt i
  have hnh : Nat.Prime (Q + 1 + leastRecurringPrimeGap) := by
    rw [<- hf.2.2.2.2.2.2.1]
    exact PrimeFactorUnimodality.prime_primeAt (i + 1)
  have hnQ : Q + 1 + leastRecurringPrimeGap <= Q * Q := by
    have hHQ := hf.2.2.2.2.1
    have hQ6 := hf.1
    nlinarith only [hHQ, hQ6]
  have he := hQ0 Q hQge (Q + 1) m leastRecurringPrimeGap k hn hnh hm hmk
    hH hk (Nat.le_refl _) hkH (by omega) hQm hnQ hmQ hdist
  exact And.intro he.1.symm he.2.symm

end PrimeFactorOscillations.FiniteFieldIntegerSignature

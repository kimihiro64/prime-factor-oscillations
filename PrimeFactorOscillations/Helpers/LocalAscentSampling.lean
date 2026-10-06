/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.AscentSamplingGrowth
import PrimeFactorOscillations.Helpers.LocalizedAscentCriterion
import PrimeFactorOscillations.Helpers.PrimeDensitySteps

/-!
# Canonical local prime-pair sampling for the ascent-only criteria

The finite set contains actual consecutive pairs with both endpoints in
[X+1, X+1+ceil(2*X^(7/10))]. The quantitative source is the explicit
all-short-interval pair count at exponent 3/5. Both canonical RH criteria
consume that source without adding an axiom for the external theorem.
-/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace PrimeFactorOscillations
open Filter PrimeFactorUnimodality

def shortIntervalPairSet (H Y h : Nat) : Finset Nat := by
  classical
  exact (Finset.range (Y + 1)).filter (fun i =>
    Y - h <= primeAt i /\ primeAt (i + 1) <= Y /\ primeGap i <= H)

def QuantitativeShortIntervalPairs (H : Nat) : Prop :=
  exists c B : Real, 0 < c /\ 0 <= B /\ exists Y0 : Nat,
    forall Y h : Nat, Y0 <= Y -> (Y : Real) ^ (3 / 5 : Real) <= h -> h <= Y ->
      c * (h : Real) / (Real.log (Y : Real)) ^ B <= (shortIntervalPairSet H Y h).card

def localAscentWindowWidth (X : Nat) : Nat :=
  Nat.ceil (2 * (X : Real) ^ (7 / 10 : Real))

def localAscentPairSet (H X : Nat) : Finset Nat :=
  shortIntervalPairSet H (X + 1 + localAscentWindowWidth X) (localAscentWindowWidth X)

def localAscentPairNumber (H X : Nat) : Nat := (localAscentPairSet H X).card

def selectedLocalAscentPair (H X : Nat) : Fin (localAscentPairNumber H X) -> Nat :=
  (localAscentPairSet H X).orderEmbOfFin rfl

theorem eventually_localAscentWindow_bounds :
    Filter.Eventually (fun X : Nat =>
      3 <= X /\ 2 * (X : Real) ^ (7 / 10 : Real) <= (localAscentWindowWidth X : Real) /\
      (localAscentWindowWidth X : Real) <= (X : Real) ^ (3 / 4 : Real) /\
      (X + 1 + localAscentWindowWidth X : Nat) <= 2 * X /\
      ((X + 1 + localAscentWindowWidth X : Nat) : Real) ^ (3 / 5 : Real) <=
        (localAscentWindowWidth X : Real)) atTop := by
  have hCast : Tendsto (fun n : Nat => (n : Real)) atTop atTop := tendsto_natCast_atTop_atTop
  have hE := hCast.eventually ((tendsto_rpow_atTop
    (by norm_num : (0 : Real) < 1 / 20)).eventually_ge_atTop 4)
  have hQ := hCast.eventually ((tendsto_rpow_atTop
    (by norm_num : (0 : Real) < 1 / 4)).eventually_ge_atTop 2)
  filter_upwards [hE, hQ, eventually_ge_atTop (3 : Nat)] with X he hq hx
  have hx0 : 0 < (X : Real) := by exact_mod_cast (by omega : 0 < X)
  have hx1 : (1 : Real) <= X := by exact_mod_cast (by omega : 1 <= X)
  have hx2 : (2 : Real) <= X := by exact_mod_cast (by omega : 2 <= X)
  have hp : 1 <= (X : Real) ^ (7 / 10 : Real) := by
    simpa only [Real.rpow_zero] using Real.rpow_le_rpow_of_exponent_le hx1
      (by norm_num : (0 : Real) <= 7 / 10)
  have hUpper := (Nat.ceil_lt_add_one
    (show 0 <= 2 * (X : Real) ^ (7 / 10 : Real) by positivity)).le
  change (localAscentWindowWidth X : Real) <= 2 * (X : Real) ^ (7 / 10 : Real) + 1 at hUpper
  have hProduct : (X : Real) ^ (1 / 20 : Real) * (X : Real) ^ (7 / 10 : Real) =
      (X : Real) ^ (3 / 4 : Real) := by
    rw [<- Real.rpow_add hx0]
    norm_num
  have heMul := mul_le_mul_of_nonneg_right he
    (Real.rpow_nonneg hx0.le (7 / 10))
  rw [hProduct] at heMul
  have hWidth : (localAscentWindowWidth X : Real) <= (X : Real) ^ (3 / 4 : Real) := by linarith
  have hQuarter : (X : Real) ^ (1 / 4 : Real) * (X : Real) ^ (3 / 4 : Real) = X := by
    rw [<- Real.rpow_add hx0]
    norm_num
  have hqMul := mul_le_mul_of_nonneg_right hq (Real.rpow_nonneg hx0.le (3 / 4))
  rw [hQuarter] at hqMul
  have hYReal : ((X + 1 + localAscentWindowWidth X : Nat) : Real) <= 2 * X := by
    simp only [Nat.cast_add, Nat.cast_one]
    linarith
  have hY : X + 1 + localAscentWindowWidth X <= 2 * X := by exact_mod_cast hYReal
  have hLow : 2 * (X : Real) ^ (7 / 10 : Real) <= (localAscentWindowWidth X : Real) := Nat.le_ceil _
  refine And.intro hx (And.intro hLow (And.intro hWidth (And.intro hY ?_)))
  have hMon := Real.rpow_le_rpow (Nat.cast_nonneg (X + 1 + localAscentWindowWidth X))
    hYReal (by norm_num : (0 : Real) <= 3 / 5)
  rw [Real.mul_rpow (by norm_num : (0 : Real) <= 2) hx0.le] at hMon
  have hTwo : (2 : Real) ^ (3 / 5 : Real) <= 2 := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le
      (by norm_num : (1 : Real) <= 2) (by norm_num : (3 / 5 : Real) <= 1)
  have hP : (X : Real) ^ (3 / 5 : Real) <= (X : Real) ^ (7 / 10 : Real) :=
    Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
  exact (hMon.trans (mul_le_mul hTwo hP (by positivity) (by norm_num))).trans hLow

theorem localAscentSampling_of_quantitativeShortIntervalPairs
    (H : Nat) (hSource : QuantitativeShortIntervalPairs H) :
    LocalAscentSampling H (localAscentPairNumber H) (selectedLocalAscentPair H) := by
  choose c B hc hB Y0 hSourceBound using hSource
  let c1 : Real := c / (2 : Real) ^ B
  have hc1 : 0 < c1 := div_pos hc (Real.rpow_pos_of_pos (by norm_num) _)
  have hLower : Filter.Eventually (fun X : Nat =>
      c1 * (X : Real) ^ (7 / 10 : Real) / (Real.log (X : Real)) ^ B <=
        (localAscentPairNumber H X : Real)) atTop := by
    filter_upwards [eventually_localAscentWindow_bounds, eventually_ge_atTop Y0]
      with X hw hX0
    let h := localAscentWindowWidth X
    let Y := X + 1 + h
    have hY : Y0 <= Y := by dsimp [Y]; omega
    have hhY : h <= Y := by dsimp [Y]; omega
    have hCount := hSourceBound Y h hY hw.2.2.2.2 hhY
    have hx2 : (2 : Real) <= X := by exact_mod_cast (show 2 <= X by omega)
    have hx0 : 0 < (X : Real) := by linarith
    have hx1 : (1 : Real) < X := by linarith
    have hXY : (X : Real) <= Y := by exact_mod_cast (show X <= Y by dsimp [Y]; omega)
    have hy0 : 0 < (Y : Real) := hx0.trans_le hXY
    have hLogX : 0 < Real.log (X : Real) := Real.log_pos hx1
    have hLogY : 0 < Real.log (Y : Real) := Real.log_pos (hx1.trans_le hXY)
    have hYHigh : (Y : Real) <= 2 * X := by exact_mod_cast hw.2.2.2.1
    have hLogs := Real.log_le_log hy0 hYHigh
    rw [Real.log_mul (by norm_num : Not ((2 : Real) = 0)) hx0.ne'] at hLogs
    have hTwoLog : Real.log 2 <= Real.log (X : Real) := Real.log_le_log (by norm_num) hx2
    have hLogPower : (Real.log (Y : Real)) ^ B <=
        (2 : Real) ^ B * (Real.log (X : Real)) ^ B := by
      have ht := Real.rpow_le_rpow hLogY.le (show Real.log (Y : Real) <= 2 * Real.log (X : Real) by linarith) hB
      rwa [Real.mul_rpow (by norm_num : (0 : Real) <= 2) hLogX.le] at ht
    have hOne : (X : Real) ^ (7 / 10 : Real) <= h := by
      have hh := hw.2.1
      change 2 * (X : Real) ^ (7 / 10 : Real) <= (h : Real) at hh
      linarith [Real.rpow_nonneg hx0.le (7 / 10 : Real)]
    have hFirst := div_le_div_of_nonneg_left
      (show 0 <= c * (X : Real) ^ (7 / 10 : Real) by positivity)
      (Real.rpow_pos_of_pos hLogY _) hLogPower
    have hSecond := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hOne hc.le) (Real.rpow_nonneg hLogY.le B)
    have hEq : c1 * (X : Real) ^ (7 / 10 : Real) / (Real.log (X : Real)) ^ B =
        c * (X : Real) ^ (7 / 10 : Real) /
          ((2 : Real) ^ B * (Real.log (X : Real)) ^ B) := by dsimp [c1]; ring
    rw [hEq]
    exact (hFirst.trans hSecond).trans hCount
  refine And.intro (subpower_supply_of_power_log_lower (localAscentPairNumber H) c1 B hc1 hLower) ?_
  filter_upwards [eventually_localAscentWindow_bounds] with X hw
  constructor
  . exact (localAscentPairSet H X).orderEmbOfFin rfl |>.injective
  . intro i
    have hMem := (localAscentPairSet H X).orderEmbOfFin_mem rfl i
    have hi := (Finset.mem_filter.mp hMem).2
    change X + 1 + localAscentWindowWidth X - localAscentWindowWidth X <=
      primeAt (selectedLocalAscentPair H X i) /\
      primeAt (selectedLocalAscentPair H X i + 1) <= X + 1 + localAscentWindowWidth X /\
      primeGap (selectedLocalAscentPair H X i) <= H at hi
    have hLower : X + 1 <= primeAt (selectedLocalAscentPair H X i) := by omega
    have hGap := primeAt_gap_ge_two (selectedLocalAscentPair H X i) (by omega)
    have hNext := primeAt_strictMono (Nat.lt_succ_self (selectedLocalAscentPair H X i))
    have hPrefixLower : X <= primeAt (selectedLocalAscentPair H X i) - 1 := by omega
    have hPrefixUpper : primeAt (selectedLocalAscentPair H X i) - 1 <= X + localAscentWindowWidth X := by omega
    have hGapTwo : 2 <= primeGap (selectedLocalAscentPair H X i) := by
      unfold primeGap
      omega
    refine And.intro hGapTwo (And.intro hi.2.2 (And.intro (by exact_mod_cast hPrefixLower) ?_))
    have hUpperReal : ((primeAt (selectedLocalAscentPair H X i) - 1 : Nat) : Real) <=
        (X : Real) + localAscentWindowWidth X := by exact_mod_cast hPrefixUpper
    linarith [hw.2.2.1]

theorem quantitativeShortIntervalPairs_rh_iff_local_ascent
    (H : Nat) (hSource : QuantitativeShortIntervalPairs H) :
    RiemannHypothesis <->
      Filter.Eventually (fun X : Nat =>
        localAscentCount H (localAscentPairNumber H) (selectedLocalAscentPair H) X <=
          localReferenceCount H (localAscentPairNumber H) (selectedLocalAscentPair H) X) atTop :=
  riemannHypothesis_iff_eventually_localAscentCount_le_reference H _ _
    (localAscentSampling_of_quantitativeShortIntervalPairs H hSource)

theorem quantitativeShortIntervalPairs_rh_iff_local_ascent_power
    (H : Nat) (hSource : QuantitativeShortIntervalPairs H) :
    RiemannHypothesis <->
      exists C : Real, 0 < C /\ Filter.Eventually (fun X : Nat =>
        (localAscentCount H (localAscentPairNumber H) (selectedLocalAscentPair H) X : Real) -
          (localReferenceCount H (localAscentPairNumber H) (selectedLocalAscentPair H) X : Real) <=
            C * (X : Real) ^ (7 / 10 : Real)) atTop :=
  riemannHypothesis_iff_eventually_localAscentCount_power_upper H _ _
    (localAscentSampling_of_quantitativeShortIntervalPairs H hSource)

end PrimeFactorOscillations



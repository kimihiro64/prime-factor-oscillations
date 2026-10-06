/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import PrimeFactorOscillations.Definitions.GapFrequency
import PrimeFactorOscillations.Helpers.ThetaErrorIntegrability

/-!
# Exact-gap coverage from a global counting error

The full logarithmic-integral main term and both endpoint errors are retained.
A little-o error at sqrt(x)/log(x)^4 forces a consecutive pair of the specified
exact gap in every sufficiently late real interval of length sqrt(x)/log(x)^2.
The global error estimate is an explicit hypothesis, not a proved gap theorem.
-/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace PrimeFactorOscillations
open Filter Asymptotics MeasureTheory Set

def logarithmicIntegralTwo (x : Real) : Real :=
  intervalIntegral (fun t : Real => 1 / (Real.log t) ^ (2 : Nat)) 2 x volume

def gapCoverageLength (x : Real) : Real :=
  Real.sqrt x / (Real.log x) ^ (2 : Nat)

def gapCoverageErrorScale (x : Real) : Real :=
  Real.sqrt x / (Real.log x) ^ (4 : Nat)

private theorem liTwo_integrable {x y : Real} (hx : 1 < x) (hxy : x <= y) :
    IntervalIntegrable (fun t : Real => 1 / (Real.log t) ^ (2 : Nat)) volume x y := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le hxy]
  apply continuousOn_const.div
  . exact (Real.continuousOn_log.mono (by
      intro t ht
      exact ne_of_gt (lt_trans zero_lt_one (hx.trans_le ht.1)))).pow 2
  . intro t ht
    exact pow_ne_zero 2 (Real.log_pos (hx.trans_le ht.1)).ne'

theorem logarithmicIntegralTwo_increment_lower (x y : Real)
    (hx : 2 <= x) (hxy : x <= y) (hy : y <= 2 * x) :
    (y - x) / (4 * (Real.log x) ^ (2 : Nat)) <=
      logarithmicIntegralTwo y - logarithmicIntegralTwo x := by
  have hxi : IntervalIntegrable (fun t : Real => 1 / (Real.log t) ^ (2 : Nat))
      volume 2 x := liTwo_integrable (by norm_num) hx
  have hxyi := liTwo_integrable (by linarith : (1 : Real) < x) hxy
  have hid : logarithmicIntegralTwo y - logarithmicIntegralTwo x =
      intervalIntegral (fun t : Real => 1 / (Real.log t) ^ (2 : Nat)) x y volume := by
    dsimp only [logarithmicIntegralTwo]
    linarith [intervalIntegral.integral_add_adjacent_intervals hxi hxyi]
  rw [hid]
  have hl : 0 < Real.log x := Real.log_pos (by linarith)
  have h : intervalIntegral (fun _ : Real => 1 / (4 * (Real.log x) ^ (2 : Nat))) x y volume <=
      intervalIntegral (fun t : Real => 1 / (Real.log t) ^ (2 : Nat)) x y volume := by
    apply intervalIntegral.integral_mono_on hxy intervalIntegrable_const hxyi
    intro t ht
    have ht0 : 0 < t := by linarith [ht.1]
    have hlt : 0 < Real.log t := Real.log_pos (by linarith [ht.1])
    have hLogs := Real.log_le_log ht0 (ht.2.trans hy)
    rw [Real.log_mul (by norm_num : Not ((2 : Real) = 0))
      (by linarith : Not (x = 0))] at hLogs
    have hLogTwo := Real.log_le_log (by norm_num : (0 : Real) < 2) hx
    apply one_div_le_one_div_of_le (sq_pos_of_pos hlt)
    nlinarith
  simpa only [intervalIntegral.integral_const, smul_eq_mul, one_div, div_eq_mul_inv, one_mul] using h

theorem eventually_gapCoverageLength_bounds :
    Filter.Eventually (fun x : Real => 0 < gapCoverageLength x /\ gapCoverageLength x <= x)
      atTop := by
  filter_upwards [eventually_ge_atTop (3 : Real)] with x hx
  have hl : 1 < Real.log x :=
    (Real.lt_log_iff_exp_lt (by linarith : 0 < x)).mpr (Real.exp_one_lt_three.trans_le hx)
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.mpr (by linarith)
  have hsx : Real.sqrt x <= x := by
    nlinarith [Real.sq_sqrt (by linarith : 0 <= x)]
  refine And.intro (div_pos hs (sq_pos_of_pos (by linarith))) ?_
  dsimp [gapCoverageLength]
  exact (div_le_self hs.le (by nlinarith : 1 <= (Real.log x) ^ (2 : Nat))).trans hsx

theorem gapCoverageErrorScale_endpoint_bound (x y : Real)
    (hx : 2 <= x) (hxy : x <= y) (hy : y <= 2 * x) :
    gapCoverageErrorScale y <= 2 * gapCoverageErrorScale x := by
  have hx0 : 0 < x := by linarith
  have hy0 : 0 < y := hx0.trans_le hxy
  have hlx : 0 < Real.log x := Real.log_pos (by linarith)
  have hly := Real.log_le_log hx0 hxy
  have hsqrt : Real.sqrt y <= 2 * Real.sqrt x := by
    nlinarith [Real.sq_sqrt hx0.le, Real.sq_sqrt hy0.le,
      Real.sqrt_nonneg x, Real.sqrt_nonneg y]
  have hpow : (Real.log x) ^ (4 : Nat) <= (Real.log y) ^ (4 : Nat) := by
    have hsq : (Real.log x) ^ (2 : Nat) <= (Real.log y) ^ (2 : Nat) := by nlinarith
    nlinarith [sq_nonneg ((Real.log x) ^ (2 : Nat) - (Real.log y) ^ (2 : Nat))]
  dsimp only [gapCoverageErrorScale]
  calc
    _ <= (2 * Real.sqrt x) / (Real.log y) ^ (4 : Nat) :=
      div_le_div_of_nonneg_right hsqrt (by positivity)
    _ <= (2 * Real.sqrt x) / (Real.log x) ^ (4 : Nat) :=
      div_le_div_of_nonneg_left (by positivity) (pow_pos hlx 4) hpow
    _ = _ := by ring

theorem eventually_count_increases_of_liTwo_error (G : Real -> Real) (c : Real)
    (hc : 0 < c)
    (hError : IsLittleO atTop (fun x => G x - c * logarithmicIntegralTwo x)
      gapCoverageErrorScale) :
    Filter.Eventually (fun x : Real => G x < G (x + gapCoverageLength x)) atTop := by
  have he := hError.bound (show 0 < c / 32 by positivity)
  choose x0 hx0 using he.exists_forall_of_atTop
  filter_upwards [eventually_ge_atTop (max x0 3), eventually_gapCoverageLength_bounds]
    with x hx hlen
  let y := x + gapCoverageLength x
  have hxy : x <= y := by dsimp [y]; linarith [hlen.1]
  have hy : y <= 2 * x := by dsimp [y]; linarith [hlen.2]
  have hx3 : 3 <= x := (le_max_right _ _).trans hx
  have hScale : 0 < gapCoverageErrorScale x := by
    dsimp [gapCoverageErrorScale]
    exact div_pos (Real.sqrt_pos.mpr (by linarith))
      (pow_pos (Real.log_pos (by linarith)) 4)
  have hBounds := And.intro (hx0 x ((le_max_left _ _).trans hx))
    (hx0 y (((le_max_left _ _).trans hx).trans hxy))
  simp only [Real.norm_eq_abs] at hBounds
  have hyScale : 0 <= gapCoverageErrorScale y := by
    dsimp [gapCoverageErrorScale]
    positivity
  rw [abs_of_pos hScale] at hBounds
  rw [abs_of_nonneg hyScale] at hBounds
  have hys := gapCoverageErrorScale_endpoint_bound x y (by linarith) hxy hy
  have hmain := logarithmicIntegralTwo_increment_lower x y (by linarith) hxy hy
  have hid : (y - x) / (4 * (Real.log x) ^ (2 : Nat)) =
      gapCoverageErrorScale x / 4 := by
    dsimp [y, gapCoverageLength, gapCoverageErrorScale]
    ring
  rw [hid] at hmain
  have hb1 := (abs_le.mp hBounds.1).2
  have hb2 := (abs_le.mp hBounds.2).1
  nlinarith

/-- Actual consecutive pairs of exactly the fixed width, with lower prime at
most the real endpoint. The finite index range imposes no extra restriction. -/
def exactPrimeGapSet (h : Nat) (x : Real) : Finset Nat := by
  classical
  exact (Finset.range (Nat.floor x + 1)).filter (fun i =>
    (PrimeFactorUnimodality.primeAt i : Real) <= x /\
      PrimeFactorUnimodality.primeGap i = h)

def exactPrimeGapCount (h : Nat) (x : Real) : Real :=
  (exactPrimeGapSet h x).card

theorem mem_exactPrimeGapSet_iff (h i : Nat) (x : Real) (hx : 0 <= x) :
    Membership.mem (exactPrimeGapSet h x) i <->
      (PrimeFactorUnimodality.primeAt i : Real) <= x /\
        PrimeFactorUnimodality.primeGap i = h := by
  classical
  constructor
  . intro hi
    exact (Finset.mem_filter.mp hi).2
  . intro hi
    have hp : PrimeFactorUnimodality.primeAt i <= Nat.floor x :=
      (Nat.le_floor_iff hx).mpr hi.1
    have hbase := Nat.add_two_le_nth_prime i
    change i + 2 <= PrimeFactorUnimodality.primeAt i at hbase
    exact Finset.mem_filter.mpr (And.intro (Finset.mem_range.mpr (by omega)) hi)

/-- An error smaller than sqrt(x)/log(x)^4 forces an actual pair of the
specified exact gap in every sufficiently late interval of length
sqrt(x)/log(x)^2. This is conditional on the stated global error estimate. -/
theorem eventually_exact_gap_coverage_of_liTwo_error (h : Nat) (c : Real)
    (hc : 0 < c)
    (hError : IsLittleO atTop
      (fun x => exactPrimeGapCount h x - c * logarithmicIntegralTwo x)
      gapCoverageErrorScale) :
    Filter.Eventually (fun x : Real => exists i : Nat,
      x < (PrimeFactorUnimodality.primeAt i : Real) /\
      (PrimeFactorUnimodality.primeAt i : Real) <= x + gapCoverageLength x /\
      PrimeFactorUnimodality.primeGap i = h) atTop := by
  have hInc := eventually_count_increases_of_liTwo_error (exactPrimeGapCount h) c hc hError
  filter_upwards [hInc, eventually_ge_atTop (3 : Real), eventually_gapCoverageLength_bounds]
    with x hIncX hx hlen
  by_contra hnone
  have hsubset : exactPrimeGapSet h (x + gapCoverageLength x) <= exactPrimeGapSet h x := by
    intro i hi
    have hxy0 : 0 <= x + gapCoverageLength x := by linarith [hlen.1]
    have hmem := (mem_exactPrimeGapSet_iff h i _ hxy0).mp hi
    apply (mem_exactPrimeGapSet_iff h i x (by linarith)).mpr
    refine And.intro ?_ hmem.2
    by_contra hnot
    exact hnone (Exists.intro i (And.intro (lt_of_not_ge hnot) (And.intro hmem.1 hmem.2)))
  have hcard := Finset.card_le_card hsubset
  have hreal : exactPrimeGapCount h (x + gapCoverageLength x) <= exactPrimeGapCount h x := by
    dsimp only [exactPrimeGapCount]
    exact_mod_cast hcard
  exact not_lt_of_ge hreal hIncX


end PrimeFactorOscillations

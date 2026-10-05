/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.NicolasCanonicalSign
import PrimeFactorOscillations.Helpers.PrimeProfileLinearization

/-!
# Actual theta-centered density-ratio linearization

The bound is uniform in every sufficiently large integer rank below a fixed
multiple of the theta clock. It retains the exact Nicolas logarithm and both
positive denominators; no RH or prime-gap assumption is used.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations

open Filter Robin1984

theorem exists_eventually_densityRatio_thetaClock_linearization
    (b : Real) (hb : 0 < b) :
    exists r0 : Nat, exists K : Real, 0 < r0 /\ 0 <= K /\
      Filter.Eventually (fun N : Nat =>
        let L := Real.eulerMascheroniConstant +
          Real.log (Real.log (Chebyshev.theta (N : Real)))
        let F := nicolasLogMertensOscillation (N : Real)
        1 < Chebyshev.theta (N : Real) /\ 2 <= L /\
        forall r : Nat, r0 <= r -> (r : Real) / L <= b ->
          0 < (PrimeFactorUnimodality.weightEsymm
            (PrimeFactorUnimodality.primesBelow (N + 1)) r : Real) /\
          0 < Nat.factorialConvolution primeProfileRealCoefficient r L /\
          abs ((PrimeFactorUnimodality.densityRatio
              (PrimeFactorUnimodality.primesBelow (N + 1)) r : Real) -
            Nat.factorialConvolution primeProfileRealCoefficient (r - 1) L /
              Nat.factorialConvolution primeProfileRealCoefficient r L -
            ((r : Real) / L ^ 2) * F) <=
              K * (abs F / L ^ 2 + 1 / ((r : Real) * (N : Real)))) atTop := by
  choose r0 N0 K hr0 hN0 hK hBound using
    exists_primePrefixProfile_ratio_linearization b hb
  have hNear : Tendsto (fun N : Nat =>
      abs ((primeProfilePrefixSet N).sum
        (fun p => Real.log (1 + primeProfileWeight (p : Nat))) -
        (Real.eulerMascheroniConstant +
          Real.log (Real.log (Chebyshev.theta (N : Real)))))) atTop (nhds 0) := by
    simpa only [abs_zero] using tendsto_primePrefixProfile_logSum_sub_thetaClock.abs
  refine Exists.intro r0 (Exists.intro K (And.intro hr0 (And.intro hK ?_)))
  filter_upwards [eventually_ge_atTop N0,
    tendsto_primeProfile_theta_atTop.eventually_gt_atTop 1,
    tendsto_primeProfile_thetaClock_atTop.eventually_ge_atTop 2,
    hNear.eventually_lt_const (by norm_num : (0 : Real) < 1)] with N hN hTheta hL hAbs
  refine And.intro hTheta (And.intro hL ?_)
  intro r hr hRange
  have h := hBound r hr N hN
    ((primeProfilePrefixSet N).sum
      (fun p => Real.log (1 + primeProfileWeight (p : Nat))))
    (Real.eulerMascheroniConstant +
      Real.log (Real.log (Chebyshev.theta (N : Real)))) hL hAbs.le hRange
  rw [<- densityRatio_eq_primePrefixProfile_factorialConvolution,
    primePrefixProfile_factorialConvolution_eq_weightEsymm,
    <- nicolasLog_nat_eq_primeProfile_clock_difference N hTheta] at h
  exact h

theorem exists_eventually_densityRatio_real_thetaClock_linearization
    (b : Real) (hb : 0 < b) :
    exists r0 : Nat, exists K : Real, 0 < r0 /\ 0 <= K /\
      Filter.Eventually (fun x : Real =>
        let L := Real.eulerMascheroniConstant + Real.log (Real.log (Chebyshev.theta x))
        let F := nicolasLogMertensOscillation x
        1 < Chebyshev.theta x /\ 2 <= L /\
        forall r : Nat, r0 <= r -> (r : Real) / L <= b ->
          0 < (PrimeFactorUnimodality.weightEsymm
            (PrimeFactorUnimodality.primesBelow (Nat.floor x + 1)) r : Real) /\
          0 < Nat.factorialConvolution primeProfileRealCoefficient r L /\
          abs ((PrimeFactorUnimodality.densityRatio
              (PrimeFactorUnimodality.primesBelow (Nat.floor x + 1)) r : Real) -
            Nat.factorialConvolution primeProfileRealCoefficient (r - 1) L /
              Nat.factorialConvolution primeProfileRealCoefficient r L -
            ((r : Real) / L ^ 2) * F) <=
              K * (abs F / L ^ 2 + 1 / ((r : Real) * x))) atTop := by
  choose r0 K hr0 hK hEvent using exists_eventually_densityRatio_thetaClock_linearization b hb
  choose N0 hN0 using eventually_atTop.mp hEvent
  refine Exists.intro r0 (Exists.intro (2 * K) (And.intro hr0 (And.intro (by positivity) ?_)))
  filter_upwards [eventually_ge_atTop (max (2 : Real) (N0 : Real))] with x hx
  have hxTwo : 2 <= x := (le_max_left _ _).trans hx
  have hxN0 : (N0 : Real) <= x := (le_max_right _ _).trans hx
  have hxPos : 0 < x := by linarith
  have hn0 : N0 <= Nat.floor x := Nat.le_floor hxN0
  have hnTwo : 2 <= Nat.floor x := Nat.le_floor hxTwo
  have hnTwoReal : (2 : Real) <= (Nat.floor x : Real) := by exact_mod_cast hnTwo
  have hnPos : 0 < (Nat.floor x : Real) := by linarith
  have hFloor : x / 2 <= (Nat.floor x : Real) := by
    have hUpper := Nat.lt_floor_add_one x
    linarith
  have h := hN0 (Nat.floor x) hn0
  dsimp only at h
  rw [<- Chebyshev.theta_eq_theta_coe_floor x,
    nicolasLogMertensOscillation_natFloor] at h
  refine And.intro h.1 (And.intro h.2.1 ?_)
  intro r hr hRange
  have hRank := h.2.2 r hr hRange
  have hrReal : (0 : Real) < r := by exact_mod_cast hr0.trans_le hr
  have hInverse : (1 : Real) / ((r : Real) * (Nat.floor x : Real)) <=
      2 / ((r : Real) * x) := by
    calc
      (1 : Real) / ((r : Real) * (Nat.floor x : Real)) <=
          1 / ((r : Real) * (x / 2)) := by gcongr
      _ = 2 / ((r : Real) * x) := by field_simp [hrReal.ne', hxPos.ne']
  let L := Real.eulerMascheroniConstant + Real.log (Real.log (Chebyshev.theta x))
  let F := nicolasLogMertensOscillation x
  let E := abs ((PrimeFactorUnimodality.densityRatio
    (PrimeFactorUnimodality.primesBelow (Nat.floor x + 1)) r : Real) -
      Nat.factorialConvolution primeProfileRealCoefficient (r - 1) L /
        Nat.factorialConvolution primeProfileRealCoefficient r L -
      ((r : Real) / L ^ 2) * F)
  have hError : E <= K * (abs F / L ^ 2 +
      1 / ((r : Real) * (Nat.floor x : Real))) := hRank.2.2
  have hNonneg : (0 : Real) <= abs F / L ^ 2 := by positivity
  refine And.intro hRank.1 (And.intro hRank.2.1 ?_)
  change E <= (2 * K) * (abs F / L ^ 2 + 1 / ((r : Real) * x))
  calc
    E <= K * (abs F / L ^ 2 + 1 / ((r : Real) * (Nat.floor x : Real))) := hError
    _ <= K * (abs F / L ^ 2 + 2 / ((r : Real) * x)) := by gcongr
    _ = (2 * K) * (abs F / L ^ 2 + 1 / ((r : Real) * x)) -
        K * (abs F / L ^ 2) := by ring
    _ <= (2 * K) * (abs F / L ^ 2 + 1 / ((r : Real) * x)) :=
      sub_le_self _ (mul_nonneg hK hNonneg)

end PrimeFactorOscillations

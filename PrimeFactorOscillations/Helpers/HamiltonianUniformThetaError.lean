/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianCountPowerDecay
import PrimeFactorOscillations.Helpers.ThetaPolylogDecay

/-! # Uniform theta error at all physical row endpoints

The existing strong theta theorem is made uniform for every endpoint
0<=x<=2n. Small endpoints are controlled by the explicit Chebyshev bound;
large endpoints use log(x)>=log(n)/2. Both ranges share one threshold.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations.LPF

theorem hamiltonian_uniform_theta_error (m : Nat) :
    exists D : Real, And (0 < D)
      (exists N0 : Nat, And (256 <= N0)
        (forall n : Nat, N0 <= n -> forall x : Real, 0 <= x -> x <= 2 * (n : Real) ->
          abs (Chebyshev.theta x - x) <=
            D * (n : Real) / Real.log (n : Real) ^ m)) := by
  choose C hAsymp using (Asymptotics.isBigO_iff.mp (thetaError_isBigO_div_log_pow m))
  choose X hX using Filter.eventually_atTop.mp hAsymp
  let C' := abs C + 1
  let K : Real := Real.log 4 + 1
  let D := K + C' * (2 : Real) ^ (m + 1)
  let Y := max 2 X
  have hC : 0 < C' := by dsimp [C']; positivity
  have hCC : C <= C' := by
    have h := le_abs_self C
    dsimp [C']
    linarith only [h]
  have hK : 0 < K := by
    have h := Real.log_nonneg (by norm_num : (1 : Real) <= 4)
    dsimp [K]
    positivity
  have hD : 0 < D := by dsimp [D]; positivity
  have hY : (2 : Real) <= Y := le_max_left _ _
  have hYX : X <= Y := le_max_right _ _
  choose B hB hDom using hamiltonian_log_power_dominated_uniform
    1 (by norm_num) m (1 / 2) (by norm_num)
  let N0 := max B (Nat.ceil (Y ^ 2))
  refine Exists.intro D (And.intro hD (Exists.intro N0
    (And.intro (hB.trans (le_max_left _ _)) ?_)))
  intro n hn x hx0 hxTop
  have hnB : B <= n := (le_max_left _ _).trans hn
  have hnCeil : Nat.ceil (Y ^ 2) <= n := (le_max_right _ _).trans hn
  have hn256 : 256 <= n := hB.trans hnB
  have hnR : (256 : Real) <= (n : Real) := by exact_mod_cast hn256
  have hn0 : 0 < (n : Real) := by linarith only [hnR]
  have hn1 : (1 : Real) < (n : Real) := by linarith only [hnR]
  have hLogN : 0 < Real.log (n : Real) := Real.log_pos hn1
  have hDen : 0 < Real.log (n : Real) ^ m := pow_pos hLogN m
  let s := Real.sqrt (n : Real)
  have hs0 : 0 <= s := Real.sqrt_nonneg _
  have hsSquare : s ^ 2 = (n : Real) := Real.sq_sqrt hn0.le
  have hY2 : Y ^ 2 <= (n : Real) :=
    (Nat.le_ceil _).trans (by exact_mod_cast hnCeil)
  have hYS : Y <= s := by nlinarith only [hY2, hsSquare, hs0, hY]
  have hsPos : 0 < s := by linarith only [hYS, hY]
  have hLarge (hx : s <= x) : abs (Chebyshev.theta x - x) <=
      (C' * (2 : Real) ^ (m + 1)) * (n : Real) / Real.log (n : Real) ^ m := by
    have hxX : X <= x := hYX.trans (hYS.trans hx)
    have hx2 : (2 : Real) <= x := hY.trans (hYS.trans hx)
    have hxPos : 0 < x := by linarith only [hx2]
    have hLogX : 0 < Real.log x := Real.log_pos (by linarith only [hx2])
    have hBase := (hX x hxX).trans
      (mul_le_mul_of_nonneg_right hCC (norm_nonneg (x / Real.log x ^ m)))
    have hError : abs (Chebyshev.theta x - x) <= C' * (x / Real.log x ^ m) := by
      simpa only [Real.norm_eq_abs,
        abs_of_nonneg (div_nonneg hx0 (pow_nonneg hLogX.le m))] using hBase
    have hLogS : Real.log s = Real.log (n : Real) / 2 := by
      dsimp [s]
      rw [Real.sqrt_eq_rpow, Real.log_rpow hn0]
      ring
    have hLogHalf : Real.log (n : Real) / 2 <= Real.log x := by
      rw [<- hLogS]
      exact Real.log_le_log hsPos hx
    have hPower := wick_nonnegative_power_le _ _
      (show 0 <= Real.log (n : Real) / 2 by positivity) hLogHalf m
    calc
      _ <= C' * (x / Real.log x ^ m) := hError
      _ <= C' * ((2 * (n : Real)) / (Real.log (n : Real) / 2) ^ m) := by
        gcongr
      _ = _ := by rw [div_pow, pow_succ]; field_simp <;> ring
  have hSmall (hx : x <= s) : abs (Chebyshev.theta x - x) <=
      K * (n : Real) / Real.log (n : Real) ^ m := by
    have hLinear : abs (Chebyshev.theta x - x) <= K * x := by
      calc
        _ <= abs (Chebyshev.theta x) + abs x := abs_sub _ _
        _ = Chebyshev.theta x + x := by
          rw [abs_of_nonneg (Chebyshev.theta_nonneg x), abs_of_nonneg hx0]
        _ <= Real.log 4 * x + x := add_le_add (Chebyshev.theta_le_log4_mul_x hx0) (le_refl _)
        _ = _ := by dsimp [K]; ring
    have hLogDouble : Real.log (n : Real) <= Real.log (2 * (n : Real)) :=
      Real.log_le_log hn0 (by linarith only [hnR])
    have hLogPower := wick_nonnegative_power_le _ _ hLogN.le hLogDouble m
    have hDomN := hDom n hnB
    simp only [one_mul] at hDomN
    rw [<- Real.sqrt_eq_rpow] at hDomN
    have hPowerS : Real.log (n : Real) ^ m <= s := hLogPower.trans hDomN
    have hCross := mul_le_mul_of_nonneg_left hPowerS hs0
    have hSBound : s <= (n : Real) / Real.log (n : Real) ^ m := by
      calc
        _ = (s * Real.log (n : Real) ^ m) / Real.log (n : Real) ^ m := by field_simp
        _ <= (n : Real) / Real.log (n : Real) ^ m :=
          div_le_div_of_nonneg_right (by nlinarith only [hCross, hsSquare]) hDen.le
    calc
      _ <= K * x := hLinear
      _ <= K * s := mul_le_mul_of_nonneg_left hx hK.le
      _ <= K * ((n : Real) / Real.log (n : Real) ^ m) :=
        mul_le_mul_of_nonneg_left hSBound hK.le
      _ = _ := by ring
  have hDLower1 : K <= D := by
    have h : 0 <= C' * (2 : Real) ^ (m + 1) := by positivity
    dsimp [D]
    linarith only [h]
  have hDLower2 : C' * (2 : Real) ^ (m + 1) <= D := by dsimp [D]; linarith only [hK]
  by_cases hxS : x <= s
  . exact (hSmall hxS).trans (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hDLower1 (Nat.cast_nonneg n)) hDen.le)
  . exact (hLarge (le_of_lt (lt_of_not_ge hxS))).trans
      (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right hDLower2 (Nat.cast_nonneg n)) hDen.le)

end PrimeFactorOscillations.LPF

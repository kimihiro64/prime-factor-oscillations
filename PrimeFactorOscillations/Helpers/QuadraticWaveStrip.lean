/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import PrimeFactorOscillations.Helpers.NicolasStripAsymptotic
import PrimeFactorOscillations.Helpers.ProbabilityZeroRecovery
import PrimeFactorOscillations.Helpers.QRHSevenEighths

/-!
# Unconditional lower bounds for the probability wave from QRH

The full signed coefficient comparison transfers a zeta zero-free strip
Re(s) > b into Z(N) >= -C N^(b-1/2), for each fixed admissible law and
positive moving-rank parameter. The installed QRH theorem gives b=7/8
without an epsilon loss. At quartic cutoffs the exponent is exactly 3/2.
All constants and eventual cutoffs may depend on the fixed law and rank.
No new zero-free region is proved here.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations.QuadraticPrimeLaw

open Filter Robin1984
open scoped Topology

theorem eventually_normalizedFloorRatioWave_lower_of_strip
    (law : QuadraticPrimeLaw) (alpha : Real) (ha : 0 < alpha)
    (b : Real) (hb : (1 / 2 : Real) <= b) (hbOne : b < 1)
    (hZeroFree : forall s : Complex, b < s.re -> Not (s = 1) ->
      Not (riemannZeta s = 0)) :
    exists C : Real, 0 < C /\ Filter.Eventually (fun N : Nat =>
      -C * (N : Real) ^ (b - 1 / 2) <=
        law.normalizedFloorRatioWave alpha N) atTop := by
  choose K E hK hE hApprox using law.exists_eventually_normalizedFloorRatioWave_error alpha ha
  let A : Real := (Real.eulerMascheroniConstant + 2 - Real.log (4 * Real.pi)) /
    (2 * Real.sqrt (b * (1 - b)))
  let D : Real := abs A + 1
  have hD : 0 < D := by dsimp [D]; positivity
  have ht : Tendsto (fun N : Nat => (N : Real)) atTop atTop := tendsto_natCast_atTop_atTop
  have hRank : Tendsto (fun N : Nat => (law.floorRank alpha N : Real)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (law.tendsto_floorRank_atTop alpha ha)
  have hDelta : Tendsto (fun N : Nat => K / (law.floorRank alpha N : Real))
      atTop (nhds 0) := tendsto_const_nhds.div_atTop hRank
  have hTail : Tendsto (fun N : Nat =>
      E * (Real.log (N : Real) / (N : Real) ^ (1 / 2 : Real))) atTop (nhds 0) := by
    simpa only [mul_zero, Function.comp_def] using
      (((isLittleO_log_rpow_atTop (by norm_num : (0 : Real) < 1 / 2)).tendsto_div_nhds_zero).comp
        ht).const_mul E
  have hbPos : 0 < b := lt_of_lt_of_le (by norm_num) hb
  have hStrip := ht.eventually
    (eventually_nicolasLog_scaled_strip_lt hbPos hbOne hZeroFree (by norm_num : (0 : Real) < 1))
  refine Exists.intro (3 + 2 * D) (And.intro (by positivity) ?_)
  filter_upwards [hApprox, hStrip, ht.eventually_ge_atTop (1 : Real),
    hDelta.eventually (eventually_le_nhds (by norm_num : (0 : Real) < 1)),
    hTail.eventually (eventually_le_nhds (by norm_num : (0 : Real) < 1))] with
    N hApproxN hStripN hN hDeltaN hTailN
  let T : Real := (N : Real) ^ (1 / 2 : Real) * Real.log (N : Real) *
    nicolasLogMertensOscillation (N : Real)
  let S : Real := ((N : Real) ^ (1 - b) * Real.log (N : Real)) *
    nicolasLogMertensOscillation (N : Real)
  let Y : Real := (N : Real) ^ (b - 1 / 2)
  have hY : 1 <= Y := Real.one_le_rpow hN (sub_nonneg.mpr hb)
  have hY0 : 0 <= Y := zero_le_one.trans hY
  have hS : S <= D := by
    change S < A + 1 at hStripN
    dsimp [D]
    linarith only [hStripN, le_abs_self A]
  have hIdentity : Y * S = T := by
    dsimp [Y, S, T]
    calc
      _ = ((N : Real) ^ (b - 1 / 2) * (N : Real) ^ (1 - b)) *
          Real.log (N : Real) * nicolasLogMertensOscillation (N : Real) := by ring
      _ = _ := by
        rw [<- Real.rpow_add (zero_lt_one.trans_le hN)]
        rw [show b - 1 / 2 + (1 - b) = (1 / 2 : Real) by ring]
  have hT : T <= D * Y := by
    have h := mul_le_mul_of_nonneg_left hS hY0
    rw [hIdentity] at h
    simpa only [mul_comm Y D] using h
  have hError := hApproxN.2.2.2
  change abs (law.normalizedFloorRatioWave alpha N + 2 + T) <=
    K / (law.floorRank alpha N : Real) * abs T +
      E * (Real.log (N : Real) / (N : Real) ^ (1 / 2 : Real)) at hError
  have hLower := (abs_le.mp hError).1
  have hDY : 0 <= D * Y := mul_nonneg hD.le hY0
  change -(3 + 2 * D) * Y <= law.normalizedFloorRatioWave alpha N
  by_cases hSign : 0 <= T
  . rw [abs_of_nonneg hSign] at hLower
    have hMul := mul_le_mul_of_nonneg_right hDeltaN hSign
    nlinarith only [hLower, hMul, hTailN, hT, hY]
  . have hNonpos : T <= 0 := le_of_not_ge hSign
    rw [abs_of_nonpos hNonpos] at hLower
    have hMul := mul_le_mul_of_nonneg_right hDeltaN (neg_nonneg.mpr hNonpos)
    nlinarith only [hLower, hMul, hTailN, hDY, hY]

theorem eventually_normalizedFloorRatioWave_seven_eighths_lower
    (law : QuadraticPrimeLaw) (alpha : Real) (ha : 0 < alpha) :
    exists C : Real, 0 < C /\ Filter.Eventually (fun N : Nat =>
      -C * (N : Real) ^ (3 / 8 : Real) <=
        law.normalizedFloorRatioWave alpha N) atTop := by
  have h := law.eventually_normalizedFloorRatioWave_lower_of_strip alpha ha
    (7 / 8) (by norm_num) (by norm_num) (fun s hs _ => QRH.zeta_ne_zero s hs)
  norm_num only [show (7 / 8 : Real) - 1 / 2 = 3 / 8 by norm_num] at h
  exact h

theorem eventually_normalizedFloorRatioWave_fourthPower_three_halves_lower
    (law : QuadraticPrimeLaw) (alpha : Real) (ha : 0 < alpha) :
    exists C : Real, 0 < C /\ Filter.Eventually (fun j : Nat =>
      -C * (j : Real) ^ (3 / 2 : Real) <=
        law.normalizedFloorRatioWave alpha (j ^ 4)) atTop := by
  choose C hC hBound using law.eventually_normalizedFloorRatioWave_seven_eighths_lower alpha ha
  refine Exists.intro C (And.intro hC ?_)
  filter_upwards [Nat.strictMono_fourthPower.tendsto_atTop.eventually hBound] with j hj
  have hPower : ((j ^ 4 : Nat) : Real) ^ (3 / 8 : Real) =
      (j : Real) ^ (3 / 2 : Real) := by
    rw [Nat.cast_pow, <- Real.rpow_natCast, <- Real.rpow_mul (Nat.cast_nonneg j)]
    norm_num
  rwa [hPower] at hj

theorem eventually_probabilityWave_fourthPower_three_halves_lower
    (law : QuadraticPrimeLaw) (eta : Nat -> Real)
    (hProb : forall p : Nat, Nat.Prime p -> eta p <= 1)
    (hWeight : forall p : Nat.Primes, law.weight p = eta (p : Nat) / (1 - eta (p : Nat)))
    (alpha : Real) (ha : 0 < alpha) :
    exists C : Real, 0 < C /\ Filter.Eventually (fun j : Nat =>
      -C * (j : Real) ^ (3 / 2 : Real) <=
        law.probabilityNormalizedFloorRatioWave eta alpha (j ^ 4)) atTop := by
  simpa only [law.probabilityNormalizedFloorRatioWave_eq_normalizedFloorRatioWave eta hProb hWeight]
    using law.eventually_normalizedFloorRatioWave_fourthPower_three_halves_lower alpha ha

end PrimeFactorOscillations.QuadraticPrimeLaw

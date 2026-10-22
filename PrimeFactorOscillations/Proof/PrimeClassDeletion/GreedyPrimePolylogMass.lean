/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.ThetaPolylogDecay
import PrimeFactorOscillations.Proof.PrimeClassDeletion.GreedyPrimeRealCutoffs

/-!
# Unconditional logarithmic mass control for the actual greedy deletion

Use the proved PNT estimates of orders zero and two on the full running
maximum. Splitting its prime argument at the square root retains the
initial range, every intermediate record, and the greedy overshoot.
This bound supplies the tail control needed for the missing Euler constant.
-/

set_option autoImplicit false
set_option Elab.async false

open Filter
open PrimeFactorOscillations.PrimeClassSampling

namespace PrimeFactorOscillations.PrimeClassDeletion

theorem greedyDeletedPrimeClass_eventually_theta_polylog_bound :
    Exists fun A : Real => And (0 <= A) (Exists fun C : Real => And (0 < C)
      (Filter.Eventually (fun X : Nat =>
        primeClassTheta greedyDeletedPrimeClass X <=
          A + C * ((X : Real) / (Real.log (X : Real)) ^ 2) +
            Real.log (X : Real)) atTop)) := by
  choose C0 h0 using Asymptotics.isBigO_iff'.mp (thetaError_isBigO_div_log_pow 0)
  choose C2 h2 using Asymptotics.isBigO_iff'.mp (thetaError_isBigO_div_log_pow 2)
  choose T0 hT0 using Filter.eventually_atTop.mp h0.2
  choose T2 hT2 using Filter.eventually_atTop.mp h2.2
  let T : Real := max 4 (max T0 T2)
  let A : Real := Chebyshev.theta T
  let C : Real := C0 + 4 * C2
  have hA : 0 <= A := Chebyshev.theta_nonneg T
  have hC : 0 < C := by dsimp only [C]; linarith only [h0.1, h2.1]
  have hT0T : T0 <= T := (le_max_left T0 T2).trans (le_max_right 4 (max T0 T2))
  have hT2T : T2 <= T := (le_max_right T0 T2).trans (le_max_right 4 (max T0 T2))
  have hRatio : Tendsto (fun X : Nat =>
      (Real.log (X : Real)) ^ 2 / Real.sqrt (X : Real)) atTop (nhds 0) := by
    simpa only [Nat.reduceAdd, Function.comp_def] using
      (tendsto_log_pow_div_sqrt 1).comp tendsto_natCast_atTop_atTop
  refine Exists.intro A (And.intro hA (Exists.intro C (And.intro hC ?_)))
  filter_upwards [hRatio.eventually (eventually_lt_nhds (by norm_num : (0 : Real) < 1)),
    eventually_ge_atTop (Nat.ceil (Real.exp 1) + 4)] with X hRatioX hX
  let x : Real := (X : Real)
  let l : Real := Real.log x
  let q : Real := Real.sqrt x
  have hFour : 4 <= X := by omega
  have hx : 0 < x := by dsimp only [x]; exact_mod_cast (by omega : 0 < X)
  have hExp : Real.exp 1 <= x :=
    (Nat.le_ceil (Real.exp 1)).trans (Nat.cast_le.mpr (by omega))
  have hl : 1 <= l := by
    have h := Real.log_le_log (Real.exp_pos 1) hExp
    simpa only [Real.log_exp] using h
  have hlPos : 0 < l := by linarith only [hl]
  have hlSq : 0 < l ^ 2 := by positivity
  have hq : 0 < q := Real.sqrt_pos.mpr hx
  have hqSq : q ^ 2 = x := Real.sq_sqrt hx.le
  have hLogRoot : Real.log q = l / 2 := Real.log_sqrt hx.le
  have hLogBound : l ^ 2 <= q := by
    change l ^ 2 / q < 1 at hRatioX
    have h := mul_lt_mul_of_pos_right hRatioX hq
    have heq : l ^ 2 / q * q = l ^ 2 := by field_simp [hq.ne']
    rw [heq, one_mul] at h
    exact h.le
  have hRootWeighted : q * l ^ 2 <= x := by
    have h := mul_le_mul_of_nonneg_left hLogBound hq.le
    nlinarith only [h, hqSq]
  have hRecord : greedyPrimeRegulator X <= A + C * (x / l ^ 2) := by
    apply (greedyPrimeRegulator_le_iff X _).mpr
    refine And.intro (by positivity) ?_
    intro p hp hpX
    rw [primeClassTheta_univ_eq_chebyshev]
    have hp0 : (0 : Real) <= (p : Real) := Nat.cast_nonneg p
    have hpPos : (0 : Real) < (p : Real) := Nat.cast_pos.mpr hp.pos
    have hpLe : (p : Real) <= x := Nat.cast_le.mpr hpX
    by_cases hSmallT : (p : Real) < T
    case pos =>
      have hTheta := Chebyshev.theta_mono hSmallT.le
      have hRest : 0 <= C * (x / l ^ 2) := by positivity
      change Chebyshev.theta (p : Real) - (p : Real) <=
        Chebyshev.theta T + C * (x / l ^ 2)
      linarith only [hTheta, hp0, hRest]
    case neg =>
      have hpT : T <= (p : Real) := le_of_not_gt hSmallT
      let e : Real := abs (Chebyshev.theta (p : Real) - (p : Real))
      let lp : Real := Real.log (p : Real)
      have he : 0 <= e := abs_nonneg _
      have hLp : 0 < lp := Real.log_pos (by exact_mod_cast hp.one_lt)
      have hP0 := hT0 (p : Real) (hT0T.trans hpT)
      have hP2 := hT2 (p : Real) (hT2T.trans hpT)
      simp only [Real.norm_eq_abs, pow_zero, div_one, abs_of_nonneg hp0] at hP0
      have hDivNonneg : 0 <= (p : Real) / lp ^ 2 := div_nonneg hp0 (sq_nonneg lp)
      simp only [Real.norm_eq_abs] at hP2
      change e <= C0 * (p : Real) at hP0
      change e <= C2 * abs ((p : Real) / lp ^ 2) at hP2
      rw [abs_of_nonneg hDivNonneg] at hP2
      have hWeighted : e * l ^ 2 <= C * x := by
        by_cases hSmall : (p : Real) <= q
        case pos =>
          have hPScaled := mul_le_mul_of_nonneg_right
            (hP0.trans (mul_le_mul_of_nonneg_left hSmall h0.1.le)) hlSq.le
          have hRScaled := mul_le_mul_of_nonneg_left hRootWeighted h0.1.le
          have hOther : 0 <= 4 * C2 * x :=
            mul_nonneg (mul_nonneg (by norm_num : (0 : Real) <= 4) h2.1.le) hx.le
          dsimp only [C]
          nlinarith only [hPScaled, hRScaled, hOther]
        case neg =>
          have hLog := Real.log_le_log hq (le_of_lt (lt_of_not_ge hSmall))
          rw [hLogRoot] at hLog
          change l / 2 <= lp at hLog
          have hSquare : l ^ 2 <= 4 * lp ^ 2 := by
            have hMinus : 0 <= 2 * lp - l := by linarith only [hLog]
            have hPlus : 0 <= 2 * lp + l := by linarith only [hLp, hl]
            have h := mul_nonneg hMinus hPlus
            nlinarith only [h]
          have hE := mul_le_mul_of_nonneg_left hSquare he
          have hP := mul_le_mul_of_nonneg_right hP2 (sq_nonneg lp)
          have hCancel : (C2 * ((p : Real) / lp ^ 2)) * lp ^ 2 =
              C2 * (p : Real) := by field_simp [hLp.ne']
          rw [hCancel] at hP
          have hPX := mul_le_mul_of_nonneg_left hpLe h2.1.le
          have hOther : 0 <= C0 * x := mul_nonneg h0.1.le hx.le
          dsimp only [C]
          nlinarith only [hE, hP, hPX, hOther]
      have hError : e <= C * (x / l ^ 2) := by
        have hCancel : (C * (x / l ^ 2)) * l ^ 2 = C * x := by field_simp [hlPos.ne']
        by_contra hFail
        have h := mul_lt_mul_of_pos_right (lt_of_not_ge hFail) hlSq
        rw [hCancel] at h
        linarith only [h, hWeighted]
      have hSign : Chebyshev.theta (p : Real) - (p : Real) <= e := le_abs_self _
      linarith only [hSign, hError, hA]
  have hMass := (greedyDeletedPrimeClass_record_bounds X (by omega)).2
  change primeClassTheta greedyDeletedPrimeClass X <= A + C * (x / l ^ 2) + l
  change primeClassTheta greedyDeletedPrimeClass X <= greedyPrimeRegulator X + l at hMass
  linarith only [hMass, hRecord]

end PrimeFactorOscillations.PrimeClassDeletion

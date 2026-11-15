/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianComplexCovarianceBounds

/-! # The full signed low Wick correction and its uniform truncation tail

The complete low correction is retained as the main term. A complex circle
bound controls only the difference between that value and its finite
Taylor truncation; it does not replace the signed correction by its norm.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

variable {Iota J : Type*} [Fintype Iota] [DecidableEq Iota]
variable [Fintype J] [DecidableEq J]

def gaussianWickLowValue (z : Iota -> Complex) (row : J -> Iota -> Complex) : Complex :=
  Finset.sum (Finset.range 4) (fun e =>
    Finset.sum (Finset.range (e + 1)) (fun v =>
      gaussianWickDiagramCoefficient z row e v))

theorem gaussianWickLowValue_analyticAt
    (z : Complex -> Iota -> Complex) (row : J -> Iota -> Complex) (s : Complex)
    (hz : forall i, AnalyticAt Complex (fun w => z w i) s) :
    AnalyticAt Complex (fun w => gaussianWickLowValue (z w) row) s := by
  unfold gaussianWickLowValue
  apply Finset.analyticAt_fun_sum
  intro e he
  apply Finset.analyticAt_fun_sum
  intro v hv
  exact gaussianWickDiagramCoefficient_analyticAt z row s hz e v

theorem gaussianWickLowValue_norm_bound
    (z : Iota -> Complex) (row : J -> Iota -> Complex) (n : Nat) (kappa : Real)
    (hCard : Fintype.card J = 2 * n) (hn : 3 <= n) (hKappa : 0 <= kappa)
    (hCov : forall i j, norm (gaussianLinearCovariance z (row i) (row j)) <=
      kappa / (n : Real)) :
    norm (gaussianWickLowValue z row) <=
      10 * (1 + 16 * Real.exp 1 * kappa) ^ 3 := by
  have hnPos : 0 < n := by omega
  have hnReal : 0 < (n : Real) := Nat.cast_pos.mpr hnPos
  have hnZero : Not ((n : Real) = 0) := ne_of_gt hnReal
  let C : Real := 16 * Real.exp 1 * kappa
  let M : Real := (1 + C) ^ 3
  have hC : 0 <= C := by dsimp only [C]; positivity
  have hBase : 1 <= 1 + C := by linarith
  have hM : 1 <= M := by
    simpa only [M, one_pow] using
      wick_nonnegative_power_le 1 (1 + C) (by norm_num) hBase 3
  have hTerm : forall e, Membership.mem (Finset.range 4) e ->
      forall v, Membership.mem (Finset.range (e + 1)) v ->
        norm (gaussianWickDiagramCoefficient z row e v) <= M := by
    intro e he v hv
    have he3 : e <= 3 := by have h := Finset.mem_range.mp he; omega
    have hVE : v <= e := by have h := Finset.mem_range.mp hv; omega
    by_cases hZero : e = 0
    case pos =>
      subst e
      have hvZero : v = 0 := by omega
      subst v
      have h := gaussianWickDiagramCoefficient_norm_bound z row
        (kappa / (n : Real)) (div_nonneg hKappa hnReal.le) hCov 0 0
      norm_num [wickPairCount] at h
      exact le_trans h hM
    case neg =>
      have hePos : 0 < e := Nat.pos_of_ne_zero hZero
      have hEN : (e : Real) <= (n : Real) := by exact_mod_cast (show e <= n by omega)
      have hRatio0 : 0 <= (e : Real) / (n : Real) :=
        div_nonneg (Nat.cast_nonneg e) hnReal.le
      have hRatio1 : (e : Real) / (n : Real) <= 1 := by
        have h := div_le_div_of_nonneg_right hEN hnReal.le
        simpa only [div_self hnZero] using h
      have hRest : 1 <= (1 + C) ^ (3 - e) := by
        simpa only [one_pow] using
          wick_nonnegative_power_le 1 (1 + C) (by norm_num) hBase (3 - e)
      have hDegree : C ^ e <= M := by
        calc
          _ <= (1 + C) ^ e :=
            wick_nonnegative_power_le C (1 + C) hC (by linarith) e
          _ <= (1 + C) ^ e * (1 + C) ^ (3 - e) := by
            simpa only [mul_one] using mul_le_mul_of_nonneg_left hRest
              (pow_nonneg (by linarith : 0 <= 1 + C) e)
          _ = _ := by rw [<- pow_add, Nat.add_sub_of_le he3]
      have hFactor : (16 * kappa) ^ e * Real.exp (e : Real) = C ^ e := by
        rw [wick_exp_nat_power, <- mul_pow]
        dsimp only [C]
        congr 1
        ring
      calc
        _ <= (16 * kappa) ^ e * Real.exp (e : Real) *
            ((e : Real) / (n : Real)) ^ (e - v) :=
          gaussianWickDiagramCoefficient_support_envelope z row n kappa e v
            hCard hnPos hKappa hePos hVE hCov
        _ <= (16 * kappa) ^ e * Real.exp (e : Real) := by
          have hNonneg : 0 <= (16 * kappa) ^ e * Real.exp (e : Real) :=
            mul_nonneg (pow_nonneg (by positivity) e) (Real.exp_pos (e : Real)).le
          have h := mul_le_mul_of_nonneg_left
            (wick_unit_power_le_one _ hRatio0 hRatio1 (e - v)) hNonneg
          simpa only [mul_one] using h
        _ <= _ := by rw [hFactor]; exact hDegree
  unfold gaussianWickLowValue
  calc
    _ <= Finset.sum (Finset.range 4) (fun e =>
      norm (Finset.sum (Finset.range (e + 1)) (fun v =>
        gaussianWickDiagramCoefficient z row e v))) := norm_sum_le _ _
    _ <= Finset.sum (Finset.range 4) (fun e => ((e + 1 : Nat) : Real) * M) := by
      apply Finset.sum_le_sum
      intro e he
      calc
        _ <= Finset.sum (Finset.range (e + 1)) (fun v =>
          norm (gaussianWickDiagramCoefficient z row e v)) := norm_sum_le _ _
        _ <= Finset.sum (Finset.range (e + 1)) (fun _ => M) :=
          Finset.sum_le_sum (fun v hv => hTerm e he v hv)
        _ = _ := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ = _ := by
      dsimp only [M, C]
      norm_num [Finset.sum_range_succ]
      ring

theorem gaussianWickLowValue_taylor_series
    (z : Complex -> Iota -> Complex) (row : J -> Iota -> Complex)
    (hz : forall i, AnalyticAt Complex (fun w => z w i) 0) :
    wickTaylorSeries (fun w => gaussianWickLowValue (z w) row) =
      wickSeriesLowDiagrams (gaussianCovarianceTaylorSeries z row) := by
  unfold gaussianWickLowValue wickSeriesLowDiagrams
  rw [wickTaylorSeries_finset_sum]
  case hf =>
    intro e he
    apply Finset.analyticAt_fun_sum
    intro v hv
    exact gaussianWickDiagramCoefficient_analyticAt z row 0 hz e v
  apply Finset.sum_congr rfl
  intro e he
  rw [wickTaylorSeries_finset_sum]
  case hf =>
    intro v hv
    exact gaussianWickDiagramCoefficient_analyticAt z row 0 hz e v
  apply Finset.sum_congr rfl
  intro v hv
  exact gaussianWickDiagramCoefficient_taylor_series z row hz e v

theorem gaussianWickLowValue_cauchy_remainder
    (z : Complex -> Iota -> Complex) (row : J -> Iota -> Complex)
    (n H : Nat) (kappa : Real) (R : NNReal)
    (hCard : Fintype.card J = 2 * n) (hn : 3 <= n) (hKappa : 0 <= kappa)
    (hR : 1 < (R : Real))
    (hz : forall w, Membership.mem (Metric.closedBall (0 : Complex) (R : Real)) w ->
      forall i, AnalyticAt Complex (fun t => z t i) w)
    (hCov : forall w, Membership.mem (Metric.sphere (0 : Complex) (R : Real)) w ->
      forall i j, norm (gaussianLinearCovariance (z w) (row i) (row j)) <=
        kappa / (n : Real)) :
    norm (gaussianWickLowValue (z 1) row -
      hamiltonianFiniteSeriesValue H
        (wickSeriesLowDiagrams (gaussianCovarianceTaylorSeries z row))) <=
      10 * (1 + 16 * Real.exp 1 * kappa) ^ 3 *
        (Inv.inv (R : Real)) ^ (H + 1) / (1 - (Inv.inv (R : Real))) := by
  let f := fun w => gaussianWickLowValue (z w) row
  have hR0 : 0 < R := by
    exact_mod_cast lt_trans (by norm_num : (0 : Real) < 1) hR
  have hSeries : HasFPowerSeriesOnBall f (cauchyPowerSeries f 0 R) 0 R := by
    apply DifferentiableOn.hasFPowerSeriesOnBall _ hR0
    intro w hw
    exact (gaussianWickLowValue_analyticAt z row w (hz w hw)).differentiableAt.differentiableWithinAt
  have hOne : Membership.mem (Metric.eball (0 : Complex) (R : ENNReal)) (1 : Complex) := by
    rw [mem_eball_zero_iff, enorm_lt_coe]
    simpa only [nnnorm_one] using (show (1 : NNReal) < R by exact_mod_cast hR)
  have hSum : HasSum (hamiltonianCauchyCoefficient f R) (f 1) := by
    change HasSum (fun k => cauchyPowerSeries f 0 R k (fun _ => 1)) (f 1)
    simpa only [zero_add] using hSeries.hasSum hOne
  have hCircle : forall w, Membership.mem (Metric.sphere (0 : Complex) (R : Real)) w ->
      norm (f w) <= 10 * (1 + 16 * Real.exp 1 * kappa) ^ 3 := by
    intro w hw
    exact gaussianWickLowValue_norm_bound (z w) row n kappa hCard hn hKappa (hCov w hw)
  have hTail := hamiltonianCauchyTail_of_hasSum f R _ (H + 1) hR hSum hCircle
  have hZero : Membership.mem (Metric.closedBall (0 : Complex) (R : Real)) (0 : Complex) := by
    rw [Metric.mem_closedBall, dist_self]
    exact_mod_cast R.property
  have hTaylor := gaussianWickLowValue_taylor_series z row (hz 0 hZero)
  have hCoeff : forall k, hamiltonianCauchyCoefficient f R k =
      PowerSeries.coeff k (wickSeriesLowDiagrams (gaussianCovarianceTaylorSeries z row)) := by
    intro k
    exact (hamiltonianCauchyCoefficient_eq_taylor f R hSeries k).trans
      (congrArg (fun P : PowerSeries Complex => PowerSeries.coeff k P) hTaylor)
  simp_rw [hCoeff] at hTail
  exact hTail

end PrimeFactorOscillations

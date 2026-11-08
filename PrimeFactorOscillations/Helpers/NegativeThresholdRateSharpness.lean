/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import PrimeFactorOscillations.Helpers.NegativeThresholdSplitFamily

/-! # Optimality of the square-root inverse rate at fixed threshold moments -/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 5000000

noncomputable section
namespace PrimeFactorOscillations


def thresholdNegativeSplitDefect (d M K N q : Real) : Real :=
  Finset.sum Finset.univ (fun i => thresholdNegativeSplitWeights d M K N q i *
    thresholdNegativeSplitCoords d M K q i * (thresholdNegativeSplitCoords d M K q i - 1) ^ 2) -
      thresholdNegativeCost d M K

def thresholdNegativeSplitError (d M K N q : Real) : Real :=
  let z := thresholdNegativeRoot d M K
  abs (Finset.sum Finset.univ (fun i => thresholdNegativeSplitWeights d M K N q i *
    abs (thresholdNegativeSplitCoords d M K q i - z)) -
      negativeThresholdCanonicalStatistic d z M K N (fun y => abs (y - z)))

def thresholdNegativeSplitLaw (d M K N q : Real) : Prop :=
  let a := thresholdNegativeSplitWeights d M K N q
  let y := thresholdNegativeSplitCoords d M K q
  And (forall i, 0 <= a i) (And (forall i, 0 <= y i)
    (And (Finset.sum Finset.univ a = N)
      (And (Finset.sum Finset.univ (fun i => a i * y i) = M)
        (And (Finset.sum Finset.univ (fun i => a i * (y i) ^ 2) = M)
          (thresholdSelectedMass d Finset.univ a y = K)))))

private theorem negativeSplit_defect_formula (d M K N q : Real)
    (hd : And (0 < d) (d < 1)) (hM : 0 < M) (hMK : M < K) (hDomain : d * K < M) :
    thresholdNegativeSplitDefect d M K N q =
      (M - d * K) * (thresholdNegativeRoot d M K - d) ^ 2 *
        q ^ 2 * (1 - q ^ 2) / (1 + q ^ 2) ^ 2 := by
  have hh := (thresholdNegativeSplit_moments d M K N q hd hM hMK hDomain).2.2
  unfold thresholdNegativeSplitDefect
  rw [hh]
  ring

private theorem negativeSplit_error_formula (d M K N q : Real)
    (hd : And (0 < d) (d < 1)) (hM : 0 < M) (hMK : M < K) (hDomain : d * K < M)
    (hq : And (0 <= q) (q <= 1)) :
    thresholdNegativeSplitError d M K N q = (M - d * K) * q * (1 - q) := by
  dsimp only [thresholdNegativeSplitError]
  rw [thresholdNegativeSplit_statistic d M K N q hd hM hMK hDomain hq]
  exact abs_of_nonneg
    (mul_nonneg (mul_nonneg (sub_nonneg.mpr hDomain.le) hq.1) (sub_nonneg.mpr hq.2))

theorem thresholdNegativeSplit_rate_bounds (d M K N q : Real)
    (hd : And (0 < d) (d < 1)) (hM : 0 < M) (hMK : M < K) (hDomain : d * K < M)
    (hq : And (0 < q) (q <= thresholdNegativeSplitWindow d M K)) :
    let g := thresholdNegativeRoot d M K - d
    let A := M - d * K
    let delta := thresholdNegativeSplitDefect d M K N q
    let D := thresholdNegativeSplitError d M K N q
    And (0 < delta) (And (delta <= A * g ^ 2 * q ^ 2)
      (And (0 < D) (And (A * q / 2 <= D) (delta <= (4 * g ^ 2 / A) * D ^ 2)))) := by
  dsimp only
  let g := thresholdNegativeRoot d M K - d
  let A := M - d * K
  let delta := thresholdNegativeSplitDefect d M K N q
  let D := thresholdNegativeSplitError d M K N q
  have hg : 0 < g := (thresholdNegativeSplit_constants d M K hd hM hMK hDomain).1
  have hA : 0 < A := sub_pos.mpr hDomain
  have hSmall : q <= 1 / 4 := le_trans hq.2 (min_le_left _ _)
  have hOne : q < 1 := by linarith only [hSmall]
  have hQSquare : q ^ 2 <= q := by
    have hp := mul_nonneg hq.1.le (sub_nonneg.mpr hOne.le)
    nlinarith only [hp]
  have hQSquareOne : q ^ 2 < 1 := lt_of_le_of_lt hQSquare hOne
  have hv : 0 < 1 + q ^ 2 := by nlinarith only [sq_nonneg q]
  have hDeltaId : delta = A * g ^ 2 * q ^ 2 * (1 - q ^ 2) / (1 + q ^ 2) ^ 2 :=
    negativeSplit_defect_formula d M K N q hd hM hMK hDomain
  have hErrorId : D = A * q * (1 - q) :=
    negativeSplit_error_formula d M K N q hd hM hMK hDomain (And.intro hq.1.le hOne.le)
  have hDeltaPos : 0 < delta := by
    rw [hDeltaId]
    exact div_pos
      (mul_pos (mul_pos (mul_pos hA (sq_pos_of_pos hg)) (sq_pos_of_pos hq.1))
        (sub_pos.mpr hQSquareOne)) (sq_pos_of_pos hv)
  have hFraction : (1 - q ^ 2) / (1 + q ^ 2) ^ 2 <= 1 :=
    (div_le_one (sq_pos_of_pos hv)).mpr (by nlinarith only [sq_nonneg q, sq_nonneg (q ^ 2)])
  have hPositive : 0 <= A * g ^ 2 * q ^ 2 :=
    mul_nonneg (mul_nonneg hA.le (sq_nonneg g)) (sq_nonneg q)
  have hUpper : delta <= A * g ^ 2 * q ^ 2 := by
    calc
      _ = (A * g ^ 2 * q ^ 2) * ((1 - q ^ 2) / (1 + q ^ 2) ^ 2) := by rw [hDeltaId]; ring
      _ <= (A * g ^ 2 * q ^ 2) * 1 := mul_le_mul_of_nonneg_left hFraction hPositive
      _ = _ := by ring
  have hDPos : 0 < D := by
    rw [hErrorId]
    exact mul_pos (mul_pos hA hq.1) (sub_pos.mpr hOne)
  have hDLower : A * q / 2 <= D := by
    rw [hErrorId]
    have hp := mul_le_mul_of_nonneg_left
      (show (1 / 2 : Real) <= 1 - q by linarith only [hSmall]) (mul_nonneg hA.le hq.1.le)
    nlinarith only [hp]
  have hAQ : 0 < A * q := mul_pos hA hq.1
  have hProduct := mul_nonneg (show 0 <= 2 * D - A * q by linarith only [hDLower])
    (show 0 <= 2 * D + A * q by linarith only [hDPos, hAQ])
  have hSquare : A ^ 2 * q ^ 2 <= 4 * D ^ 2 := by nlinarith only [hProduct]
  have hScale := mul_le_mul_of_nonneg_left hSquare (div_nonneg (sq_nonneg g) hA.le)
  have hLeft : (g ^ 2 / A) * (A ^ 2 * q ^ 2) = A * g ^ 2 * q ^ 2 := by
    calc
      _ = (A / A) * (A * g ^ 2 * q ^ 2) := by ring
      _ = _ := by rw [div_self hA.ne', one_mul]
  have hRight : (g ^ 2 / A) * (4 * D ^ 2) = (4 * g ^ 2 / A) * D ^ 2 := by ring
  rw [hLeft, hRight] at hScale
  exact And.intro hDeltaPos (And.intro hUpper (And.intro hDPos
    (And.intro hDLower (le_trans hUpper hScale))))

theorem thresholdNegativeSplit_arbitrarily_small (d M K N eps : Real)
    (hd : And (0 < d) (d < 1)) (hM : 0 < M) (hMK : M < K) (hDomain : d * K < M)
    (heps : 0 < eps) :
    exists q : Real, And (0 < q) (And (q <= thresholdNegativeSplitWindow d M K)
      (And (0 < thresholdNegativeSplitDefect d M K N q)
        (And (thresholdNegativeSplitDefect d M K N q < eps)
          (And (0 < thresholdNegativeSplitError d M K N q)
            (thresholdNegativeSplitDefect d M K N q <=
              (4 * (thresholdNegativeRoot d M K - d) ^ 2 / (M - d * K)) *
                (thresholdNegativeSplitError d M K N q) ^ 2))))) := by
  let eta := thresholdNegativeSplitWindow d M K
  let g := thresholdNegativeRoot d M K - d
  let A := M - d * K
  let H := A * g ^ 2
  let q := min (eta / 2) (eps / (2 * H))
  have hc := thresholdNegativeSplit_constants d M K hd hM hMK hDomain
  have hg : 0 < g := hc.1
  have hEta : 0 < eta := hc.2.2.2
  have hA : 0 < A := sub_pos.mpr hDomain
  have hH : 0 < H := mul_pos hA (sq_pos_of_pos hg)
  have hq : 0 < q := lt_min (div_pos hEta (by norm_num)) (div_pos heps (by linarith only [hH]))
  have hqEta : q <= eta := le_trans (min_le_left _ _) (by linarith only [hEta])
  have hb := thresholdNegativeSplit_rate_bounds d M K N q hd hM hMK hDomain (And.intro hq hqEta)
  have hSmall : q <= 1 / 4 := le_trans hqEta (min_le_left _ _)
  have hQSquare : q ^ 2 <= q := by
    have hp := mul_nonneg hq.le (show 0 <= 1 - q by linarith only [hSmall])
    nlinarith only [hp]
  have hBound := mul_le_mul_of_nonneg_left hQSquare hH.le
  have hqEps : q <= eps / (2 * H) := min_le_right _ _
  have hMultiply := mul_le_mul_of_nonneg_right hqEps (show 0 <= 2 * H by linarith only [hH])
  have hCancel : (eps / (2 * H)) * (2 * H) = eps := by field_simp [hH.ne']
  rw [hCancel] at hMultiply
  have hDeltaEps : thresholdNegativeSplitDefect d M K N q < eps := by
    have hUpper : thresholdNegativeSplitDefect d M K N q <= H * q ^ 2 := hb.2.1
    nlinarith only [hUpper, hBound, hMultiply, heps]
  exact Exists.intro q (And.intro hq (And.intro hqEta (And.intro hb.1
    (And.intro hDeltaEps (And.intro hb.2.2.1 hb.2.2.2.2)))))

private theorem negativeSplit_power_small (L C a : Real) (ha : 0 < a) :
    exists e : Real, And (0 < e)
      (forall x : Real, And (0 < x) (x < e) -> L * C ^ 2 * x ^ a < 1) := by
  have hCont : ContinuousAt (fun x : Real => L * C ^ 2 * x ^ a) 0 :=
    continuousAt_const.mul (Real.continuous_rpow_const ha.le).continuousAt
  have hZero : L * C ^ 2 * (0 : Real) ^ a < 1 := by
    rw [Real.zero_rpow ha.ne', mul_zero]
    norm_num
  have hEvent : Filter.Eventually (fun x : Real => L * C ^ 2 * x ^ a < 1) (nhds 0) :=
    hCont.tendsto.eventually (Iio_mem_nhds hZero)
  choose e he hBall using (Metric.mem_nhds_iff.mp hEvent)
  refine Exists.intro e (And.intro he ?_)
  intro x hx
  have hMem : Membership.mem (Metric.ball (0 : Real) e) x := by
    change dist x 0 < e
    simpa only [Real.dist_eq, sub_zero, abs_of_pos hx.1] using hx.2
  exact hBall hMem

private theorem negativeSplit_power_contradiction (delta D L C h : Real)
    (hDelta : 0 < delta) (hD : 0 < D) (hL : 0 < L) (hC : 0 <= C)
    (hLower : delta <= L * D ^ 2)
    (hSmall : L * C ^ 2 * delta ^ (2 * h - 1) < 1)
    (hUpper : D <= C * delta ^ h) : False := by
  have hPower : delta ^ h * delta ^ h = delta * delta ^ (2 * h - 1) := by
    calc
      _ = delta ^ (h + h) := (Real.rpow_add hDelta h h).symm
      _ = delta ^ (1 + (2 * h - 1)) := by congr 1; ring
      _ = delta * delta ^ (2 * h - 1) := by rw [Real.rpow_add hDelta, Real.rpow_one]
  have hCD : 0 <= C * delta ^ h := mul_nonneg hC (Real.rpow_pos_of_pos hDelta h).le
  have hProduct := mul_nonneg (sub_nonneg.mpr hUpper) (add_nonneg hCD hD.le)
  have hSquare : D ^ 2 <= C ^ 2 * delta * delta ^ (2 * h - 1) := by
    calc
      _ <= (C * delta ^ h) ^ 2 := by nlinarith only [hProduct]
      _ = C ^ 2 * (delta ^ h * delta ^ h) := by ring
      _ = _ := by rw [hPower]; ring
  have hScale := mul_le_mul_of_nonneg_left hSquare hL.le
  have hStrict : L * (C ^ 2 * delta * delta ^ (2 * h - 1)) < delta := by
    calc
      _ = delta * (L * C ^ 2 * delta ^ (2 * h - 1)) := by ring
      _ < delta * 1 := mul_lt_mul_of_pos_left hSmall hDelta
      _ = _ := by ring
  nlinarith only [hLower, hScale, hStrict]

theorem thresholdNegativeSplit_no_better_holder (d M K N h C eps : Real)
    (hd : And (0 < d) (d < 1)) (hM : 0 < M) (hMK : M < K) (hDomain : d * K < M)
    (hN : K <= N) (hh : 1 / 2 < h) (hC : 0 <= C) (heps : 0 < eps) :
    let z := thresholdNegativeRoot d M K
    And (forall u v : Real, abs (abs (u - z) - abs (v - z)) <= abs (u - v))
      (exists q : Real, And (0 < q) (And (q <= thresholdNegativeSplitWindow d M K)
        (And (thresholdNegativeSplitLaw d M K N q)
          (And (0 < thresholdNegativeSplitDefect d M K N q)
            (And (thresholdNegativeSplitDefect d M K N q < eps)
              (C * (thresholdNegativeSplitDefect d M K N q) ^ h <
                thresholdNegativeSplitError d M K N q)))))) := by
  dsimp only
  constructor
  case left =>
    intro u v
    have hp := abs_abs_sub_abs_le_abs_sub (u - thresholdNegativeRoot d M K) (v - thresholdNegativeRoot d M K)
    have hId : (u - thresholdNegativeRoot d M K) - (v - thresholdNegativeRoot d M K) = u - v := by ring
    rw [hId] at hp
    exact hp
  case right =>
    let g := thresholdNegativeRoot d M K - d
    let A := M - d * K
    let L := 4 * g ^ 2 / A
    have hg : 0 < g := (thresholdNegativeSplit_constants d M K hd hM hMK hDomain).1
    have hA : 0 < A := sub_pos.mpr hDomain
    have hL : 0 < L := div_pos (mul_pos (by norm_num) (sq_pos_of_pos hg)) hA
    have hPower : 0 < 2 * h - 1 := by linarith only [hh]
    choose e he hSmall using negativeSplit_power_small L C (2 * h - 1) hPower
    choose q hq hqWindow hDelta hDeltaSmall hD hLower using
      thresholdNegativeSplit_arbitrarily_small d M K N (min eps e) hd hM hMK hDomain (lt_min heps he)
    have hDeltaEps : thresholdNegativeSplitDefect d M K N q < eps :=
      lt_of_lt_of_le hDeltaSmall (min_le_left _ _)
    have hDeltaE : thresholdNegativeSplitDefect d M K N q < e :=
      lt_of_lt_of_le hDeltaSmall (min_le_right _ _)
    have hStrict : C * (thresholdNegativeSplitDefect d M K N q) ^ h <
        thresholdNegativeSplitError d M K N q := by
      by_contra hn
      have hUpper : thresholdNegativeSplitError d M K N q <=
          C * (thresholdNegativeSplitDefect d M K N q) ^ h := le_of_not_gt hn
      exact negativeSplit_power_contradiction (thresholdNegativeSplitDefect d M K N q)
        (thresholdNegativeSplitError d M K N q) L C h hDelta hD hL hC hLower
        (hSmall _ (And.intro hDelta hDeltaE)) hUpper
    have ha := thresholdNegativeSplit_admissible d M K N q hd hM hMK hDomain hN (And.intro hq hqWindow)
    have hm := thresholdNegativeSplit_moments d M K N q hd hM hMK hDomain
    have hLaw : thresholdNegativeSplitLaw d M K N q :=
      And.intro ha.1 (And.intro ha.2.1 (And.intro ha.2.2.1
        (And.intro hm.1 (And.intro hm.2.1 ha.2.2.2))))
    exact Exists.intro q (And.intro hq (And.intro hqWindow (And.intro hLaw
      (And.intro hDelta (And.intro hDeltaEps hStrict)))))

end PrimeFactorOscillations

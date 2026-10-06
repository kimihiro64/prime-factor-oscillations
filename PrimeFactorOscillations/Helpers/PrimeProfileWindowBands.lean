/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.TiltedCountExcursion

/-!
# Uniform ratio bands for a fixed window rank

The actual coefficient ratio and the full-profile reference both approach
r / L uniformly in compact positive rank bands. Freezing the rank at the
left edge of a dyadic window gives a common half-unit band at every cutoff.
This supplies the support and grid margins for localized reversal counts.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

open Filter Robin1984

theorem exists_primeProfile_reference_rank_error (B : Real) (hB : 0 <= B) :
    exists r0 : Nat, exists K : Real, 0 < r0 /\ 0 <= K /\
      forall r : Nat, r0 <= r -> forall L : Real, 0 < L -> (r : Real) / L <= B ->
        abs (Nat.factorialConvolution primeProfileRealCoefficient (r - 1) L /
          Nat.factorialConvolution primeProfileRealCoefficient r L -
          (r : Real) / L) <= K / r := by
  choose M hM hDeriv using exists_primeProfile_normalized_derivative_bounds B hB
  choose r0 hr0 hLower using exists_primeProfile_normalized_coefficient_lower_bound B hB
  let v : Real := Real.exp (-(B ^ 2 * tsum (fun p : Nat.Primes =>
    (primeProfileWeight (p : Nat)) ^ 2)) / 2) / 2
  have hv : 0 < v := by dsimp [v]; positivity
  refine Exists.intro r0 (Exists.intro (B ^ 2 * M / v)
    (And.intro hr0 (And.intro (by positivity) ?_)))
  intro r hr L hL hRatio
  let t := (r : Real) / L
  let A := Nat.normalizedDescFactorialPolynomial primeProfileRealCoefficient r t
  have hrPos : 0 < r := hr0.trans_le hr
  have hrReal : (0 : Real) < r := by exact_mod_cast hrPos
  have ht : 0 <= t := by dsimp [t]; positivity
  have hA : v <= A := hLower r hr t ht hRatio
  have hAPos : 0 < A := hv.trans_le hA
  have hD := (hDeriv r hrPos t ht hRatio).1
  rw [Nat.factorialConvolution_ratio_eq_normalized_logDeriv
    primeProfileRealCoefficient r hrPos L hL.ne' hAPos.ne']
  change abs ((t - (t ^ 2 / r) *
    deriv (Nat.normalizedDescFactorialPolynomial primeProfileRealCoefficient r) t / A) - t) <= _
  rw [sub_sub_cancel_left, abs_neg, abs_div, abs_mul,
    abs_of_nonneg (div_nonneg (sq_nonneg t) hrReal.le), abs_of_pos hAPos]
  calc
    (t ^ 2 / r) * abs (deriv (Nat.normalizedDescFactorialPolynomial
        primeProfileRealCoefficient r) t) / A <= (B ^ 2 / r) * M / v := by
      have hNum : (t ^ 2 / r) * abs (deriv
          (Nat.normalizedDescFactorialPolynomial primeProfileRealCoefficient r) t) <=
          (B ^ 2 / r) * M := by
        apply mul_le_mul
        . apply div_le_div_of_nonneg_right _ hrReal.le
          nlinarith
        . exact hD
        . exact abs_nonneg _
        . positivity
      exact (div_le_div_of_nonneg_right hNum hAPos.le).trans
        (div_le_div_of_nonneg_left (by positivity) hv hA)
    _ = (B ^ 2 * M / v) / r := by ring

theorem tendsto_nicolasLog_zero_unconditionally :
    Tendsto nicolasLogMertensOscillation atTop (nhds (0 : Real)) := by
  have hNat : Tendsto (fun N : Nat => nicolasLogMertensOscillation (N : Real))
      atTop (nhds (0 : Real)) := by
    have h := tendsto_primePrefixProfile_logSum_sub_thetaClock.neg
    simp only [neg_zero] at h
    apply h.congr'
    filter_upwards [tendsto_primeProfile_theta_atTop.eventually_gt_atTop 1] with N hTheta
    rw [nicolasLog_nat_eq_primeProfile_clock_difference N hTheta]
    ring
  have hFloor : Tendsto (fun x : Real => Nat.floor x) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    filter_upwards [eventually_ge_atTop (b : Real)] with x hx
    exact Nat.le_floor hx
  have h := hNat.comp hFloor
  apply h.congr'
  filter_upwards [] with x
  exact nicolasLogMertensOscillation_natFloor x

theorem exists_eventually_primeProfile_rank_band_error
    (a B : Real) (ha : 0 < a) (haB : a <= B) :
    exists D : Real, 0 <= D /\
      Filter.Eventually (fun x : Real =>
        let L := Real.eulerMascheroniConstant + Real.log (Real.log (Chebyshev.theta x))
        2 <= L /\ forall r : Nat, a <= (r : Real) / L -> (r : Real) / L <= B ->
          0 < (PrimeFactorUnimodality.weightEsymm
            (PrimeFactorUnimodality.primesBelow (Nat.floor x + 1)) r : Real) /\
          abs (Nat.factorialConvolution primeProfileRealCoefficient (r - 1) L /
            Nat.factorialConvolution primeProfileRealCoefficient r L -
              (r : Real) / L) <= D / L /\
          abs ((PrimeFactorUnimodality.densityRatio
            (PrimeFactorUnimodality.primesBelow (Nat.floor x + 1)) r : Real) -
              (r : Real) / L) <= D / L) atTop := by
  have hB : 0 < B := ha.trans_le haB
  choose r1 K hr1 hK hLin using
    exists_eventually_densityRatio_real_thetaClock_linearization B hB
  choose r2 J hr2 hJ hRef using exists_primeProfile_reference_rank_error B hB.le
  let D := J / a + B + K * (1 + 1 / a)
  have hD : 0 <= D := by dsimp [D]; positivity
  refine Exists.intro D (And.intro hD ?_)
  have hF := tendsto_nicolasLog_zero_unconditionally.abs.eventually_lt_const
    (by norm_num : abs (0 : Real) < 1)
  have hClock : Tendsto (fun x : Real => Real.eulerMascheroniConstant +
      Real.log (Real.log (Chebyshev.theta x))) atTop atTop :=
    tendsto_const_nhds.add_atTop (Real.tendsto_log_atTop.comp
      (Real.tendsto_log_atTop.comp
        (primeProfile_theta_isEquivalent_id.symm.tendsto_atTop tendsto_id)))
  filter_upwards [hLin, hF, eventually_ge_atTop (1 : Real),
    hClock.eventually_ge_atTop
      ((max r1 r2 : Nat) / a)] with x hx hFx hxOne hLarge
  dsimp only at hx
  let L := Real.eulerMascheroniConstant + Real.log (Real.log (Chebyshev.theta x))
  have hL : 2 <= L := hx.2.1
  have hLp : 0 < L := by linarith
  refine And.intro hL ?_
  intro r hra hrB
  have har : a * L <= (r : Real) := by
    have h := mul_le_mul_of_nonneg_right hra hLp.le
    have he : (r : Real) / L * L = r := by field_simp
    rwa [he] at h
  have hrp : (0 : Real) < r := (mul_pos ha hLp).trans_le har
  have hrmax : max r1 r2 <= r := by
    have h := mul_le_mul_of_nonneg_right hLarge ha.le
    have he : ((max r1 r2 : Nat) : Real) / a * a = max r1 r2 := by field_simp
    rw [he] at h
    have hmax : ((max r1 r2 : Nat) : Real) <= a * L := by nlinarith
    exact_mod_cast hmax.trans har
  have hlin := hx.2.2 r ((le_max_left r1 r2).trans hrmax) hrB
  have href := hRef r ((le_max_right r1 r2).trans hrmax) L hLp hrB
  have hJr : J / (r : Real) <= (J / a) / L := by
    calc
      J / (r : Real) <= J / (a * L) := div_le_div_of_nonneg_left hJ (mul_pos ha hLp) har
      _ = (J / a) / L := by ring
  have hinv : (1 : Real) / ((r : Real) * x) <= (1 / a) / L := by
    calc
      (1 : Real) / ((r : Real) * x) <= 1 / (r : Real) := by
        apply one_div_le_one_div_of_le hrp
        nlinarith
      _ <= 1 / (a * L) := one_div_le_one_div_of_le (mul_pos ha hLp) har
      _ = (1 / a) / L := by ring
  have hFsmall : abs (nicolasLogMertensOscillation x) / L ^ 2 <= 1 / L := by
    calc
      abs (nicolasLogMertensOscillation x) / L ^ 2 <= L / L ^ 2 :=
        div_le_div_of_nonneg_right (hFx.le.trans (by linarith)) (sq_nonneg L)
      _ = 1 / L := by field_simp <;> ring
  have hLead : abs (((r : Real) / L ^ 2) * nicolasLogMertensOscillation x) <= B / L := by
    rw [abs_mul, abs_of_nonneg (div_nonneg hrp.le (sq_nonneg L))]
    calc
      (r : Real) / L ^ 2 * abs (nicolasLogMertensOscillation x) <= (r : Real) / L ^ 2 :=
        mul_le_of_le_one_right (by positivity) hFx.le
      _ = ((r : Real) / L) / L := by ring
      _ <= B / L := div_le_div_of_nonneg_right hrB hLp.le
  have hRefD : J / a <= D := by
    dsimp [D]
    have hNon : 0 <= K * (1 + 1 / a) := by positivity
    linarith
  refine And.intro hlin.1 (And.intro
    (href.trans (hJr.trans (div_le_div_of_nonneg_right hRefD hLp.le))) ?_)
  let R : Real := PrimeFactorUnimodality.densityRatio
    (PrimeFactorUnimodality.primesBelow (Nat.floor x + 1)) r
  let U := Nat.factorialConvolution primeProfileRealCoefficient (r - 1) L /
    Nat.factorialConvolution primeProfileRealCoefficient r L
  let Q := ((r : Real) / L ^ 2) * nicolasLogMertensOscillation x
  have hSplit : R - (r : Real) / L = (R - U - Q) + Q + (U - (r : Real) / L) := by ring
  change abs (R - (r : Real) / L) <= D / L
  rw [hSplit]
  calc
    abs ((R - U - Q) + Q + (U - (r : Real) / L)) <=
        abs (R - U - Q) + abs Q + abs (U - (r : Real) / L) :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ <= K * (1 / L + (1 / a) / L) + B / L + (J / a) / L := by
      apply add_le_add
      . apply add_le_add
        . exact hlin.2.2.trans (mul_le_mul_of_nonneg_left (add_le_add hFsmall hinv) hK)
        . exact hLead
      . exact href.trans hJr
    _ = D / L := by dsimp [D]; ring

theorem eventually_primeProfile_fixed_window_bands (alpha : Real) (ha : 0 < alpha) :
    Filter.Eventually (fun X : Real =>
      let L : Real -> Real := fun y => Real.eulerMascheroniConstant +
        Real.log (Real.log (Chebyshev.theta y))
      let r := Nat.floor (alpha * L X)
      1 <= r /\ forall y : Real, X <= y -> y <= 2 * X ->
        alpha / 3 <= (r : Real) / L y /\ (r : Real) / L y <= 2 * alpha /\
        0 < (PrimeFactorUnimodality.weightEsymm
          (PrimeFactorUnimodality.primesBelow (Nat.floor y + 1)) r : Real) /\
        abs (Nat.factorialConvolution primeProfileRealCoefficient (r - 1) (L y) /
          Nat.factorialConvolution primeProfileRealCoefficient r (L y) - alpha) <= 1 / 2 /\
        abs ((PrimeFactorUnimodality.densityRatio
          (PrimeFactorUnimodality.primesBelow (Nat.floor y + 1)) r : Real) - alpha) <= 1 / 2)
      atTop := by
  let L : Real -> Real := fun y => Real.eulerMascheroniConstant +
    Real.log (Real.log (Chebyshev.theta y))
  have hClock : Tendsto L atTop atTop :=
    tendsto_const_nhds.add_atTop (Real.tendsto_log_atTop.comp
      (Real.tendsto_log_atTop.comp
        (primeProfile_theta_isEquivalent_id.symm.tendsto_atTop tendsto_id)))
  choose D hD hEvent using exists_eventually_primeProfile_rank_band_error
    (alpha / 3) (2 * alpha) (by linarith) (by linarith)
  choose Y hY using eventually_atTop.mp hEvent
  filter_upwards [eventually_thetaClock_dyadic_width,
    hClock.eventually_ge_atTop 2, hClock.eventually_ge_atTop (2 / alpha),
    hClock.eventually_ge_atTop (2 * (D + alpha + 1)),
    eventually_ge_atTop Y] with X hWidth hTwo hLarge hSmall hXY
  dsimp only
  let r := Nat.floor (alpha * L X)
  have hAlphaL : 2 <= alpha * L X := by
    have h := mul_le_mul_of_nonneg_left hLarge ha.le
    have he : alpha * (2 / alpha) = 2 := by field_simp [ha.ne']
    rwa [he] at h
  have hr : 1 <= r :=
    (Nat.floor_mul_div_mem_compact_of_abs_sub_le_one
      alpha (L X) (L X) ha hTwo hAlphaL (by simp)).1
  refine And.intro hr ?_
  intro y hxy hyx
  have hWidths := hWidth.2 y hxy hyx
  change 0 <= L y - L X /\ L y - L X <= 1 at hWidths
  have hAbs : abs (L y - L X) <= 1 := by
    rw [abs_of_nonneg hWidths.1]
    exact hWidths.2
  have hBand := (Nat.floor_mul_div_mem_compact_of_abs_sub_le_one
    alpha (L y) (L X) ha hTwo hAlphaL hAbs).2
    (L y) (And.intro (min_le_left _ _) (le_max_left _ _))
  have hPoint := hY y (hXY.trans hxy)
  dsimp only at hPoint
  have hLy : 0 < L y := by linarith [hPoint.1]
  have hb := hPoint.2 r hBand.2.1 hBand.2.2
  refine And.intro hBand.2.1 (And.intro hBand.2.2 (And.intro hb.1 ?_))
  have hrUp : (r : Real) <= alpha * L X := Nat.floor_le (by linarith)
  have hrLow : alpha * L X < (r : Real) + 1 := Nat.lt_floor_add_one _
  have htUp : (r : Real) / L y <= alpha := by
    calc
      (r : Real) / L y <= (alpha * L y) / L y := by
        apply div_le_div_of_nonneg_right _ hLy.le
        nlinarith
      _ = alpha := by field_simp
  have htError : abs ((r : Real) / L y - alpha) <= (alpha + 1) / L y := by
    rw [abs_of_nonpos (sub_nonpos.mpr htUp), neg_sub]
    calc
      alpha - (r : Real) / L y = (alpha * L y - r) / L y := by field_simp <;> ring
      _ <= (alpha + 1) / L y := by
        apply div_le_div_of_nonneg_right _ hLy.le
        nlinarith
  have hTotal : (D + alpha + 1) / L y <= (1 : Real) / 2 := by
    calc
      (D + alpha + 1) / L y <= ((1 / 2) * L y) / L y := by
        apply div_le_div_of_nonneg_right _ hLy.le
        linarith
      _ = 1 / 2 := by field_simp
  have hTransfer : forall v : Real, abs (v - (r : Real) / L y) <= D / L y ->
      abs (v - alpha) <= (1 : Real) / 2 := by
    intro v hv
    calc
      abs (v - alpha) = abs ((v - (r : Real) / L y) + ((r : Real) / L y - alpha)) := by ring_nf
      _ <= abs (v - (r : Real) / L y) + abs ((r : Real) / L y - alpha) := abs_add_le _ _
      _ <= D / L y + (alpha + 1) / L y := add_le_add hv htError
      _ = (D + alpha + 1) / L y := by ring
      _ <= 1 / 2 := hTotal
  exact And.intro (hTransfer _ hb.2.1) (hTransfer _ hb.2.2)

end PrimeFactorOscillations

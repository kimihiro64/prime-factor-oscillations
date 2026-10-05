/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.NicolasPowerPeak
import PrimeFactorOscillations.Helpers.PrimeProfileCanonicalLinearization

/-!
# Quantitative power excursions of the actual moving-rank ratio

The paired canonical coefficient estimate preserves both signs of the
Nicolas logarithm after multiplication by the actual theta clock. The
prescribed floor rank lies in a fixed positive compact band. Its actual and
reference denominators remain positive, and the reciprocal additive loss is
negligible at every admissible zero-dependent power scale. The rank grows
with the endpoint; this does not give infinitely many raw ascents at a fixed
rank or independent smaller-gap supply.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

open Filter Robin1984

/-- The actual ratio error preserves both signs of its Nicolas signal on
every fixed compact positive rank band, with a reciprocal additive loss. -/
theorem exists_eventually_densityRatio_signed_thetaClock_margin
    (a B : Real) (ha : 0 < a) (haB : a <= B) :
    exists K : Real, 0 <= K /\ Filter.Eventually (fun x : Real =>
      let L := Real.eulerMascheroniConstant + Real.log (Real.log (Chebyshev.theta x))
      let F := nicolasLogMertensOscillation x
      1 < Chebyshev.theta x /\ 2 <= L /\
      forall r : Nat, a <= (r : Real) / L -> (r : Real) / L <= B ->
        0 < (PrimeFactorUnimodality.weightEsymm
          (PrimeFactorUnimodality.primesBelow (Nat.floor x + 1)) r : Real) /\
        0 < Nat.factorialConvolution primeProfileRealCoefficient r L /\
        (let E := L * ((PrimeFactorUnimodality.densityRatio
            (PrimeFactorUnimodality.primesBelow (Nat.floor x + 1)) r : Real) -
          Nat.factorialConvolution primeProfileRealCoefficient (r - 1) L /
            Nat.factorialConvolution primeProfileRealCoefficient r L)
         (0 <= F -> (a / 2) * F - K / (a * x) <= E) /\
         (F <= 0 -> E <= (a / 2) * F + K / (a * x)))) atTop := by
  choose r0 K hr0 hK hApprox using
    exists_eventually_densityRatio_real_thetaClock_linearization B (ha.trans_le haB)
  have hTheta : Tendsto Chebyshev.theta atTop atTop :=
    primeProfile_theta_isEquivalent_id.symm.tendsto_atTop tendsto_id
  have hClock : Tendsto (fun x : Real => Real.eulerMascheroniConstant +
      Real.log (Real.log (Chebyshev.theta x))) atTop atTop :=
    tendsto_const_nhds.add_atTop
      (Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp hTheta))
  refine Exists.intro K (And.intro hK ?_)
  filter_upwards [hApprox,
    hClock.eventually_ge_atTop (((r0 : Real) + 2 * K + 1) / a),
    eventually_ge_atTop (2 : Real)] with x hApproxX hLarge hxTwo
  let L := Real.eulerMascheroniConstant + Real.log (Real.log (Chebyshev.theta x))
  let F := nicolasLogMertensOscillation x
  have hLTwo : 2 <= L := hApproxX.2.1
  have hLPos : 0 < L := by linarith
  have hxPos : 0 < x := by linarith
  change ((r0 : Real) + 2 * K + 1) / a <= L at hLarge
  refine And.intro hApproxX.1 (And.intro hLTwo ?_)
  intro r hLow hHigh
  have hRankLower : a * L <= (r : Real) := by
    calc
      _ <= ((r : Real) / L) * L := mul_le_mul_of_nonneg_right hLow hLPos.le
      _ = _ := by field_simp [hLPos.ne']
  have hRankLarge : (r0 : Real) + 2 * K + 1 <= (r : Real) := by
    calc
      _ = a * (((r0 : Real) + 2 * K + 1) / a) := by field_simp [ha.ne']
      _ <= a * L := mul_le_mul_of_nonneg_left hLarge ha.le
      _ <= _ := hRankLower
  have hRank0 : r0 <= r := by
    have hReal : (r0 : Real) <= r := by linarith
    exact_mod_cast hReal
  have hrReal : (0 : Real) < r := by exact_mod_cast hr0.trans_le hRank0
  have hReserve : 2 * K <= (r : Real) := by
    have hr0Nonneg : (0 : Real) <= r0 := Nat.cast_nonneg r0
    linarith
  have hRank := hApproxX.2.2 r hRank0 hHigh
  let D := (PrimeFactorUnimodality.densityRatio
    (PrimeFactorUnimodality.primesBelow (Nat.floor x + 1)) r : Real)
  let R := Nat.factorialConvolution primeProfileRealCoefficient (r - 1) L /
    Nat.factorialConvolution primeProfileRealCoefficient r L
  have hError : abs (D - R - ((r : Real) / L ^ 2) * F) <=
      K * (abs F / L ^ 2 + 1 / ((r : Real) * x)) := hRank.2.2
  have hCoefficient : a / 2 <= ((r : Real) - K) / L := by
    have hNumerator : a * L / 2 <= (r : Real) - K := by
      linarith only [hRankLower, hReserve]
    calc
      _ = (a * L / 2) / L := by field_simp [hLPos.ne']
      _ <= _ := div_le_div_of_nonneg_right hNumerator hLPos.le
  have hInverseRank : L / (r : Real) <= 1 / a := by
    have h := one_div_le_one_div_of_le (mul_pos ha hLPos) hRankLower
    have hScaled := mul_le_mul_of_nonneg_left h hLPos.le
    calc
      _ = L * (1 / (r : Real)) := by ring
      _ <= L * (1 / (a * L)) := hScaled
      _ = _ := by field_simp [hLPos.ne']
  have hTail : K * L / ((r : Real) * x) <= K / (a * x) := by
    have h := mul_le_mul_of_nonneg_left hInverseRank (div_nonneg hK hxPos.le)
    convert h using 1 <;> ring
  refine And.intro hRank.1 (And.intro hRank.2.1 (And.intro ?_ ?_))
  . intro hF
    change 0 <= F at hF
    change (a / 2) * F - K / (a * x) <= L * (D - R)
    have hLower := (abs_le.mp hError).1
    rw [abs_of_nonneg hF] at hLower
    have hBasic : (((r : Real) - K) / L ^ 2) * F -
        K / ((r : Real) * x) <= D - R := by
      have hExpand : (((r : Real) - K) / L ^ 2) * F -
          K / ((r : Real) * x) =
        ((r : Real) / L ^ 2) * F -
          K * (F / L ^ 2 + 1 / ((r : Real) * x)) := by ring
      rw [hExpand]
      linarith only [hLower]
    have hScaled : (((r : Real) - K) / L) * F -
        K * L / ((r : Real) * x) <= L * (D - R) := by
      have h := mul_le_mul_of_nonneg_left hBasic hLPos.le
      convert h using 1
      field_simp [hLPos.ne', hrReal.ne', hxPos.ne']
    have hSignal := mul_le_mul_of_nonneg_right hCoefficient hF
    linarith only [hScaled, hSignal, hTail]
  . intro hF
    change F <= 0 at hF
    change L * (D - R) <= (a / 2) * F + K / (a * x)
    have hUpper := (abs_le.mp hError).2
    rw [abs_of_nonpos hF] at hUpper
    have hBasic : D - R <= (((r : Real) - K) / L ^ 2) * F +
        K / ((r : Real) * x) := by
      have hExpand : (((r : Real) - K) / L ^ 2) * F +
          K / ((r : Real) * x) =
        ((r : Real) / L ^ 2) * F +
          K * (-F / L ^ 2 + 1 / ((r : Real) * x)) := by ring
      rw [hExpand]
      linarith only [hUpper]
    have hScaled : L * (D - R) <= (((r : Real) - K) / L) * F +
        K * L / ((r : Real) * x) := by
      have h := mul_le_mul_of_nonneg_left hBasic hLPos.le
      convert h using 1
      field_simp [hLPos.ne', hrReal.ne', hxPos.ne']
    have hSignal := mul_le_mul_of_nonpos_right hCoefficient hF
    linarith only [hScaled, hSignal, hTail]


/-- The prescribed floor rank lies in the positive band and inherits both
signed quantitative comparisons, with positive actual denominators. -/
theorem exists_eventually_floor_densityRatio_signed_margin
    (alpha : Real) (ha : 0 < alpha) :
    exists C : Real, 0 <= C /\ Filter.Eventually (fun x : Real =>
      let L := Real.eulerMascheroniConstant + Real.log (Real.log (Chebyshev.theta x))
      let F := nicolasLogMertensOscillation x
      let r := Nat.floor (alpha * L)
      let E := L * ((PrimeFactorUnimodality.densityRatio
          (PrimeFactorUnimodality.primesBelow (Nat.floor x + 1)) r : Real) -
        Nat.factorialConvolution primeProfileRealCoefficient (r - 1) L /
          Nat.factorialConvolution primeProfileRealCoefficient r L)
      1 < Chebyshev.theta x /\ 2 <= L /\
      0 < (PrimeFactorUnimodality.weightEsymm
        (PrimeFactorUnimodality.primesBelow (Nat.floor x + 1)) r : Real) /\
      0 < Nat.factorialConvolution primeProfileRealCoefficient r L /\
      (0 <= F -> (alpha / 4) * F - C / x <= E) /\
      (F <= 0 -> E <= (alpha / 4) * F + C / x)) atTop := by
  choose K hK hEvent using exists_eventually_densityRatio_signed_thetaClock_margin
    (alpha / 2) (alpha + 1) (by linarith) (by linarith)
  have hTheta : Tendsto Chebyshev.theta atTop atTop :=
    primeProfile_theta_isEquivalent_id.symm.tendsto_atTop tendsto_id
  have hClock : Tendsto (fun x : Real => Real.eulerMascheroniConstant +
      Real.log (Real.log (Chebyshev.theta x))) atTop atTop :=
    tendsto_const_nhds.add_atTop
      (Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp hTheta))
  refine Exists.intro (K / (alpha / 2)) (And.intro (by positivity) ?_)
  filter_upwards [hEvent, hClock.eventually_ge_atTop (2 / alpha)] with x hCompare hLarge
  let L := Real.eulerMascheroniConstant + Real.log (Real.log (Chebyshev.theta x))
  let r := Nat.floor (alpha * L)
  have hL : 2 <= L := hCompare.2.1
  have hLPos : 0 < L := by linarith
  have hAlphaL : 2 <= alpha * L := by
    calc
      _ = alpha * (2 / alpha) := by field_simp [ha.ne']
      _ <= _ := mul_le_mul_of_nonneg_left hLarge ha.le
  have hUpper : (r : Real) <= alpha * L := Nat.floor_le (by positivity)
  have hStrictLower : alpha * L < (r : Real) + 1 := Nat.lt_floor_add_one _
  have hNumerator : (alpha / 2) * L <= (r : Real) := by
    nlinarith only [hStrictLower, hAlphaL]
  have hLow : alpha / 2 <= (r : Real) / L := by
    calc
      _ = ((alpha / 2) * L) / L := by field_simp [hLPos.ne']
      _ <= _ := div_le_div_of_nonneg_right hNumerator hLPos.le
  have hHigh : (r : Real) / L <= alpha + 1 := by
    calc
      _ <= (alpha * L) / L := div_le_div_of_nonneg_right hUpper hLPos.le
      _ = alpha := by field_simp [hLPos.ne']
      _ <= _ := by linarith
  have hRank := hCompare.2.2 r hLow hHigh
  refine And.intro hCompare.1 (And.intro hL
    (And.intro hRank.1 (And.intro hRank.2.1 (And.intro ?_ ?_))))
  . intro hF
    have h := hRank.2.2.1 hF
    convert h using 1
    ring
  . intro hF
    have h := hRank.2.2.2 hF
    convert h using 1
    ring


/-- Both zero-dependent power excursions occur in the actual prescribed
moving-rank ratio, with its two positive denominators retained. -/
theorem densityRatio_thetaClock_two_sided_power_excursions_of_zero
    {rho : Complex} (hZero : riemannZeta rho = 0)
    (hHalf : (1 / 2 : Real) < rho.re) (hOne : rho.re < 1)
    {b : Real} (hLower : 1 - rho.re < b) (hbHalf : b <= 1 / 2)
    (alpha : Real) (ha : 0 < alpha) :
    let L : Real -> Real := fun x =>
      Real.eulerMascheroniConstant + Real.log (Real.log (Chebyshev.theta x))
    let r : Real -> Nat := fun x => Nat.floor (alpha * L x)
    let E : Real -> Real := fun x => L x *
      ((PrimeFactorUnimodality.densityRatio
        (PrimeFactorUnimodality.primesBelow (Nat.floor x + 1)) (r x) : Real) -
        Nat.factorialConvolution primeProfileRealCoefficient (r x - 1) (L x) /
          Nat.factorialConvolution primeProfileRealCoefficient (r x) (L x))
    let V : Real -> Prop := fun x =>
      1 < Chebyshev.theta x /\ 2 <= L x /\
      0 < (PrimeFactorUnimodality.weightEsymm
        (PrimeFactorUnimodality.primesBelow (Nat.floor x + 1)) (r x) : Real) /\
      0 < Nat.factorialConvolution primeProfileRealCoefficient (r x) (L x)
    forall X A : Real,
      (exists x : Real, max X 3 < x /\ V x /\ A * x ^ (-b) < E x) /\
      (exists x : Real, max X 3 < x /\ V x /\ A * x ^ (-b) < -E x) := by
  let L : Real -> Real := fun x =>
    Real.eulerMascheroniConstant + Real.log (Real.log (Chebyshev.theta x))
  let r : Real -> Nat := fun x => Nat.floor (alpha * L x)
  let E : Real -> Real := fun x => L x *
    ((PrimeFactorUnimodality.densityRatio
      (PrimeFactorUnimodality.primesBelow (Nat.floor x + 1)) (r x) : Real) -
      Nat.factorialConvolution primeProfileRealCoefficient (r x - 1) (L x) /
        Nat.factorialConvolution primeProfileRealCoefficient (r x) (L x))
  let V : Real -> Prop := fun x =>
    1 < Chebyshev.theta x /\ 2 <= L x /\
    0 < (PrimeFactorUnimodality.weightEsymm
      (PrimeFactorUnimodality.primesBelow (Nat.floor x + 1)) (r x) : Real) /\
    0 < Nat.factorialConvolution primeProfileRealCoefficient (r x) (L x)
  change forall X A : Real,
    (exists x : Real, max X 3 < x /\ V x /\ A * x ^ (-b) < E x) /\
    (exists x : Real, max X 3 < x /\ V x /\ A * x ^ (-b) < -E x)
  choose C hC hEvent using exists_eventually_floor_densityRatio_signed_margin alpha ha
  have hSmall := ((rpow_neg_one_isLittleO_rpow_neg (by linarith : b < 1)).const_mul_left C).bound
    (by norm_num : (0 : Real) < 1)
  choose Y hY using eventually_atTop.mp
    (hEvent.and (hSmall.and (eventually_gt_atTop (1 : Real))))
  have hAt (x : Real) (hx : Y <= x) :
      V x /\ C / x <= x ^ (-b) /\
      (0 <= nicolasLogMertensOscillation x ->
        (alpha / 4) * nicolasLogMertensOscillation x - C / x <= E x) /\
      (nicolasLogMertensOscillation x <= 0 ->
        E x <= (alpha / 4) * nicolasLogMertensOscillation x + C / x) := by
    have hAll := hY x hx
    have hCompare := hAll.1
    have hxPos : 0 < x := by linarith only [hAll.2.2]
    have hError := hAll.2.1
    change norm (C * x ^ (-(1 : Real))) <= 1 * norm (x ^ (-b)) at hError
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg hC (Real.rpow_nonneg hxPos.le _)),
      abs_of_pos (Real.rpow_pos_of_pos hxPos (-b)), one_mul,
      Real.rpow_neg_one] at hError
    have hBound : C / x <= x ^ (-b) := by simpa only [div_eq_mul_inv] using hError
    refine And.intro
      (And.intro hCompare.1 (And.intro hCompare.2.1
        (And.intro hCompare.2.2.1 hCompare.2.2.2.1)))
      (And.intro hBound (And.intro ?_ ?_))
    . exact hCompare.2.2.2.2.1
    . exact hCompare.2.2.2.2.2
  intro X A
  let M : Real := 4 * (max A 0 + 2) / alpha
  have hM : 0 < M := by
    dsimp [M]
    have h := le_max_right A 0
    positivity
  have hSource := nicolasLog_two_sided_power_excursions_of_zero hZero hHalf hOne hLower hbHalf
    (max X Y) M
  have hFactor (x : Real) :
      (alpha / 4) * (M * x ^ (-b)) = (max A 0 + 2) * x ^ (-b) := by
    dsimp [M]
    field_simp [ha.ne']
  constructor
  . choose x hx hValue using hSource.1
    have hxThree : 3 < x := (le_max_right _ _).trans_lt hx
    have hxPos : 0 < x := by linarith
    have hxY : Y <= x := (le_max_right X Y).trans ((le_max_left _ _).trans hx.le)
    have hxX : X < x := ((le_max_left X Y).trans (le_max_left _ _)).trans_lt hx
    have hData := hAt x hxY
    have hPower : 0 < x ^ (-b) := Real.rpow_pos_of_pos hxPos _
    have hF : 0 <= nicolasLogMertensOscillation x := ((mul_pos hM hPower).trans hValue).le
    have hSignal := mul_lt_mul_of_pos_left hValue (by linarith : 0 < alpha / 4)
    rw [hFactor] at hSignal
    have hMargin := hData.2.2.1 hF
    have hReserve := mul_le_mul_of_nonneg_right (le_max_left A 0) hPower.le
    refine Exists.intro x (And.intro (max_lt hxX hxThree) (And.intro hData.1 ?_))
    nlinarith only [hSignal, hMargin, hData.2.1, hReserve, hPower]
  . choose x hx hValue using hSource.2
    have hxThree : 3 < x := (le_max_right _ _).trans_lt hx
    have hxPos : 0 < x := by linarith
    have hxY : Y <= x := (le_max_right X Y).trans ((le_max_left _ _).trans hx.le)
    have hxX : X < x := ((le_max_left X Y).trans (le_max_left _ _)).trans_lt hx
    have hData := hAt x hxY
    have hPower : 0 < x ^ (-b) := Real.rpow_pos_of_pos hxPos _
    have hNegative : 0 < -nicolasLogMertensOscillation x := (mul_pos hM hPower).trans hValue
    have hF : nicolasLogMertensOscillation x <= 0 := by linarith only [hNegative]
    have hSignal := mul_lt_mul_of_pos_left hValue (by linarith : 0 < alpha / 4)
    rw [hFactor] at hSignal
    have hMargin := hData.2.2.2 hF
    have hReserve := mul_le_mul_of_nonneg_right (le_max_left A 0) hPower.le
    refine Exists.intro x (And.intro (max_lt hxX hxThree) (And.intro hData.1 ?_))
    nlinarith only [hSignal, hMargin, hData.2.1, hReserve, hPower]

end PrimeFactorOscillations

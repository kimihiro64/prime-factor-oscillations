/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.NicolasDegreeLocalization
import PrimeFactorOscillations.Helpers.NicolasLogDegreeMoment

/-!
# Squared-logarithmic RH localization

The exact weighted psi integral retains its complete zero sum and correction.
A uniform squared-logarithmic degree coefficient controls both endpoints of a
short multiplicative band. Choosing the degree just above the square root of
the endpoint gives the classical RH square-root, squared-logarithm estimates
for psi and theta. RH remains an explicit hypothesis throughout.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

open Robin1984

private theorem norm_nicolasLogDegreeZeroKernel_le (hRH : RiemannHypothesis)
    {n : Nat} (hn : 2 <= n) {x : Real} (hx : 1 < x) (hL : 1 <= Real.log x)
    (p : RiemannXiDivisorZeroIndex) :
    norm (robinZeroKernel n (riemannXiDivisorZeroValue p) x /
        riemannXiDivisorZeroValue p) <=
      (norm (((n : Complex) / ((n : Complex) - riemannXiDivisorZeroValue p)) /
        riemannXiDivisorZeroValue p) +
        5 * (Inv.inv (norm (riemannXiDivisorZeroValue p))) ^ (2 : Nat)) *
      (x ^ ((1 / 2 : Real) - n) * Inv.inv (Real.log x)) := by
  let rho := riemannXiDivisorZeroValue p
  have hRe : rho.re = (1 / 2 : Real) :=
    riemannXiDivisorZeroValue_re_eq_half_of_riemannHypothesis hRH p
  have hnReal : (2 : Real) <= n := by exact_mod_cast hn
  have hReLt : rho.re < n := by rw [hRe]; linarith
  have hNorm :
      norm ((x : Complex) ^ (rho - (n : Complex)) *
        ((Inv.inv (Real.log x) : Real) : Complex)) =
      x ^ ((1 / 2 : Real) - n) * Inv.inv (Real.log x) := by
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (by linarith : 0 < x),
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (Real.log_pos hx))]
    simp only [Complex.sub_re, Complex.natCast_re, hRe]
  have hRem := norm_robinZeroKernelRemainder_div_rho_le (by omega : 1 <= n)
    (riemannXiDivisorZeroValue_ne_zero p) hRe hx
  have hRemScalar := mul_le_mul_of_nonneg_left (nicolasDegreeRemainderScalar_le hn hx hL)
    (sq_nonneg (Inv.inv (norm rho)))
  change norm (robinZeroKernel n rho x / rho) <= _
  rw [robinZeroKernel_eq_main_add_remainder (by omega) hx hReLt, add_div]
  have hRewrite :
      ((n : Complex) / ((n : Complex) - rho) *
        (x : Complex) ^ (rho - (n : Complex)) *
          ((Inv.inv (Real.log x) : Real) : Complex)) / rho =
      (((n : Complex) / ((n : Complex) - rho)) / rho) *
        ((x : Complex) ^ (rho - (n : Complex)) *
          ((Inv.inv (Real.log x) : Real) : Complex)) := by ring
  rw [hRewrite]
  have hTriangle := norm_add_le
    ((((n : Complex) / ((n : Complex) - rho)) / rho) *
      ((x : Complex) ^ (rho - (n : Complex)) *
        ((Inv.inv (Real.log x) : Real) : Complex)))
    (robinZeroKernelRemainder n rho x / rho)
  rw [norm_mul, hNorm] at hTriangle
  dsimp only [rho] at hTriangle hRemScalar
  nlinarith only [hTriangle, hRem, hRemScalar]


/-- The exact weighted psi error has the squared-logarithmic degree allowance. -/
theorem exists_nicolasLogDegreeError_le_mass (hRH : RiemannHypothesis) :
    Exists fun D : Real => And (0 < D) (forall n : Nat, 2 <= n ->
      forall x : Real, 2 <= x -> 1 <= Real.log x ->
        abs (robinPsiWeightedErrorIntegral n x) <=
          D * (Real.log ((n : Real) + 2)) ^ (2 : Nat) *
            Real.sqrt x * nicolasDegreeMass n x) := by
  choose C hC hCoefficient using exists_nicolasZeroCoefficient_log_bound hRH
  let B : Real := 5 * (Real.eulerMascheroniConstant + 2 - Real.log (4 * Real.pi)) +
    Real.log (2 * Real.pi)
  let D : Real := C + (abs B + 1) / (Real.log 2) ^ (2 : Nat)
  have hLog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hD : 0 < D := by dsimp [D]; positivity
  refine Exists.intro D (And.intro hD ?_)
  intro n hn x hx hL
  have hx1 : 1 < x := by linarith
  have hxPos : 0 < x := by linarith
  let F : Real := x ^ ((1 / 2 : Real) - n) * Inv.inv (Real.log x)
  have hF : 0 <= F := by dsimp [F]; positivity
  have hCoefficientSum : Summable (fun p : RiemannXiDivisorZeroIndex =>
      norm (((n : Complex) / ((n : Complex) - riemannXiDivisorZeroValue p)) /
        riemannXiDivisorZeroValue p)) := by
    apply (summable_nicolasThreeHalfZeroWeight.mul_left
      (2 * Real.sqrt (n : Real))).of_nonneg_of_le (fun p => norm_nonneg _)
    intro p
    exact norm_nicolasZeroCoefficient_le_sqrt_degree hRH hn p
  have hSeries := summable_robinZeroKernel_div_rho hRH (by omega : 1 <= n) hx1
  have hMajor := (hCoefficientSum.add
    (summable_robinXiZeroWeight.mul_left 5)).mul_right F
  have hSum :
      norm (tsum (fun p : RiemannXiDivisorZeroIndex =>
        robinZeroKernel n (riemannXiDivisorZeroValue p) x / riemannXiDivisorZeroValue p)) <=
      (C * (Real.log ((n : Real) + 2)) ^ (2 : Nat) +
        5 * (Real.eulerMascheroniConstant + 2 - Real.log (4 * Real.pi))) * F := by
    calc
      _ <= tsum (fun p : RiemannXiDivisorZeroIndex =>
          norm (robinZeroKernel n (riemannXiDivisorZeroValue p) x /
            riemannXiDivisorZeroValue p)) := norm_tsum_le_tsum_norm hSeries.norm
      _ <= tsum (fun p : RiemannXiDivisorZeroIndex =>
          (norm (((n : Complex) / ((n : Complex) - riemannXiDivisorZeroValue p)) /
            riemannXiDivisorZeroValue p) +
              5 * (Inv.inv (norm (riemannXiDivisorZeroValue p))) ^ (2 : Nat)) * F) :=
        hSeries.norm.tsum_le_tsum
          (fun p => norm_nicolasLogDegreeZeroKernel_le hRH hn hx1 hL p) hMajor
      _ = (tsum (fun p : RiemannXiDivisorZeroIndex =>
          norm (((n : Complex) / ((n : Complex) - riemannXiDivisorZeroValue p)) /
            riemannXiDivisorZeroValue p)) +
          5 * (Real.eulerMascheroniConstant + 2 - Real.log (4 * Real.pi))) * F := by
        rw [tsum_mul_right, Summable.tsum_add hCoefficientSum
          (summable_robinXiZeroWeight.mul_left 5), tsum_mul_left,
          robinXiZeroConstant_eq_of_riemannHypothesis hRH]
      _ <= _ := mul_le_mul_of_nonneg_right
        (by linarith only [hCoefficient n hn]) hF
  have hTrivial := robinTrivialZeroCorrection_bounds (by omega : 1 <= n) hx
  have hFormula := robinPsiWeightedErrorIntegral_eq_zero_sum_correction hRH hn hx
  have hAbs : abs (robinPsiWeightedErrorIntegral n x) <=
      norm (tsum (fun p : RiemannXiDivisorZeroIndex =>
        robinZeroKernel n (riemannXiDivisorZeroValue p) x / riemannXiDivisorZeroValue p)) +
          robinTrivialZeroCorrection n x := by
    have hTriangle := norm_sub_le
      (-tsum (fun p : RiemannXiDivisorZeroIndex =>
        robinZeroKernel n (riemannXiDivisorZeroValue p) x / riemannXiDivisorZeroValue p))
      (robinTrivialZeroCorrection n x : Complex)
    rw [<- hFormula, norm_neg, Complex.norm_real, Real.norm_eq_abs,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hTrivial.1] at hTriangle
    exact hTriangle
  have hLogPi : 0 <= Real.log (2 * Real.pi) :=
    Real.log_nonneg (by nlinarith [Real.pi_gt_three])
  have hPower : x ^ (-(n : Real)) <= x ^ ((1 / 2 : Real) - n) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  have hCorrection := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hPower hLogPi) (inv_nonneg.mpr (Real.log_pos hx1).le)
  have hTrivialBound : robinTrivialZeroCorrection n x <= Real.log (2 * Real.pi) * F := by
    calc
      _ <= Real.log (2 * Real.pi) * x ^ (-(n : Real)) * Inv.inv (Real.log x) :=
        hTrivial.2
      _ <= Real.log (2 * Real.pi) * x ^ ((1 / 2 : Real) - n) *
          Inv.inv (Real.log x) := hCorrection
      _ = _ := by dsimp [F]; ring
  have hBefore : abs (robinPsiWeightedErrorIntegral n x) <=
      (C * (Real.log ((n : Real) + 2)) ^ (2 : Nat) + B) * F := by
    dsimp [B]
    nlinarith only [hAbs, hSum, hTrivialBound]
  have hLogN : Real.log 2 <= Real.log ((n : Real) + 2) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast (show 2 <= n + 2 by omega))
  have hLogN0 : 0 <= Real.log ((n : Real) + 2) := hLog2.le.trans hLogN
  have hSquare : (Real.log 2) ^ (2 : Nat) <=
      (Real.log ((n : Real) + 2)) ^ (2 : Nat) := by
    have h := mul_nonneg (sub_nonneg.mpr hLogN)
      (add_nonneg hLogN0 hLog2.le)
    nlinarith only [h]
  have hReserve := mul_le_mul_of_nonneg_left hSquare
    (show 0 <= (abs B + 1) / (Real.log 2) ^ (2 : Nat) by positivity)
  have hPaid : (abs B + 1) / (Real.log 2) ^ (2 : Nat) *
      (Real.log 2) ^ (2 : Nat) = abs B + 1 := by field_simp [hLog2.ne']
  rw [hPaid] at hReserve
  have hAllowance : C * (Real.log ((n : Real) + 2)) ^ (2 : Nat) + B <=
      D * (Real.log ((n : Real) + 2)) ^ (2 : Nat) := by
    dsimp [D]
    nlinarith only [hReserve, le_abs_self B]
  have hFinal := hBefore.trans (mul_le_mul_of_nonneg_right hAllowance hF)
  have hFactor : F = Real.sqrt x * nicolasDegreeMass n x := by
    dsimp [F, nicolasDegreeMass]
    rw [Real.sqrt_eq_rpow, <- mul_assoc, <- Real.rpow_add hxPos]
    congr 2
  calc
    _ <= D * (Real.log ((n : Real) + 2)) ^ (2 : Nat) * F := hFinal
    _ = _ := by rw [hFactor]; ring

private theorem nicolasLogDegree_band_pointwise_bounds
    {n : Nat} (hn : 2 <= n) (D : Real) (hD : 0 <= D)
    (hError : forall y : Real, 2 <= y -> 1 <= Real.log y ->
      abs (robinPsiWeightedErrorIntegral n y) <=
        D * Real.sqrt y * nicolasDegreeMass n y) {a b : Real} (ha : 2 <= a) (hL : 1 <= Real.log a)
    (hab : a <= b) (hPower : 2 * a ^ n <= b ^ n) :
    Chebyshev.psi a <= b +
        3 * D * Real.sqrt b /\
    a - 3 * D * Real.sqrt b <=
      Chebyshev.psi b := by
  let T := D * Real.sqrt b
  let ma := nicolasDegreeMass n a
  let mb := nicolasDegreeMass n b
  have ha1 : 1 < a := by linarith
  have hb : 2 <= b := ha.trans hab
  have hb1 : 1 < b := ha1.trans_le hab
  have hLb : 1 <= Real.log b := hL.trans (Real.log_le_log (by linarith) hab)
  have hma : 0 < ma := nicolasDegreeMass_pos n ha1
  have hmb : 0 < mb := nicolasDegreeMass_pos n hb1
  have hhalf : mb <= ma / 2 := nicolasDegreeMass_halving ha1 hab hPower
  have hR : 0 < ma - mb := by linarith
  have hT : 0 <= T := by dsimp [T]; positivity
  have hA0 := hError a ha hL
  have hB : abs (robinPsiWeightedErrorIntegral n b) <= T * mb :=
    hError b hb hLb
  have hA : abs (robinPsiWeightedErrorIntegral n a) <= T * ma := by
    have h := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hab)
        hD) hma.le
    exact hA0.trans h
  have hBand := nicolasDegreeError_band_sandwich hn ha1 hab
  change (Chebyshev.psi a - b) * (ma - mb) <= _ /\
    _ <= (Chebyshev.psi b - a) * (ma - mb) at hBand
  have hPlus : ma + mb <= 3 * (ma - mb) := by linarith
  have hAllowance := mul_le_mul_of_nonneg_left hPlus hT
  have hLower : -(3 * T) * (ma - mb) <=
      robinPsiWeightedErrorIntegral n a - robinPsiWeightedErrorIntegral n b := by
    have hAe := (abs_le.mp hA).1
    have hBe := (abs_le.mp hB).2
    nlinarith only [hAe, hBe, hAllowance]
  have hUpper : robinPsiWeightedErrorIntegral n a - robinPsiWeightedErrorIntegral n b <=
      (3 * T) * (ma - mb) := by
    have hAe := (abs_le.mp hA).2
    have hBe := (abs_le.mp hB).1
    nlinarith only [hAe, hBe, hAllowance]
  have hLeft := le_of_mul_le_mul_right (hBand.1.trans hUpper) hR
  have hRight := le_of_mul_le_mul_right (hLower.trans hBand.2) hR
  dsimp [T] at hLeft hRight
  constructor <;> linarith only [hLeft, hRight]

private theorem abs_nicolasPsiError_le_logDegree
    {n : Nat} (hn : 2 <= n) (D : Real) (hD : 0 <= D)
    (hError : forall y : Real, 2 <= y -> 1 <= Real.log y ->
      abs (robinPsiWeightedErrorIntegral n y) <=
        D * Real.sqrt y * nicolasDegreeMass n y) {x : Real} (hx : 4 <= x)
    (hL : 1 <= Real.log (x / 2)) :
    abs (Chebyshev.psi x - x) <= x / ((n : Real) - 1) +
      6 * D * Real.sqrt x := by
  let a := x * ((n : Real) - 1) / (n : Real)
  let b := x * (n : Real) / ((n : Real) - 1)
  have hN : (2 : Real) <= n := by exact_mod_cast hn
  have hNp : (0 : Real) < n := by linarith
  have hd : 0 < (n : Real) - 1 := by linarith
  have hxPos : 0 < x := by linarith
  have haEq : a * (n : Real) = x * ((n : Real) - 1) := by
    dsimp [a]
    field_simp
  have hbEq : b * ((n : Real) - 1) = x * (n : Real) := by
    dsimp [b]
    field_simp
  have haHalf : x / 2 <= a := by
    have h := mul_nonneg hxPos.le (sub_nonneg.mpr hN)
    have hprod : x / 2 * (n : Real) <= a * (n : Real) := by
      nlinarith only [haEq, h]
    exact le_of_mul_le_mul_right hprod hNp
  have hax : a <= x := by
    have hprod : a * (n : Real) <= x * (n : Real) := by
      nlinarith only [haEq, hxPos]
    exact le_of_mul_le_mul_right hprod hNp
  have hxb : x <= b := by
    have hprod : x * ((n : Real) - 1) <= b * ((n : Real) - 1) := by
      nlinarith only [hbEq, hxPos]
    exact le_of_mul_le_mul_right hprod hd
  have hbx : b <= 2 * x := by
    have h := mul_nonneg hxPos.le (sub_nonneg.mpr hN)
    have hprod : b * ((n : Real) - 1) <= (2 * x) * ((n : Real) - 1) := by
      nlinarith only [hbEq, h]
    exact le_of_mul_le_mul_right hprod hd
  have ha2 : 2 <= a := by linarith
  have hLa : 1 <= Real.log a :=
    hL.trans (Real.log_le_log (by positivity) haHalf)
  have hLx : 1 <= Real.log x :=
    hL.trans (Real.log_le_log (by positivity) (by linarith : x / 2 <= x))
  have hScaledA : a * (n : Real) / ((n : Real) - 1) = x := by
    rw [haEq]
    field_simp
  have hLower := (nicolasLogDegree_band_pointwise_bounds hn D hD hError ha2 hLa hax
    (by simpa only [hScaledA] using nicolasDegree_dilation_power hn (by linarith : 0 <= a))).2
  have hUpper := (nicolasLogDegree_band_pointwise_bounds hn D hD hError (by linarith : 2 <= x)
    hLx hxb (nicolasDegree_dilation_power hn hxPos.le)).1
  have hSqrt : Real.sqrt b <= 2 * Real.sqrt x := by
    have hbp : 0 <= b := hxPos.le.trans hxb
    nlinarith only [Real.sq_sqrt hbp, Real.sq_sqrt hxPos.le,
      Real.sqrt_nonneg b, Real.sqrt_nonneg x, hbx, hxPos]
  have hScaledRoot := mul_le_mul_of_nonneg_left hSqrt
    (show 0 <= 3 * D by positivity)
  have hDiffA : x - a = x / (n : Real) := by
    dsimp [a]
    field_simp
    ring
  have hDiffB : b - x = x / ((n : Real) - 1) := by
    dsimp [b]
    field_simp
    ring
  have hInv := one_div_le_one_div_of_le hd (show (n : Real) - 1 <= n by linarith)
  have hFractions : x / (n : Real) <= x / ((n : Real) - 1) := by
    simpa only [div_eq_mul_inv, one_mul] using mul_le_mul_of_nonneg_left hInv hxPos.le
  have hRootNonneg : 0 <= D * Real.sqrt x := by positivity
  change abs (Chebyshev.psi x - x) <= x / ((n : Real) - 1) +
    6 * D * Real.sqrt x
  change a - 3 * D * Real.sqrt x <= Chebyshev.psi x at hLower
  change Chebyshev.psi x <= b + 3 * D * Real.sqrt b at hUpper
  apply abs_le.mpr
  constructor <;> nlinarith only [hLower, hUpper, hScaledRoot, hDiffA, hDiffB,
    hFractions, hRootNonneg]


/-- The classical RH square-root, squared-logarithm bound from the exact
weighted integral, with one constant for every admissible endpoint. -/
theorem exists_nicolasPsiError_le_sqrt_log_sq (hRH : RiemannHypothesis) :
    Exists fun C : Real => And (0 < C) (forall x : Real, 4 <= x ->
      1 <= Real.log (x / 2) ->
      abs (Chebyshev.psi x - x) <=
        C * Real.sqrt x * (Real.log x) ^ (2 : Nat)) := by
  choose D hD hError using exists_nicolasLogDegreeError_le_mass hRH
  let A : Real := Real.log 5 + 1 / 2
  let C : Real := 1 + 6 * D * A ^ (2 : Nat)
  have hA : 0 < A := by
    dsimp [A]
    have h := Real.log_pos (by norm_num : (1 : Real) < 5)
    linarith
  have hC : 0 < C := by dsimp [C]; positivity
  refine Exists.intro C (And.intro hC ?_)
  intro x hx hL
  let q : Real := Real.sqrt x
  let n : Nat := Nat.ceil q + 1
  have hxPos : 0 < x := by linarith
  have hqPos : 0 < q := Real.sqrt_pos.mpr hxPos
  have hqSq : q ^ (2 : Nat) = x := Real.sq_sqrt hxPos.le
  have hq1 : 1 <= q := by
    dsimp [q]
    exact (Real.le_sqrt (by norm_num) hxPos.le).mpr (by linarith)
  have hceil : q <= (Nat.ceil q : Real) := Nat.le_ceil q
  have hceilHi : (Nat.ceil q : Real) < q + 1 := Nat.ceil_lt_add_one hqPos.le
  have hn : 2 <= n := by
    have h1 : (1 : Real) <= (Nat.ceil q : Real) := hq1.trans hceil
    have h1n : 1 <= Nat.ceil q := by exact_mod_cast h1
    dsimp [n]
    omega
  have hnEq : (n : Real) = (Nat.ceil q : Real) + 1 := by
    dsimp [n]
    norm_cast
  have hnLower : q <= (n : Real) - 1 := by linarith only [hceil, hnEq]
  have hnUpper : (n : Real) + 2 <= 5 * q := by
    linarith only [hceilHi, hnEq, hq1]
  have hFirst : x / ((n : Real) - 1) <= q := by
    have hd : 0 < (n : Real) - 1 := by linarith
    have hprod : x <= q * ((n : Real) - 1) := by
      nlinarith only [mul_le_mul_of_nonneg_left hnLower hqPos.le, hqSq]
    calc
      _ <= (q * ((n : Real) - 1)) / ((n : Real) - 1) :=
        div_le_div_of_nonneg_right hprod hd.le
      _ = q := by field_simp
  have hLx : 1 <= Real.log x :=
    hL.trans (Real.log_le_log (by positivity) (by linarith : x / 2 <= x))
  have hLogN0 : 0 <= Real.log ((n : Real) + 2) :=
    Real.log_nonneg (by
      have hN : (2 : Real) <= n := by exact_mod_cast hn
      linarith)
  have hLogRoot : Real.log q = Real.log x / 2 := by
    dsimp [q]
    rw [Real.sqrt_eq_rpow, Real.log_rpow hxPos]
    ring
  have hLogN : Real.log ((n : Real) + 2) <= A * Real.log x := by
    have h1 := Real.log_le_log (by positivity : 0 < (n : Real) + 2) hnUpper
    rw [Real.log_mul (by norm_num : Not ((5 : Real) = 0)) hqPos.ne',
      hLogRoot] at h1
    have h2 := mul_le_mul_of_nonneg_left hLx
      (Real.log_nonneg (by norm_num : (1 : Real) <= 5))
    dsimp [A]
    nlinarith only [h1, h2]
  have hSquare : (Real.log ((n : Real) + 2)) ^ (2 : Nat) <=
      A ^ (2 : Nat) * (Real.log x) ^ (2 : Nat) := by
    have h := mul_nonneg (sub_nonneg.mpr hLogN)
      (add_nonneg (mul_nonneg hA.le (by linarith : 0 <= Real.log x)) hLogN0)
    nlinarith only [h]
  have h := abs_nicolasPsiError_le_logDegree hn
    (D * (Real.log ((n : Real) + 2)) ^ (2 : Nat)) (by positivity)
    (hError n hn) hx hL
  have hScaled := mul_le_mul_of_nonneg_left hSquare
    (show 0 <= 6 * D * q by positivity)
  have hOne : q <= q * (Real.log x) ^ (2 : Nat) := by
    have h := mul_nonneg hqPos.le (show 0 <= (Real.log x) ^ (2 : Nat) - 1 by nlinarith)
    nlinarith only [h]
  change abs (Chebyshev.psi x - x) <= C * q * (Real.log x) ^ (2 : Nat)
  dsimp [C]
  change abs (Chebyshev.psi x - x) <= x / ((n : Real) - 1) +
    6 * (D * (Real.log ((n : Real) + 2)) ^ (2 : Nat)) * q at h
  nlinarith only [h, hFirst, hScaled, hOne]

/-- The same RH bound for theta, retaining the prime-power correction. -/
theorem exists_nicolasThetaError_le_sqrt_log_sq (hRH : RiemannHypothesis) :
    Exists fun C : Real => And (0 < C) (forall x : Real, 4 <= x ->
      1 <= Real.log (x / 2) ->
      abs (Chebyshev.theta x - x) <=
        C * Real.sqrt x * (Real.log x) ^ (2 : Nat)) := by
  choose C hC hPsi using exists_nicolasPsiError_le_sqrt_log_sq hRH
  refine Exists.intro (C + 2) (And.intro (by linarith) ?_)
  intro x hx hL
  have hLx : 1 <= Real.log x :=
    hL.trans (Real.log_le_log (by positivity) (by linarith : x / 2 <= x))
  have hDiff := Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log (by linarith : 1 <= x)
  have hLogTerm : 2 * Real.sqrt x * Real.log x <=
      2 * Real.sqrt x * (Real.log x) ^ (2 : Nat) := by
    exact mul_le_mul_of_nonneg_left (by nlinarith) (by positivity)
  have hTriangle := abs_sub_le (Chebyshev.theta x) (Chebyshev.psi x) x
  rw [abs_sub_comm (Chebyshev.theta x) (Chebyshev.psi x)] at hTriangle
  nlinarith only [hPsi x hx hL, hDiff, hLogTerm, hTriangle]

end PrimeFactorOscillations

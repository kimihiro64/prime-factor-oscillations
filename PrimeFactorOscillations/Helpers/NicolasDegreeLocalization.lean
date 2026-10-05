/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.NicolasDegreeMoment

/-!
# Localization of the weighted Chebyshev error

Exact finite-band identities retain both tail endpoints. Monotonicity of psi
then converts a uniform weighted estimate into pointwise control.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

open MeasureTheory Set Robin1984

def nicolasDegreeMass (n : Nat) (x : Real) : Real :=
  x ^ (-(n : Real)) * Inv.inv (Real.log x)

theorem nicolasDegreeError_sub_eq_band
    {n : Nat} (hn : 2 <= n) {a b : Real} (ha : 1 < a) (hab : a <= b) :
    robinPsiWeightedErrorIntegral n a - robinPsiWeightedErrorIntegral n b =
      integral (volume.restrict (Ioc a b))
        (fun t : Real => (Chebyshev.psi t - t) * robinRealWeight n t) := by
  unfold robinPsiWeightedErrorIntegral
  rw [intervalIntegral.integral_Ioi_sub_Ioi (integrableOn_robinPsiWeightedError hn ha) hab,
    intervalIntegral.integral_of_le hab]

theorem nicolasDegreeMass_sub_eq_band
    {n : Nat} (hn : 1 <= n) {a b : Real} (ha : 1 < a) (hab : a <= b) :
    nicolasDegreeMass n a - nicolasDegreeMass n b =
      integral (volume.restrict (Ioc a b)) (robinRealWeight n) := by
  rw [nicolasDegreeMass, nicolasDegreeMass,
    <- integral_robinRealWeight hn ha,
    <- integral_robinRealWeight hn (ha.trans_le hab),
    intervalIntegral.integral_Ioi_sub_Ioi (integrableOn_robinRealWeight hn ha) hab,
    intervalIntegral.integral_of_le hab]

theorem nicolasDegreeError_band_sandwich
    {n : Nat} (hn : 2 <= n) {a b : Real} (ha : 1 < a) (hab : a <= b) :
    (Chebyshev.psi a - b) * (nicolasDegreeMass n a - nicolasDegreeMass n b) <=
        robinPsiWeightedErrorIntegral n a - robinPsiWeightedErrorIntegral n b /\
    robinPsiWeightedErrorIntegral n a - robinPsiWeightedErrorIntegral n b <=
      (Chebyshev.psi b - a) * (nicolasDegreeMass n a - nicolasDegreeMass n b) := by
  rw [nicolasDegreeError_sub_eq_band hn ha hab,
    nicolasDegreeMass_sub_eq_band (by omega : 1 <= n) ha hab]
  have hSubset : Ioc a b <= Ioi a := fun t ht => ht.1
  have hW := (integrableOn_robinRealWeight (by omega : 1 <= n) ha).mono_set hSubset
  have hE := (integrableOn_robinPsiWeightedError hn ha).mono_set hSubset
  constructor
  . rw [<- integral_const_mul]
    apply integral_mono_ae (hW.const_mul _) hE
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact mul_le_mul_of_nonneg_right
      (sub_le_sub (Chebyshev.psi_mono ht.1.le) ht.2)
      (robinRealWeight_nonneg (ha.trans ht.1))
  . rw [<- integral_const_mul]
    apply integral_mono_ae hE (hW.const_mul _)
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact mul_le_mul_of_nonneg_right
      (sub_le_sub (Chebyshev.psi_mono ht.2) ht.1.le)
      (robinRealWeight_nonneg (ha.trans ht.1))

theorem nicolasDegreeMass_pos (n : Nat) {x : Real} (hx : 1 < x) :
    0 < nicolasDegreeMass n x := by
  unfold nicolasDegreeMass
  exact mul_pos (Real.rpow_pos_of_pos (by linarith) _)
    (inv_pos.mpr (Real.log_pos hx))

theorem nicolasDegreeMass_eq_inv (n : Nat) {x : Real} (hx : 0 < x) :
    nicolasDegreeMass n x = Inv.inv (x ^ n * Real.log x) := by
  unfold nicolasDegreeMass
  rw [Real.rpow_neg hx.le, Real.rpow_natCast, mul_inv_rev]
  ring

theorem nicolasDegreeMass_halving
    {n : Nat} {a b : Real} (ha : 1 < a) (hab : a <= b)
    (hPower : 2 * a ^ n <= b ^ n) :
    nicolasDegreeMass n b <= nicolasDegreeMass n a / 2 := by
  have hb : 1 < b := ha.trans_le hab
  have hA : 0 < a ^ n * Real.log a :=
    mul_pos (pow_pos (by linarith) n) (Real.log_pos ha)
  have hprod : 2 * (a ^ n * Real.log a) <= b ^ n * Real.log b := by
    have h := mul_le_mul hPower (Real.log_le_log (by linarith) hab)
      (Real.log_pos ha).le (by positivity : 0 <= b ^ n)
    nlinarith only [h]
  have hInv := one_div_le_one_div_of_le (mul_pos (by norm_num) hA) hprod
  rw [nicolasDegreeMass_eq_inv n (by linarith), nicolasDegreeMass_eq_inv n (by linarith)]
  convert hInv using 1 <;> field_simp

theorem abs_nicolasDegreeError_le_mass (hRH : RiemannHypothesis)
    {n : Nat} (hn : 2 <= n) {x : Real} (hx : 2 <= x) (hL : 1 <= Real.log x) :
    abs (robinPsiWeightedErrorIntegral n x) <=
      (abs nicolasDegreeErrorConstant + 1) * Real.sqrt (n : Real) *
        Real.sqrt x * nicolasDegreeMass n x := by
  have hxPos : 0 < x := by linarith
  have h := abs_nicolasDegreeError_le hRH hn hx hL
  have hfactor : x ^ ((1 / 2 : Real) - n) * Inv.inv (Real.log x) =
      Real.sqrt x * nicolasDegreeMass n x := by
    unfold nicolasDegreeMass
    rw [Real.sqrt_eq_rpow, <- mul_assoc, <- Real.rpow_add hxPos]
    congr 2
  rw [hfactor] at h
  have hC : nicolasDegreeErrorConstant <= abs nicolasDegreeErrorConstant + 1 := by
    linarith only [le_abs_self nicolasDegreeErrorConstant]
  have hNonneg : 0 <= Real.sqrt (n : Real) * (Real.sqrt x * nicolasDegreeMass n x) :=
    mul_nonneg (Real.sqrt_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (nicolasDegreeMass_pos n (by linarith)).le)
  have hCompare := mul_le_mul_of_nonneg_right hC hNonneg
  nlinarith only [h, hCompare]


theorem nicolasDegree_band_pointwise_bounds (hRH : RiemannHypothesis)
    {n : Nat} (hn : 2 <= n) {a b : Real} (ha : 2 <= a) (hL : 1 <= Real.log a)
    (hab : a <= b) (hPower : 2 * a ^ n <= b ^ n) :
    Chebyshev.psi a <= b +
        3 * (abs nicolasDegreeErrorConstant + 1) * Real.sqrt (n : Real) * Real.sqrt b /\
    a - 3 * (abs nicolasDegreeErrorConstant + 1) * Real.sqrt (n : Real) * Real.sqrt b <=
      Chebyshev.psi b := by
  let C := abs nicolasDegreeErrorConstant + 1
  let T := C * Real.sqrt (n : Real) * Real.sqrt b
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
  have hC : 0 <= C := by dsimp [C]; positivity
  have hT : 0 <= T := by dsimp [T]; positivity
  have hA0 := abs_nicolasDegreeError_le_mass hRH hn ha hL
  have hB : abs (robinPsiWeightedErrorIntegral n b) <= T * mb :=
    abs_nicolasDegreeError_le_mass hRH hn hb hLb
  have hA : abs (robinPsiWeightedErrorIntegral n a) <= T * ma := by
    have h := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hab)
        (mul_nonneg hC (Real.sqrt_nonneg (n : Real)))) hma.le
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
  dsimp [T, C] at hLeft hRight
  constructor <;> linarith only [hLeft, hRight]

theorem nicolasDegree_dilation_power {n : Nat} (hn : 2 <= n)
    {a : Real} (ha : 0 <= a) :
    2 * a ^ n <= (a * (n : Real) / ((n : Real) - 1)) ^ n := by
  have hN : (2 : Real) <= n := by exact_mod_cast hn
  have hd : 0 < (n : Real) - 1 := by linarith
  let u := Inv.inv ((n : Real) - 1)
  have hu : 0 <= u := (inv_pos.mpr hd).le
  have hBernoulli (m : Nat) : 1 + (m : Real) * u <= (1 + u) ^ m := by
    induction m with
    | zero => simp
    | succ m ih =>
      rw [pow_succ, Nat.cast_add, Nat.cast_one]
      have h := mul_le_mul_of_nonneg_right ih (show 0 <= 1 + u by linarith)
      nlinarith only [h, mul_nonneg (Nat.cast_nonneg m) (sq_nonneg u)]
  have hNu : 1 <= (n : Real) * u := by
    calc
      _ = ((n : Real) - 1) * u := by dsimp [u]; field_simp
      _ <= _ := mul_le_mul_of_nonneg_right (by linarith) hu
  have hratio : (n : Real) / ((n : Real) - 1) = 1 + u := by
    dsimp [u]
    field_simp
    ring
  have hPow : (2 : Real) <= ((n : Real) / ((n : Real) - 1)) ^ n := by
    rw [hratio]
    linarith only [hBernoulli n, hNu]
  have h := mul_le_mul_of_nonneg_left hPow (pow_nonneg ha n)
  rw [show a * (n : Real) / ((n : Real) - 1) =
      a * ((n : Real) / ((n : Real) - 1)) by ring, mul_pow]
  simpa only [mul_comm] using h


theorem abs_nicolasPsiError_le_degree (hRH : RiemannHypothesis)
    {n : Nat} (hn : 2 <= n) {x : Real} (hx : 4 <= x)
    (hL : 1 <= Real.log (x / 2)) :
    abs (Chebyshev.psi x - x) <= x / ((n : Real) - 1) +
      6 * (abs nicolasDegreeErrorConstant + 1) * Real.sqrt (n : Real) * Real.sqrt x := by
  let a := x * ((n : Real) - 1) / (n : Real)
  let b := x * (n : Real) / ((n : Real) - 1)
  let C := abs nicolasDegreeErrorConstant + 1
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
  have hLower := (nicolasDegree_band_pointwise_bounds hRH hn ha2 hLa hax
    (by simpa only [hScaledA] using nicolasDegree_dilation_power hn (by linarith : 0 <= a))).2
  have hUpper := (nicolasDegree_band_pointwise_bounds hRH hn (by linarith : 2 <= x)
    hLx hxb (nicolasDegree_dilation_power hn hxPos.le)).1
  have hSqrt : Real.sqrt b <= 2 * Real.sqrt x := by
    have hbp : 0 <= b := hxPos.le.trans hxb
    nlinarith only [Real.sq_sqrt hbp, Real.sq_sqrt hxPos.le,
      Real.sqrt_nonneg b, Real.sqrt_nonneg x, hbx, hxPos]
  have hC : 0 <= C := by dsimp [C]; positivity
  have hScaledRoot := mul_le_mul_of_nonneg_left hSqrt
    (show 0 <= 3 * C * Real.sqrt (n : Real) by positivity)
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
  have hRootNonneg : 0 <= C * Real.sqrt (n : Real) * Real.sqrt x := by positivity
  change abs (Chebyshev.psi x - x) <= x / ((n : Real) - 1) +
    6 * C * Real.sqrt (n : Real) * Real.sqrt x
  change a - 3 * C * Real.sqrt (n : Real) * Real.sqrt x <= Chebyshev.psi x at hLower
  change Chebyshev.psi x <= b + 3 * C * Real.sqrt (n : Real) * Real.sqrt b at hUpper
  apply abs_le.mpr
  constructor <;> nlinarith only [hLower, hUpper, hScaledRoot, hDiffA, hDiffB,
    hFractions, hRootNonneg]


theorem abs_nicolasPsiError_le_two_thirds (hRH : RiemannHypothesis)
    {x : Real} (hx : 4 <= x) (hL : 1 <= Real.log (x / 2)) :
    abs (Chebyshev.psi x - x) <=
      (1 + 12 * (abs nicolasDegreeErrorConstant + 1)) * x ^ (2 / 3 : Real) := by
  let q := x ^ (1 / 3 : Real)
  let n := Nat.ceil q + 1
  let C := abs nicolasDegreeErrorConstant + 1
  have hxPos : 0 < x := by linarith
  have hqPos : 0 < q := Real.rpow_pos_of_pos hxPos _
  have hq1 : 1 <= q := by
    simpa only [Real.one_rpow] using
      Real.rpow_le_rpow (by norm_num : (0 : Real) <= 1)
        (by linarith : (1 : Real) <= x) (by norm_num : (0 : Real) <= 1 / 3)
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
  have hnUpper : (n : Real) <= 3 * q := by linarith only [hceilHi, hnEq, hq1]
  have hFirst : x / ((n : Real) - 1) <= x ^ (2 / 3 : Real) := by
    have hInv := one_div_le_one_div_of_le hqPos hnLower
    have h := mul_le_mul_of_nonneg_left hInv hxPos.le
    have hRatio : x / q = x ^ (2 / 3 : Real) := by
      change x / x ^ (1 / 3 : Real) = _
      calc
        _ = x ^ (1 : Real) / x ^ (1 / 3 : Real) := by rw [Real.rpow_one]
        _ = x ^ ((1 : Real) - 1 / 3) := (Real.rpow_sub hxPos _ _).symm
        _ = _ := by norm_num
    simpa only [one_div, <- div_eq_mul_inv, hRatio] using h
  have hSq : (x ^ (1 / 6 : Real)) ^ (2 : Nat) = q := by
    rw [<- Real.rpow_natCast, <- Real.rpow_mul hxPos.le]
    dsimp [q]
    norm_num
  have hRoot : Real.sqrt (n : Real) <= 2 * x ^ (1 / 6 : Real) := by
    have hPos := Real.rpow_pos_of_pos hxPos (1 / 6 : Real)
    nlinarith only [Real.sq_sqrt (Nat.cast_nonneg n), Real.sqrt_nonneg (n : Real),
      hPos, hSq, hnUpper, hqPos]
  have hPowers : x ^ (1 / 6 : Real) * Real.sqrt x = x ^ (2 / 3 : Real) := by
    rw [Real.sqrt_eq_rpow, <- Real.rpow_add hxPos]
    congr 1
    norm_num
  have hC : 0 <= C := by dsimp [C]; positivity
  have hRootTerm := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right hRoot (Real.sqrt_nonneg x))
    (show 0 <= 6 * C by positivity)
  have h := abs_nicolasPsiError_le_degree hRH hn hx hL
  change abs (Chebyshev.psi x - x) <= (1 + 12 * C) * x ^ (2 / 3 : Real)
  change abs (Chebyshev.psi x - x) <= x / ((n : Real) - 1) +
    6 * C * Real.sqrt (n : Real) * Real.sqrt x at h
  have hRootTerm' :
      6 * C * Real.sqrt (n : Real) * Real.sqrt x <= 12 * C * x ^ (2 / 3 : Real) := by
    calc
      _ <= 6 * C * (2 * x ^ (1 / 6 : Real) * Real.sqrt x) := by
        nlinarith only [hRootTerm]
      _ = _ := by rw [mul_assoc 2 _ _, hPowers]; ring
  nlinarith only [h, hFirst, hRootTerm']


theorem abs_nicolasThetaError_le_two_thirds (hRH : RiemannHypothesis)
    {x : Real} (hx : 4 <= x) (hL : 1 <= Real.log (x / 2)) :
    abs (Chebyshev.theta x - x) <=
      (13 + 12 * (abs nicolasDegreeErrorConstant + 1)) * x ^ (2 / 3 : Real) := by
  have hxPos : 0 < x := by linarith
  have hPsi := abs_nicolasPsiError_le_two_thirds hRH hx hL
  have hDiff := Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log (by linarith : 1 <= x)
  have hLog : Real.log x <= 6 * x ^ (1 / 6 : Real) := by
    have h := Real.log_le_rpow_div hxPos.le (by norm_num : (0 : Real) < 1 / 6)
    convert h using 1
    ring
  have hPowers : Real.sqrt x * x ^ (1 / 6 : Real) = x ^ (2 / 3 : Real) := by
    rw [Real.sqrt_eq_rpow, <- Real.rpow_add hxPos]
    congr 1
    norm_num
  have hLogTerm : 2 * Real.sqrt x * Real.log x <= 12 * x ^ (2 / 3 : Real) := by
    have h := mul_le_mul_of_nonneg_left hLog
      (show 0 <= 2 * Real.sqrt x by positivity)
    calc
      _ <= 12 * (Real.sqrt x * x ^ (1 / 6 : Real)) := by nlinarith only [h]
      _ = _ := by rw [hPowers]
  have hTriangle := abs_sub_le (Chebyshev.theta x) (Chebyshev.psi x) x
  rw [abs_sub_comm (Chebyshev.theta x) (Chebyshev.psi x)] at hTriangle
  nlinarith only [hPsi, hDiff, hLogTerm, hTriangle]

end PrimeFactorOscillations

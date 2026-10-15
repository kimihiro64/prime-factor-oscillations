/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.LPFMajorSelection

/-!
# Actual minor-grid estimate with uniform physical cutoffs

The reduced unit approximation, both Type I sums and the complete coupled
Type II packet are consumed on the actual major-grid complement. Floor
cutoffs, physical placement, all quarter-beta conditions and logarithmic
dyadic counts are proved. The mean-square consumer is separate.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.LPF

noncomputable def lpfVaughanCutoff (M : Nat) : Nat :=
  Nat.floor ((M : Real) ^ (2 / 5 : Real)) + 1

noncomputable def lpfVaughanDyadicCount (M : Nat) : Nat :=
  Nat.floor (Real.log (2 * (M : Real)) / Real.log 2) + 1

theorem lpf_vaughan_cutoff_bounds (M : Nat) (hM : 1 <= M) :
    And (1 <= lpfVaughanCutoff M)
      (And ((M : Real) ^ (2 / 5 : Real) <= (lpfVaughanCutoff M : Real))
        ((lpfVaughanCutoff M : Real) <= 2 * (M : Real) ^ (2 / 5 : Real))) := by
  have hMR : (1 : Real) <= (M : Real) := by exact_mod_cast hM
  have hOne : 1 <= (M : Real) ^ (2 / 5 : Real) := Real.one_le_rpow hMR (by norm_num)
  have hFloor := Nat.floor_le (by positivity : 0 <= (M : Real) ^ (2 / 5 : Real))
  have hLt := Nat.lt_floor_add_one ((M : Real) ^ (2 / 5 : Real))
  refine And.intro (by dsimp [lpfVaughanCutoff]; omega) (And.intro ?_ ?_)
  next =>
    dsimp [lpfVaughanCutoff]
    push_cast
    exact hLt.le
  next =>
    dsimp [lpfVaughanCutoff]
    push_cast
    linarith only [hFloor, hOne]

theorem lpf_vaughan_cutoff_product (M : Nat) (hM : 1 <= M) :
    ((lpfVaughanCutoff M * lpfVaughanCutoff M : Nat) : Real) <=
      4 * (M : Real) ^ (4 / 5 : Real) := by
  have h := (lpf_vaughan_cutoff_bounds M hM).2.2
  have hSq := mul_le_mul h h (by positivity) (by positivity)
  have hPower : ((M : Real) ^ (2 / 5 : Real)) ^ 2 = (M : Real) ^ (4 / 5 : Real) := by
    calc
      _ = ((M : Real) ^ (2 / 5 : Real)) ^ (2 : Real) := (Real.rpow_natCast _ 2).symm
      _ = (M : Real) ^ ((2 / 5 : Real) * 2) := (Real.rpow_mul (by positivity) _ _).symm
      _ = _ := by norm_num
  push_cast
  nlinarith only [hSq, hPower]

theorem lpf_warm_power_lower (M b : Nat) (hM : 2 ^ 18 <= M)
    (a : Real) (ha : 0 <= a) (hExp : (b : Real) <= 18 * a) :
    (2 : Real) ^ b <= (M : Real) ^ a := by
  have hBase : (2 : Real) ^ 18 <= (M : Real) := by exact_mod_cast hM
  rw [<- Real.rpow_natCast (2 : Real) 18] at hBase
  have hPow := Real.rpow_le_rpow (by positivity) hBase ha
  rw [<- Real.rpow_mul (by norm_num : (0 : Real) <= 2)] at hPow
  calc
    _ = (2 : Real) ^ (b : Real) := (Real.rpow_natCast _ _).symm
    _ <= (2 : Real) ^ (18 * a) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hExp
    _ <= _ := hPow

theorem lpf_vaughan_dyadic_count_bounds (M : Nat) (hM : 1 <= M) :
    And (2 * M <= 2 ^ lpfVaughanDyadicCount M)
      ((lpfVaughanDyadicCount M : Real) <=
        (1 + 1 / Real.log 2) * (1 + Real.log (2 * (M : Real)))) := by
  have hMR : (1 : Real) <= (M : Real) := by exact_mod_cast hM
  have hTop : (0 : Real) < 2 * (M : Real) := by linarith only [hMR]
  have hLog : 0 <= Real.log (2 * (M : Real)) := Real.log_nonneg (by linarith only [hMR])
  have hLogTwo : (0 : Real) < Real.log 2 := Real.log_pos (by norm_num)
  have hDiv : 0 <= Real.log (2 * (M : Real)) / Real.log 2 := by positivity
  have hJ : Real.log (2 * (M : Real)) / Real.log 2 < (lpfVaughanDyadicCount M : Real) := by
    dsimp [lpfVaughanDyadicCount]
    push_cast
    exact Nat.lt_floor_add_one _
  have hJLog := mul_lt_mul_of_pos_right hJ hLogTwo
  have hCancel : (Real.log (2 * (M : Real)) / Real.log 2) * Real.log 2 =
      Real.log (2 * (M : Real)) := by field_simp
  rw [hCancel] at hJLog
  have hExp := Real.exp_le_exp.mpr hJLog.le
  rw [Real.exp_log hTop, Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : Real) < 2)] at hExp
  refine And.intro (by exact_mod_cast hExp) ?_
  have hFloor := Nat.floor_le hDiv
  have hInv : 0 <= 1 / Real.log 2 := by positivity
  dsimp [lpfVaughanDyadicCount]
  push_cast
  have hNormalize : Real.log (2 * (M : Real)) / Real.log 2 =
      Real.log (2 * (M : Real)) * (1 / Real.log 2) := by ring
  rw [hNormalize] at hFloor
  rw [hNormalize]
  nlinarith only [hFloor, hInv, hLog]

theorem lpf_warm_multiple_rpow_le (M b : Nat) (hM : 2 ^ 18 <= M)
    (a : Real) (ha : a <= 1) (hExp : (b : Real) <= 18 * (1 - a)) :
    (2 : Real) ^ b * (M : Real) ^ a <= (M : Real) := by
  have hMPos : (0 : Real) < (M : Real) := by
    have hOne : 1 <= M := (by decide : 1 <= 2 ^ 18).trans hM
    exact_mod_cast (by omega : 0 < M)
  have hLower := lpf_warm_power_lower M b hM (1 - a) (by linarith only [ha]) hExp
  calc
    _ <= (M : Real) ^ (1 - a) * (M : Real) ^ a :=
      mul_le_mul_of_nonneg_right hLower (Real.rpow_nonneg hMPos.le _)
    _ = (M : Real) ^ ((1 - a) + a) := (Real.rpow_add hMPos _ _).symm
    _ = _ := by simp only [sub_add_cancel, Real.rpow_one]

theorem lpf_vaughan_cutoff_warm_upper (M : Nat) (hM : 2 ^ 18 <= M) :
    (lpfVaughanCutoff M : Real) <= (5 / 4 : Real) * (M : Real) ^ (2 / 5 : Real) := by
  have hFour := lpf_warm_power_lower M 2 hM (2 / 5) (by norm_num) (by norm_num)
  norm_num at hFour
  have hFloor := Nat.floor_le (by positivity : 0 <= (M : Real) ^ (2 / 5 : Real))
  dsimp [lpfVaughanCutoff]
  push_cast
  linarith only [hFour, hFloor]

theorem lpf_vaughan_cutoff_warm_product (M : Nat) (hM : 2 ^ 18 <= M) :
    ((lpfVaughanCutoff M * lpfVaughanCutoff M : Nat) : Real) <=
      (25 / 16 : Real) * (M : Real) ^ (4 / 5 : Real) := by
  have h := lpf_vaughan_cutoff_warm_upper M hM
  have hSq := mul_le_mul h h (by positivity) (by positivity)
  have hPower : ((M : Real) ^ (2 / 5 : Real)) ^ 2 = (M : Real) ^ (4 / 5 : Real) := by
    calc
      _ = ((M : Real) ^ (2 / 5 : Real)) ^ (2 : Real) := (Real.rpow_natCast _ 2).symm
      _ = (M : Real) ^ ((2 / 5 : Real) * 2) := (Real.rpow_mul (by positivity) _ _).symm
      _ = _ := by norm_num
  push_cast
  nlinarith only [hSq, hPower]

theorem lpf_vaughan_cutoff_physical (M : Nat) (hM : 2 ^ 18 <= M) :
    And ((lpfVaughanCutoff M : Real) <= (M : Real) / 4)
      (((lpfVaughanCutoff M * lpfVaughanCutoff M : Nat) : Real) <= (M : Real) / 4) := by
  have hOne : 1 <= M := (by decide : 1 <= 2 ^ 18).trans hM
  have hU := (lpf_vaughan_cutoff_bounds M hOne).2.2
  have hUV := lpf_vaughan_cutoff_warm_product M hM
  have hFirst := lpf_warm_multiple_rpow_le M 3 hM (2 / 5) (by norm_num) (by norm_num)
  have hSecond := lpf_warm_multiple_rpow_le M 3 hM (4 / 5) (by norm_num) (by norm_num)
  have hPowerNN : 0 <= (M : Real) ^ (4 / 5 : Real) := by positivity
  norm_num at hFirst hSecond
  exact And.intro (by linarith only [hU, hFirst]) (by linarith only [hUV, hSecond, hPowerNN])

theorem lpf_beta_product_le_quarter (M P q : Nat) (beta D : Real)
    (hM : 0 < M) (hq : 0 < q) (hD : 0 <= D)
    (hBeta : abs beta <= (P : Real) / ((M : Real) * (q : Real)))
    (hSize : 4 * (P : Real) * D <= (M : Real)) :
    abs beta * D <= 1 / (4 * (q : Real)) := by
  have hMR : (0 : Real) < (M : Real) := by exact_mod_cast hM
  have hqR : (0 : Real) < (q : Real) := by exact_mod_cast hq
  calc
    _ <= ((P : Real) / ((M : Real) * (q : Real))) * D :=
      mul_le_mul_of_nonneg_right hBeta hD
    _ <= _ := by
      apply (mul_le_mul_iff_of_pos_right (by positivity : 0 < 4 * (M : Real) * (q : Real))).mp
      calc
        _ = 4 * (P : Real) * D := by field_simp
        _ <= (M : Real) := hSize
        _ = _ := by field_simp

theorem lpf_vaughan_cutoff_beta (M P q : Nat) (hM : 2 ^ 18 <= M)
    (hq : 0 < q) (beta : Real)
    (hP : (P : Real) <= (M : Real) ^ ((1 : Real) / 40))
    (hBeta : abs beta <= (P : Real) / ((M : Real) * (q : Real))) :
    And (abs beta * (lpfVaughanCutoff M : Real) <= 1 / (4 * (q : Real)))
      (And (abs beta * ((lpfVaughanCutoff M * lpfVaughanCutoff M : Nat) : Real) <=
          1 / (4 * (q : Real)))
        (abs beta * (2 * (M : Real) ^ (3 / 5 : Real)) <= 1 / (4 * (q : Real)))) := by
  have hOne : 1 <= M := (by decide : 1 <= 2 ^ 18).trans hM
  have hMPosNat : 0 < M := by omega
  have hMPos : (0 : Real) < (M : Real) := by exact_mod_cast hMPosNat
  have hU := (lpf_vaughan_cutoff_bounds M hOne).2.2
  have hUV := lpf_vaughan_cutoff_warm_product M hM
  have hSizeU : 4 * (P : Real) * (lpfVaughanCutoff M : Real) <=
      8 * (M : Real) ^ (17 / 40 : Real) := by
    calc
      _ <= 4 * (M : Real) ^ ((1 : Real) / 40) * (2 * (M : Real) ^ (2 / 5 : Real)) := by gcongr
      _ = 8 * ((M : Real) ^ ((1 : Real) / 40) * (M : Real) ^ (2 / 5 : Real)) := by ring
      _ = _ := by rw [<- Real.rpow_add hMPos]; norm_num
  have hSizeUV : 4 * (P : Real) * ((lpfVaughanCutoff M * lpfVaughanCutoff M : Nat) : Real) <=
      8 * (M : Real) ^ (33 / 40 : Real) := by
    calc
      _ <= 4 * (M : Real) ^ ((1 : Real) / 40) *
          ((25 / 16 : Real) * (M : Real) ^ (4 / 5 : Real)) := by gcongr
      _ = (25 / 4 : Real) * (M : Real) ^ (33 / 40 : Real) := by
        rw [show 4 * (M : Real) ^ ((1 : Real) / 40) *
            ((25 / 16 : Real) * (M : Real) ^ (4 / 5 : Real)) =
            (25 / 4 : Real) * ((M : Real) ^ ((1 : Real) / 40) *
              (M : Real) ^ (4 / 5 : Real)) by ring, <- Real.rpow_add hMPos]
        norm_num
      _ <= _ := mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
  have hSizeII : 4 * (P : Real) * (2 * (M : Real) ^ (3 / 5 : Real)) <=
      8 * (M : Real) ^ (5 / 8 : Real) := by
    calc
      _ <= 4 * (M : Real) ^ ((1 : Real) / 40) * (2 * (M : Real) ^ (3 / 5 : Real)) := by gcongr
      _ = 8 * ((M : Real) ^ ((1 : Real) / 40) * (M : Real) ^ (3 / 5 : Real)) := by ring
      _ = _ := by rw [<- Real.rpow_add hMPos]; norm_num
  have hWarmU := lpf_warm_multiple_rpow_le M 3 hM (17 / 40) (by norm_num) (by norm_num)
  have hWarmUV := lpf_warm_multiple_rpow_le M 3 hM (33 / 40) (by norm_num) (by norm_num)
  have hWarmII := lpf_warm_multiple_rpow_le M 3 hM (5 / 8) (by norm_num) (by norm_num)
  norm_num at hWarmU hWarmUV hWarmII
  exact And.intro
    (lpf_beta_product_le_quarter M P q beta (lpfVaughanCutoff M : Real)
      hMPosNat hq (by positivity) hBeta (hSizeU.trans hWarmU))
    (And.intro
      (lpf_beta_product_le_quarter M P q beta
        ((lpfVaughanCutoff M * lpfVaughanCutoff M : Nat) : Real)
        hMPosNat hq (by positivity) hBeta (hSizeUV.trans hWarmUV))
      (lpf_beta_product_le_quarter M P q beta (2 * (M : Real) ^ (3 / 5 : Real))
        hMPosNat hq (by positivity) hBeta (hSizeII.trans hWarmII)))

theorem lpf_vaughan_warm_grid_minor_squared_bound :
    exists C0 : Real, And (0 < C0)
      (forall {N : Nat} [NeZero N] (M P s L : Nat),
        2 ^ 18 <= M -> 0 < P ->
        (P : Real) <= (M : Real) ^ ((1 : Real) / 40) ->
        Dvd.dvd M N -> (forall q, 0 < q -> q <= P -> Dvd.dvd q N) ->
        (M : Real) / 4 <= (s : Real) -> s + L <= 2 * M ->
        forall k : Int,
        Not (Membership.mem (lpfRationalGrid N P ((N / M) * P)) (k : ZMod N)) ->
        norm (lpfGridIntervalWeight N s L (k : ZMod N)) ^ 2 <=
          1296 * ((M : Real) / (P : Real)) ^ 2 * (1 + Real.log (2 * (M : Real))) ^ 4 +
          2304 * (M : Real) ^ (8 / 5 : Real) * (1 + Real.log (2 * (M : Real))) ^ 4 +
          2 * C0 * (lpfVaughanDyadicCount M : Real) ^ 4 *
            (M : Real) ^ ((1 : Real) / 160) *
            (3 * ((M : Real) ^ 2 / (P : Real)) + (M : Real) ^ (8 / 5 : Real)) *
            (1 + Real.log (2 * (M : Real))) ^ 3) := by
  choose C0 hC0 hBound using lpf_vaughan_minor_squared_bound
  refine Exists.intro C0 (And.intro hC0 ?_)
  intro N instN M P s L hM hP hPPower hDivM hDiv hStart hTop k hMinor
  have hOne : 1 <= M := (by decide : 1 <= 2 ^ 18).trans hM
  have hMR : (1 : Real) <= (M : Real) := by exact_mod_cast hOne
  have hPowerTop : (M : Real) ^ ((1 : Real) / 40) <= (M : Real) := by
    calc
      _ <= (M : Real) ^ (1 : Real) := Real.rpow_le_rpow_of_exponent_le hMR (by norm_num)
      _ = _ := Real.rpow_one _
  have hPM : P <= M := by exact_mod_cast (hPPower.trans hPowerTop)
  choose a q u beta hApprox using lpf_exists_minor_unit_approximation M P k hP hPM hDivM hDiv hMinor
  have hq : 0 < q := hApprox.1
  letI : NeZero q := { out := Nat.ne_of_gt hq }
  have hCut := lpf_vaughan_cutoff_bounds M hOne
  have hPhysical := lpf_vaughan_cutoff_physical M hM
  have hBeta := lpf_vaughan_cutoff_beta M P q hM hq beta hPPower hApprox.2.2.2.2.2.2
  have hCount := lpf_vaughan_dyadic_count_bounds M hOne
  have hCutTopR : (lpfVaughanCutoff M : Real) <= 2 * (M : Real) := by
    linarith only [hPhysical.1, hMR]
  have hCutTop : lpfVaughanCutoff M <= 2 * M := by exact_mod_cast hCutTopR
  have hCutStart : lpfVaughanCutoff M <= s := by exact_mod_cast (hPhysical.1.trans hStart)
  have hCutX : lpfVaughanCutoff M <= s + L := hCutStart.trans (Nat.le_add_right s L)
  have hProductStart : lpfVaughanCutoff M * lpfVaughanCutoff M <= s := by
    exact_mod_cast (hPhysical.2.trans hStart)
  have hProductX : lpfVaughanCutoff M * lpfVaughanCutoff M <= s + L :=
    hProductStart.trans (Nat.le_add_right s L)
  have hCountCut : 2 * M <= lpfVaughanCutoff M * 2 ^ lpfVaughanDyadicCount M := by
    have hMul : 2 ^ lpfVaughanDyadicCount M <=
        lpfVaughanCutoff M * 2 ^ lpfVaughanDyadicCount M := by
      simpa only [one_mul] using Nat.mul_le_mul_right (2 ^ lpfVaughanDyadicCount M) hCut.1
    exact hCount.1.trans hMul
  have h := hBound (N := N) (q := q) M P hOne hP hApprox.2.2.1 hApprox.2.1.le
    hApprox.2.2.2.1 k a u hApprox.2.2.2.2.1 beta
    (lpfVaughanCutoff M) (lpfVaughanCutoff M)
    (lpfVaughanDyadicCount M) (lpfVaughanDyadicCount M) s L
    hCut.1 hCutTop hCutTop hCut.2.1 hCut.2.1 hCountCut hCountCut hTop hCutStart hCutX hProductX
    (lpf_vaughan_cutoff_product M hOne) hApprox.2.2.2.2.2.1 hBeta.1 hBeta.2.1 hBeta.2.2
  convert h using 1 <;> ring

theorem lpf_grid_minor_uniform_squared_bound :
    exists C : Real, And (0 < C)
      (forall {N : Nat} [NeZero N] (M P s L : Nat),
        2 ^ 18 <= M -> 0 < P ->
        (P : Real) <= (M : Real) ^ ((1 : Real) / 40) ->
        Dvd.dvd M N -> (forall q, 0 < q -> q <= P -> Dvd.dvd q N) ->
        (M : Real) / 4 <= (s : Real) -> s + L <= 2 * M ->
        forall k : Int,
        Not (Membership.mem (lpfRationalGrid N P ((N / M) * P)) (k : ZMod N)) ->
        norm (lpfGridIntervalWeight N s L (k : ZMod N)) ^ 2 <=
          C * (M : Real) ^ ((1 : Real) / 160) *
            ((M : Real) ^ 2 / (P : Real) + (M : Real) ^ (8 / 5 : Real)) *
            (1 + Real.log (2 * (M : Real))) ^ 7) := by
  choose C0 hC0 hRawBound using lpf_vaughan_warm_grid_minor_squared_bound
  let cJ : Real := 1 + 1 / Real.log 2
  have hLogTwo : (0 : Real) < Real.log 2 := Real.log_pos (by norm_num)
  have hcJ : 0 < cJ := by dsimp [cJ]; positivity
  refine Exists.intro (3600 + 6 * C0 * cJ ^ 4) (And.intro (by positivity) ?_)
  intro N instN M P s L hM hP hPPower hDivM hDiv hStart hTop k hMinor
  have hOne : 1 <= M := (by decide : 1 <= 2 ^ 18).trans hM
  have hMR : (1 : Real) <= (M : Real) := by exact_mod_cast hOne
  have hPR : (1 : Real) <= (P : Real) := by exact_mod_cast (by omega : 1 <= P)
  have hPPos : (0 : Real) < (P : Real) := by exact_mod_cast hP
  let ell : Real := 1 + Real.log (2 * (M : Real))
  let j : Real := (lpfVaughanDyadicCount M : Real)
  let D : Real := (M : Real) ^ ((1 : Real) / 160) *
    ((M : Real) ^ 2 / (P : Real) + (M : Real) ^ (8 / 5 : Real)) * ell ^ 7
  have hEll : 1 <= ell := by
    have hLog : 0 <= Real.log (2 * (M : Real)) := Real.log_nonneg (by linarith only [hMR])
    dsimp [ell]
    linarith only [hLog]
  have hEll2 : 1 <= ell ^ 2 := by nlinarith only [hEll, sq_nonneg (ell - 1)]
  have hEll3 : 1 <= ell ^ 3 := by
    have h := mul_le_mul hEll2 hEll (by norm_num : (0 : Real) <= 1) (by positivity)
    convert h using 1 <;> ring
  have hEll47 : ell ^ 4 <= ell ^ 7 := by
    calc
      _ = ell ^ 4 * 1 := by ring
      _ <= ell ^ 4 * ell ^ 3 := mul_le_mul_of_nonneg_left hEll3 (by positivity)
      _ = _ := by ring
  have hEps : 1 <= (M : Real) ^ ((1 : Real) / 160) := Real.one_le_rpow hMR (by norm_num)
  have hScale : (M : Real) ^ 2 / (P : Real) + (M : Real) ^ (8 / 5 : Real) <=
      (M : Real) ^ ((1 : Real) / 160) *
        ((M : Real) ^ 2 / (P : Real) + (M : Real) ^ (8 / 5 : Real)) := by
    calc
      _ = 1 * ((M : Real) ^ 2 / (P : Real) + (M : Real) ^ (8 / 5 : Real)) := by ring
      _ <= _ := mul_le_mul_of_nonneg_right hEps (by positivity)
  have hRatio : ((M : Real) / (P : Real)) ^ 2 <= (M : Real) ^ 2 / (P : Real) := by
    rw [div_pow]
    gcongr
    nlinarith only [hPR]
  have hA : ((M : Real) / (P : Real)) ^ 2 <= (M : Real) ^ ((1 : Real) / 160) *
      ((M : Real) ^ 2 / (P : Real) + (M : Real) ^ (8 / 5 : Real)) := by
    have hAdd : (M : Real) ^ 2 / (P : Real) <=
        (M : Real) ^ 2 / (P : Real) + (M : Real) ^ (8 / 5 : Real) := by
      have hNonneg : 0 <= (M : Real) ^ (8 / 5 : Real) := by positivity
      linarith only [hNonneg]
    exact (hRatio.trans hAdd).trans hScale
  have hB : (M : Real) ^ (8 / 5 : Real) <= (M : Real) ^ ((1 : Real) / 160) *
      ((M : Real) ^ 2 / (P : Real) + (M : Real) ^ (8 / 5 : Real)) := by
    have hAdd : (M : Real) ^ (8 / 5 : Real) <=
        (M : Real) ^ 2 / (P : Real) + (M : Real) ^ (8 / 5 : Real) := by
      have hNonneg : 0 <= (M : Real) ^ 2 / (P : Real) := by positivity
      linarith only [hNonneg]
    exact hAdd.trans hScale
  have hJ := (lpf_vaughan_dyadic_count_bounds M hOne).2
  change j <= cJ * ell at hJ
  have hjNonneg : 0 <= j := by dsimp [j]; positivity
  have hJ2 : j ^ 2 <= (cJ * ell) ^ 2 := by
    simpa only [pow_two] using mul_le_mul hJ hJ hjNonneg (by positivity)
  have hJ4 : j ^ 4 <= cJ ^ 4 * ell ^ 4 := by
    have h := mul_le_mul hJ2 hJ2 (sq_nonneg _) (sq_nonneg _)
    convert h using 1 <;> ring
  have hFirst : 1296 * ((M : Real) / (P : Real)) ^ 2 * ell ^ 4 <= 1296 * D := by
    have h := mul_le_mul hA hEll47 (by positivity) (by positivity)
    have hScaled := mul_le_mul_of_nonneg_left h (by norm_num : (0 : Real) <= 1296)
    convert hScaled using 1 <;> ring
  have hSecond : 2304 * (M : Real) ^ (8 / 5 : Real) * ell ^ 4 <= 2304 * D := by
    have h := mul_le_mul hB hEll47 (by positivity) (by positivity)
    have hScaled := mul_le_mul_of_nonneg_left h (by norm_num : (0 : Real) <= 2304)
    convert hScaled using 1 <;> ring
  have hThird : 2 * C0 * j ^ 4 * (M : Real) ^ ((1 : Real) / 160) *
      (3 * ((M : Real) ^ 2 / (P : Real)) + (M : Real) ^ (8 / 5 : Real)) * ell ^ 3 <=
      6 * C0 * cJ ^ 4 * D := by
    calc
      _ <= 2 * C0 * (cJ ^ 4 * ell ^ 4) * (M : Real) ^ ((1 : Real) / 160) *
        (3 * ((M : Real) ^ 2 / (P : Real) + (M : Real) ^ (8 / 5 : Real))) * ell ^ 3 := by
          gcongr
          have hNonneg : 0 <= (M : Real) ^ (8 / 5 : Real) := by positivity
          linarith only [hNonneg]
      _ = _ := by dsimp [D]; ring
  have hRaw := hRawBound (N := N) M P s L hM hP hPPower hDivM hDiv hStart hTop k hMinor
  change norm (lpfGridIntervalWeight N s L (k : ZMod N)) ^ 2 <=
    1296 * ((M : Real) / (P : Real)) ^ 2 * ell ^ 4 +
    2304 * (M : Real) ^ (8 / 5 : Real) * ell ^ 4 +
    2 * C0 * j ^ 4 * (M : Real) ^ ((1 : Real) / 160) *
      (3 * ((M : Real) ^ 2 / (P : Real)) + (M : Real) ^ (8 / 5 : Real)) * ell ^ 3 at hRaw
  calc
    _ <= _ := hRaw
    _ <= 1296 * D + 2304 * D + 6 * C0 * cJ ^ 4 * D :=
      add_le_add (add_le_add hFirst hSecond) hThird
    _ = _ := by dsimp [D, ell]; ring

end PrimeFactorOscillations.LPF

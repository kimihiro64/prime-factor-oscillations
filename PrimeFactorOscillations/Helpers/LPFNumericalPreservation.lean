/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.LPFCompletePreservationNumeric

/-!
# Numerical cutoff for complete LPF density preservation

The fixed density fraction is at least 2^(-600). The complete preservation
inequality holds for every M >= 2^49152. All large-power casts are proved
with a quantified exponent before specialization. This is a sufficient
preservation cutoff; actual entry from the seed remains a separate obligation.
-/


set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.LPF

private theorem two_pow_one_le (n : Nat) : (1 : Real) <= (2 : Real) ^ n := by
  calc
    1 <= (2 : Real) ^ (n : Real) :=
      Real.one_le_rpow (by norm_num) (Nat.cast_nonneg n)
    _ = (2 : Real) ^ n := Real.rpow_natCast (2 : Real) n

private theorem two_pow_mono (m n : Nat) (h : m <= n) :
    (2 : Real) ^ m <= (2 : Real) ^ n := by
  rw [<- Real.rpow_natCast _ m, <- Real.rpow_natCast _ n]
  exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by exact_mod_cast h)

private theorem two_inv_pow_mono (m n : Nat) (h : m <= n) :
    (1 : Real) / (2 : Real) ^ n <= 1 / (2 : Real) ^ m :=
  one_div_le_one_div_of_le (by positivity) (two_pow_mono m n h)

private theorem log_two_numeric :
    And ((2 / 3 : Real) <= Real.log 2) (Real.log 2 <= 1) := by
  let u : Real := 16 / 15
  let v : Real := 2 * (15 / 16 : Real) ^ (10 : Nat)
  have hu : 0 < u := by norm_num [u]
  have hv : 0 < v := by dsimp [v]; positivity
  have hLu := Real.log_le_sub_one_of_pos (inv_pos.mpr hu)
  have hLv := Real.log_le_sub_one_of_pos (inv_pos.mpr hv)
  rw [Real.log_inv] at hLu hLv
  have hIdentity : (2 : Real) = u ^ (10 : Nat) * v := by norm_num [u, v]
  have hLog : Real.log (2 : Real) = 10 * Real.log u + Real.log v := by
    rw [hIdentity, Real.log_mul (pow_ne_zero 10 hu.ne') hv.ne', Real.log_pow]
    norm_num
  have hLower : (2 / 3 : Real) <= Real.log 2 := by
    rw [hLog]
    norm_num [u, v] at hLu hLv
    norm_num [u, v] <;> linarith only [hLu, hLv]
  have hUpper := Real.log_le_sub_one_of_pos (by norm_num : (0 : Real) < 2)
  exact And.intro hLower (by linarith)

theorem lpf_mertens_error_constant_upper_numeric :
    PrimeFactorUnimodality.mertensErrorConstant <= 10 := by
  have h := log_two_numeric.2
  unfold PrimeFactorUnimodality.mertensErrorConstant
  rw [show (4 : Real) = 2 ^ (2 : Nat) by norm_num, Real.log_pow]
  norm_num only [Nat.cast_ofNat]
  linarith

theorem lpf_mertens_constant_lower_numeric : -(20 : Real) <= Mertens.M := by
  have hTwo := log_two_numeric
  have hLp : 0 < Real.log (2 : Real) := by linarith only [hTwo.1]
  have hC := lpf_mertens_error_constant_upper_numeric
  have hCDiv : PrimeFactorUnimodality.mertensErrorConstant / Real.log (2 : Real) <= 20 := by
    apply (mul_le_mul_iff_of_pos_right hLp).mp
    have hCancel :
        (PrimeFactorUnimodality.mertensErrorConstant / Real.log (2 : Real)) *
          Real.log (2 : Real) = PrimeFactorUnimodality.mertensErrorConstant := by field_simp
    rw [hCancel]
    linarith only [hTwo.1, hC]
  have hLogLog : Real.log (Real.log (2 : Real)) <= 0 := by
    have h := Real.log_le_log hLp hTwo.2
    simpa only [Real.log_one] using h
  have hUpper := PrimeFactorUnimodality.reciprocalPrimeSumBelow_upper_of_estimate
    PrimeFactorUnimodality.hasMertensReciprocalPrimeEstimate (by decide : 2 <= (2 : Nat))
  have hNonneg : 0 <= PrimeFactorUnimodality.reciprocalPrimeSumBelow 3 := by
    change 0 <= Finset.sum (Nat.primesBelow 3) (fun p => 1 / (p : Real))
    exact Finset.sum_nonneg (fun p _ => by positivity)
  norm_num only [Nat.cast_ofNat] at hUpper
  linarith only [hUpper, hNonneg, hLogLog, hCDiv]

theorem lpf_sieve_mertens_constant_lower_numeric :
    (1 : Real) / (2 : Real) ^ (82 : Nat) <= sieveMertensConstant := by
  have hTwo := log_two_numeric
  have hLp : 0 < Real.log (2 : Real) := by linarith only [hTwo.1]
  have hC := lpf_mertens_error_constant_upper_numeric
  have hCDiv : PrimeFactorUnimodality.mertensErrorConstant / Real.log (2 : Real) <= 20 := by
    apply (mul_le_mul_iff_of_pos_right hLp).mp
    have hCancel :
        (PrimeFactorUnimodality.mertensErrorConstant / Real.log (2 : Real)) *
          Real.log (2 : Real) = PrimeFactorUnimodality.mertensErrorConstant := by field_simp
    rw [hCancel]
    linarith only [hTwo.1, hC]
  have hExponent : -(41 : Real) <= Mertens.M -
      PrimeFactorUnimodality.mertensErrorConstant / Real.log 2 - 1 := by
    linarith only [lpf_mertens_constant_lower_numeric, hCDiv]
  have hExp41 : Real.exp (41 : Real) <= (2 : Real) ^ (82 : Nat) := by
    calc
      _ = Real.exp 1 ^ (41 : Nat) := by
        simpa only [mul_one, Nat.cast_ofNat] using Real.exp_nat_mul 1 41
      _ <= (4 : Real) ^ (41 : Nat) := by
        rw [<- Real.rpow_natCast _ 41, <- Real.rpow_natCast _ 41]
        exact Real.rpow_le_rpow (Real.exp_pos 1).le
          (by linarith [Real.exp_one_lt_three]) (by positivity)
      _ = _ := by norm_num
  calc
    _ <= 1 / Real.exp (41 : Real) :=
      one_div_le_one_div_of_le (Real.exp_pos _) hExp41
    _ = Real.exp (-(41 : Real)) := by
      simpa only [one_div] using (Real.exp_neg (41 : Real)).symm
    _ <= sieveMertensConstant := Real.exp_le_exp.mpr hExponent

theorem lpf_sieve_three_constant_upper_numeric :
    sieveThreeUpperConstant <= (2 : Real) ^ (272 : Nat) := by
  have hLower := lpf_sieve_mertens_constant_lower_numeric
  have hPower :
      ((1 : Real) / (2 : Real) ^ (82 : Nat)) ^ (3 : Nat) <= sieveMertensConstant ^ 3 := by
    rw [<- Real.rpow_natCast _ 3, <- Real.rpow_natCast _ 3]
    exact Real.rpow_le_rpow (by positivity) hLower (by positivity)
  have hDen : (((1 : Real) / (2 : Real) ^ (82 : Nat)) ^ (3 : Nat)) =
      1 / (2 : Real) ^ (246 : Nat) := by
    rw [div_pow, one_pow, <- pow_mul] <;> norm_num only [Nat.reduceMul]
  have hCoeff : 216 * (48 : Real) ^ 3 <= (2 : Real) ^ (25 : Nat) := by norm_num
  have hCombine : (2 : Real) ^ (25 : Nat) * (2 : Real) ^ (246 : Nat) =
      (2 : Real) ^ (271 : Nat) := by
    rw [<- pow_add] <;> norm_num only [Nat.reduceAdd]
  unfold sieveThreeUpperConstant
  calc
    _ <= 216 * (48 : Real) ^ 3 /
        (((1 : Real) / (2 : Real) ^ (82 : Nat)) ^ (3 : Nat)) + 1 :=
      _root_.add_le_add
        (div_le_div_of_nonneg_left (by positivity) (by positivity) hPower) (le_refl _)
    _ = (216 * (48 : Real) ^ 3) * (2 : Real) ^ (246 : Nat) + 1 := by
      rw [hDen]
      field_simp <;> ring
    _ <= ((2 : Real) ^ (25 : Nat)) * (2 : Real) ^ (246 : Nat) + 1 :=
      _root_.add_le_add
        (mul_le_mul_of_nonneg_right hCoeff (by positivity)) (le_refl _)
    _ = (2 : Real) ^ (271 : Nat) + 1 := by rw [hCombine]
    _ <= (2 : Real) ^ (272 : Nat) := by
      have hSuccessor : (2 : Real) ^ (272 : Nat) = (2 : Real) ^ (271 : Nat) * 2 :=
        pow_succ (2 : Real) 271
      calc
        (2 : Real) ^ (271 : Nat) + 1 <=
            (2 : Real) ^ (271 : Nat) + (2 : Real) ^ (271 : Nat) :=
          _root_.add_le_add (le_refl ((2 : Real) ^ (271 : Nat))) (two_pow_one_le 271)
        _ = (2 : Real) ^ (271 : Nat) * 2 := (mul_two _).symm
        _ = (2 : Real) ^ (272 : Nat) := hSuccessor.symm

noncomputable def lpfCertifiedDensityFraction : Real :=
  let a : Real := 67 / 1024
  min ((min 1 (a ^ 2 / (160 * (sieveThreeUpperConstant * 6144)))) ^ 2)
    (min (a / 64) (a ^ 2 / 64))

theorem lpf_density_fraction_lower_numeric :
    (1 : Real) / (2 : Real) ^ (600 : Nat) <= lpfCertifiedDensityFraction := by
  let a : Real := 67 / 1024
  let d : Real := 160 * (sieveThreeUpperConstant * 6144)
  have hS := sieveThreeUpperConstant_pos
  have hd : 0 < d := by dsimp [d]; positivity
  have hRatio :
      (1 : Real) / (2 : Real) ^ (300 : Nat) <= a ^ 2 / d := by
    apply (mul_le_mul_iff_of_pos_right hd).mp
    have hCancel : (a ^ 2 / d) * d = a ^ 2 := by field_simp
    rw [hCancel]
    have hPowerSplit : (2 : Real) ^ (300 : Nat) =
        (2 : Real) ^ (272 : Nat) * (2 : Real) ^ (28 : Nat) := by
      rw [<- pow_add] <;> norm_num only [Nat.reduceAdd]
    have hPowerCancel : ((1 : Real) / (2 : Real) ^ (300 : Nat)) *
        (2 : Real) ^ (272 : Nat) = 1 / (2 : Real) ^ (28 : Nat) := by
      rw [hPowerSplit]
      field_simp <;> ring
    calc
      _ <= ((1 : Real) / (2 : Real) ^ (300 : Nat)) *
          (160 * ((2 : Real) ^ (272 : Nat) * 6144)) := by
        dsimp [d]
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right lpf_sieve_three_constant_upper_numeric
              (by norm_num : (0 : Real) <= 6144))
            (by norm_num : (0 : Real) <= 160)) (by positivity)
      _ = (160 * 6144) * (((1 : Real) / (2 : Real) ^ (300 : Nat)) *
          (2 : Real) ^ (272 : Nat)) := by ac_rfl
      _ = (160 * 6144) * (1 / (2 : Real) ^ (28 : Nat)) := by rw [hPowerCancel]
      _ <= a ^ 2 := by norm_num [a]
  have hOne : (1 : Real) / (2 : Real) ^ (300 : Nat) <= 1 := by
    simpa only [pow_zero, div_one] using two_inv_pow_mono 0 300 (by decide)
  have hInner :
      (1 : Real) / (2 : Real) ^ (300 : Nat) <= min 1 (a ^ 2 / d) :=
    le_min hOne hRatio
  have hSquare :
      (((1 : Real) / (2 : Real) ^ (300 : Nat)) ^ (2 : Nat)) <=
        (min 1 (a ^ 2 / d)) ^ (2 : Nat) := by
    have h := mul_self_le_mul_self (by positivity) hInner
    simpa only [pow_two] using h
  have hPowerEq : (1 : Real) / (2 : Real) ^ (600 : Nat) =
      (((1 : Real) / (2 : Real) ^ (300 : Nat)) ^ (2 : Nat)) := by
    rw [div_pow, one_pow, <- pow_mul] <;> norm_num only [Nat.reduceMul]
  change (1 : Real) / (2 : Real) ^ (600 : Nat) <=
    min ((min 1 (a ^ 2 / d)) ^ 2) (min (a / 64) (a ^ 2 / 64))
  apply le_min
  next => exact hPowerEq.le.trans hSquare
  next =>
    apply le_min
    next =>
      exact (two_inv_pow_mono 14 600 (by decide)).trans
        (show (1 : Real) / (2 : Real) ^ (14 : Nat) <= a / 64 by norm_num [a])
    next =>
      exact (two_inv_pow_mono 14 600 (by decide)).trans
        (show (1 : Real) / (2 : Real) ^ (14 : Nat) <= a ^ 2 / 64 by norm_num [a])

theorem lpf_density_preservation_power_cutoff (K M : Nat) (S : Finset Nat)
    (hK : 49152 <= K) (hM : 2 ^ K <= M)
    (hDense : ((SDiff.sdiff (inputPrimePrefix M) S).card : Real) <=
      lpfCertifiedDensityFraction * ((M : Real) / Real.log (M : Real))) :
    ((SDiff.sdiff (inputPrimePrefix (7 * M / 6)) (fullStep S)).card : Real) <=
      lpfCertifiedDensityFraction *
        (((7 * M / 6 : Nat) : Real) / Real.log ((7 * M / 6 : Nat) : Real)) := by
  have hPower : (2 : Real) ^ K <= (M : Real) := by
    have h : ((2 ^ K : Nat) : Real) <= (M : Real) := by exact_mod_cast hM
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using h
  have hSmallPower : (2 : Real) ^ (24 : Nat) <= (2 : Real) ^ K := by
    rw [<- Real.rpow_natCast _ 24, <- Real.rpow_natCast _ K]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num)
      (by exact_mod_cast (show 24 <= K by omega))
  have hM24 : 2 ^ 24 <= M := by exact_mod_cast hSmallPower.trans hPower
  have hTwo := log_two_numeric
  have hTwo0 : 0 <= Real.log (2 : Real) := by linarith only [hTwo.1]
  have hLogPower := Real.log_le_log (by positivity : 0 < (2 : Real) ^ K) hPower
  rw [Real.log_pow] at hLogPower
  have hKR : (49152 : Real) <= (K : Real) := by exact_mod_cast hK
  have hHalf := mul_le_mul_of_nonneg_left hTwo.1 (Nat.cast_nonneg K : (0 : Real) <= (K : Real))
  have hLog : 32768 <= Real.log (M : Real) := by
    linarith only [hLogPower, hKR, hHalf]
  have hEtaLower := lpf_density_fraction_lower_numeric
  have hEta : 0 < lpfCertifiedDensityFraction :=
    (by positivity : (0 : Real) < 1 / (2 : Real) ^ (600 : Nat)).trans_le hEtaLower
  have hInv : 1 / lpfCertifiedDensityFraction <= (2 : Real) ^ (600 : Nat) := by
    calc
      _ <= 1 / ((1 : Real) / (2 : Real) ^ (600 : Nat)) :=
        one_div_le_one_div_of_le (by positivity) hEtaLower
      _ = _ := by field_simp
  have hLogEta := Real.log_le_log (one_div_pos.mpr hEta) hInv
  rw [Real.log_pow] at hLogEta
  norm_num only [Nat.cast_ofNat] at hLogEta
  have hExponent : (48000 : Real) <= (K : Real) := by linarith only [hKR]
  have hCompare := mul_le_mul_of_nonneg_right hExponent hTwo0
  have hScale : 80 * Real.log (1 / lpfCertifiedDensityFraction) <= Real.log (M : Real) := by
    linarith only [hLogEta, hLogPower, hCompare]
  exact lpf_short_dense_preservation_numeric M S hM24 hLog hScale hDense

theorem lpf_density_preservation_numerical_cutoff (M : Nat) (S : Finset Nat)
    (hM : 2 ^ (49152 : Nat) <= M)
    (hDense : ((SDiff.sdiff (inputPrimePrefix M) S).card : Real) <=
      lpfCertifiedDensityFraction * ((M : Real) / Real.log (M : Real))) :
    ((SDiff.sdiff (inputPrimePrefix (7 * M / 6)) (fullStep S)).card : Real) <=
      lpfCertifiedDensityFraction *
        (((7 * M / 6 : Nat) : Real) / Real.log ((7 * M / 6 : Nat) : Real)) := by
  exact lpf_density_preservation_power_cutoff 49152 M S (by decide) hM hDense

end PrimeFactorOscillations.LPF

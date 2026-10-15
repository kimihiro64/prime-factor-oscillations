/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.LPFEntryThreshold
import PrimeFactorOscillations.Helpers.LPFShortSourceNumeric
import PrimeFactorOscillations.Helpers.LPFSubwindowNumeric

/-!
# Complete finite LPF density preservation

The source count, normalized deletion recurrence, both cofactor branches and
residual logarithm are absorbed in the same growth margin. The density fraction
is displayed explicitly. This theorem does not establish entry from the seed
or assign a numerical value to its sieve-dependent density fraction.
-/


set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.LPF

theorem lpf_short_source_allowance_numeric (X eta : Real)
    (hX : 0 < X) (hEta : 0 < eta) (hLog : 32768 <= Real.log X)
    (hEtaScale : 80 * Real.log (1 / eta) <= Real.log X) :
    (2 : Real) ^ (117 : Nat) * X ^ (39 / 40 : Real) *
        (1 + Real.log (2 * X)) ^ 12 <=
      (5 / 192 : Real) * eta * (X / Real.log X) := by
  let L := Real.log X
  have hL : 32768 <= L := hLog
  have hLp : 0 < L := by linarith
  have hTwo : Real.log (2 : Real) <= 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : Real) < 2)
    linarith
  have hTwo0 : 0 <= Real.log (2 : Real) := Real.log_nonneg (by norm_num)
  have hBase : Real.log (32768 : Real) <= 15 := by
    rw [show (32768 : Real) = 2 ^ (15 : Nat) by norm_num, Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    linarith only [hTwo]
  have hTangent := Real.log_le_sub_one_of_pos
    (div_pos hLp (by norm_num : (0 : Real) < 32768))
  rw [Real.log_div hLp.ne' (by norm_num)] at hTangent
  have hLogPower : 13 * Real.log L <= L / 160 := by
    linarith only [hTangent, hBase, hL]
  have hRatio : -(38 : Real) <= Real.log (5 / 192 : Real) := by
    have h := Real.log_le_sub_one_of_pos
      (by norm_num : (0 : Real) < Inv.inv (5 / 192 : Real))
    rw [Real.log_inv] at h
    norm_num at h
    linarith
  have hScale : -(80 : Real) * Real.log eta <= L := by
    rw [one_div, Real.log_inv] at hEtaScale
    change 80 * (-Real.log eta) <= L at hEtaScale
    linarith only [hEtaScale]
  have hEllEq : 1 + Real.log (2 * X) = 1 + Real.log (2 : Real) + L := by
    rw [Real.log_mul (by norm_num) hX.ne']
    dsimp [L]
    ring
  have hEll : And (0 <= 1 + Real.log (2 * X))
      (1 + Real.log (2 * X) <= 2 * L) := by
    rw [hEllEq]
    exact And.intro (by linarith) (by linarith)
  have hEllPower : (1 + Real.log (2 * X)) ^ (12 : Nat) <= (2 * L) ^ (12 : Nat) := by
    rw [<- Real.rpow_natCast _ 12, <- Real.rpow_natCast _ 12]
    exact Real.rpow_le_rpow hEll.1 hEll.2 (by positivity)
  have hLift :
      (2 : Real) ^ (117 : Nat) * X ^ (39 / 40 : Real) *
          (1 + Real.log (2 * X)) ^ 12 <=
        (2 : Real) ^ (129 : Nat) * X ^ (39 / 40 : Real) * L ^ 12 := by
    calc
      _ <= (2 : Real) ^ (117 : Nat) * X ^ (39 / 40 : Real) * (2 * L) ^ 12 :=
        mul_le_mul_of_nonneg_left hEllPower (by positivity)
      _ = _ := by rw [mul_pow]; norm_num; ring
  have hCpos : 0 < (2 : Real) ^ (129 : Nat) := by positivity
  have hPpos : 0 < X ^ (39 / 40 : Real) := Real.rpow_pos_of_pos hX _
  have hRpos : (0 : Real) < 5 / 192 := by norm_num
  have hLogA : Real.log ((2 : Real) ^ (129 : Nat) * X ^ (39 / 40 : Real) * L ^ 12) =
      129 * Real.log (2 : Real) + (39 / 40 : Real) * L + 12 * Real.log L := by
    rw [Real.log_mul (mul_ne_zero hCpos.ne' hPpos.ne') (pow_ne_zero 12 hLp.ne'),
      Real.log_mul hCpos.ne' hPpos.ne', Real.log_pow, Real.log_rpow hX, Real.log_pow]
    norm_num only [Nat.cast_ofNat] <;> rfl
  have hLogB : Real.log ((5 / 192 : Real) * eta * (X / L)) =
      Real.log (5 / 192 : Real) + Real.log eta + L - Real.log L := by
    rw [Real.log_mul (mul_ne_zero hRpos.ne' hEta.ne') (div_ne_zero hX.ne' hLp.ne'),
      Real.log_mul hRpos.ne' hEta.ne', Real.log_div hX.ne' hLp.ne']
    dsimp [L]
    ring
  have hLogBound :
      Real.log ((2 : Real) ^ (129 : Nat) * X ^ (39 / 40 : Real) * L ^ 12) <=
        Real.log ((5 / 192 : Real) * eta * (X / L)) := by
    rw [hLogA, hLogB]
    linarith only [hTwo, hLogPower, hRatio, hScale, hL]
  have hExp := Real.exp_le_exp.mpr hLogBound
  rw [Real.exp_log (by positivity), Real.exp_log (by positivity)] at hExp
  exact hLift.trans hExp

theorem lpf_short_dense_preservation_numeric (M : Nat) (S : Finset Nat)
    (hM : 2 ^ 24 <= M) (hLog : 32768 <= Real.log (M : Real)) :
    let a : Real := 67 / 1024
    let eta : Real := min ((min 1 (a ^ 2 / (160 * (sieveThreeUpperConstant * 6144)))) ^ 2)
      (min (a / 64) (a ^ 2 / 64))
    80 * Real.log (1 / eta) <= Real.log (M : Real) ->
    ((SDiff.sdiff (inputPrimePrefix M) S).card : Real) <=
      eta * ((M : Real) / Real.log (M : Real)) ->
    ((SDiff.sdiff (inputPrimePrefix (7 * M / 6)) (fullStep S)).card : Real) <=
      eta * (((7 * M / 6 : Nat) : Real) / Real.log ((7 * M / 6 : Nat) : Real)) := by
  classical
  let a : Real := 67 / 1024
  let eta : Real := min ((min 1 (a ^ 2 / (160 * (sieveThreeUpperConstant * 6144)))) ^ 2)
    (min (a / 64) (a ^ 2 / 64))
  have ha : 0 < a := by norm_num [a]
  have hK := sieveThreeUpperConstant_pos
  have hEta : 0 < eta := by
    dsimp [eta]
    apply lt_min
    next => exact sq_pos_of_pos (lt_min (by norm_num) (by positivity))
    next => exact lt_min (by positivity) (by positivity)
  dsimp only
  intro hScale hE
  change 80 * Real.log (1 / eta) <= Real.log (M : Real) at hScale
  change ((SDiff.sdiff (inputPrimePrefix M) S).card : Real) <=
    eta * ((M : Real) / Real.log (M : Real)) at hE
  change ((SDiff.sdiff (inputPrimePrefix (7 * M / 6)) (fullStep S)).card : Real) <=
    eta * (((7 * M / 6 : Nat) : Real) / Real.log ((7 * M / 6 : Nat) : Real))
  have hMWarm : 2 ^ 20 <= M := (by decide : 2 ^ 20 <= 2 ^ 24).trans hM
  have hMSieve : 5 ^ 8 <= M := (by decide : 5 ^ 8 <= 2 ^ 24).trans hM
  have hMp : 0 < (M : Real) := by exact_mod_cast (show 0 < M by omega)
  choose Z hZ hSupply using lpf_short_primeTarget_supply_numeric M hMWarm
  have hRec := lpf_dense_fullStep_subwindow_row_numeric a ha M hMSieve hLog
    (7 * M / 6) (by omega : 7 * M / 6 <= 5 * M / 4) S Z hE hSupply
  have hRec' :
      ((SDiff.sdiff (inputPrimePrefix (7 * M / 6)) (fullStep S)).card : Real) <=
        (17 / 16 : Real) * ((SDiff.sdiff (inputPrimePrefix M) S).card : Real) +
          (Z.card : Real) + (8192 / 67 : Real) * eta * Real.log (M : Real) := by
    change ((SDiff.sdiff (inputPrimePrefix (7 * M / 6)) (fullStep S)).card : Real) <=
      (17 / 16 : Real) * ((SDiff.sdiff (inputPrimePrefix M) S).card : Real) +
        (Z.card : Real) + (8 * eta / a) * Real.log (M : Real) at hRec
    have hCoefficient : 8 * eta / a = (8192 / 67 : Real) * eta := by
      dsimp only [a]
      ring
    rw [hCoefficient] at hRec
    exact hRec
  have hSource := hZ.trans (lpf_short_source_allowance_numeric (M : Real) eta
    hMp hEta hLog hScale)
  have hResidual := lpf_short_residual_allowance_explicit (M : Real)
    (by exact_mod_cast hM)
  have hGrowth := mul_le_mul_of_nonneg_left (lpf_short_growth_margin_nat M hMWarm) hEta.le
  have hResidual' := mul_le_mul_of_nonneg_left hResidual hEta.le
  have hE' := mul_le_mul_of_nonneg_left hE (by norm_num : (0 : Real) <= 17 / 16)
  nlinarith only [hGrowth, hResidual', hE', hRec', hSource]

end PrimeFactorOscillations.LPF

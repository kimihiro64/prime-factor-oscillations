/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.LPFShortSupply

/-!
# Finite entry-threshold inequalities
These inequalities replace eventual growth and logarithm comparisons by
explicit domains. Analytic source constants and overlap cutoffs are separate
inputs; no numerical full entry threshold or seed-entry theorem is asserted.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.LPF

theorem lpf_short_growth_margin_explicit (X Y : Real)
    (hX : 48 <= X) (hLog : 8 <= Real.log X)
    (hLower : 7 * X / 6 - 1 <= Y) (hUpper : Y <= 7 * X / 6) :
    (5 / 96 : Real) * (X / Real.log X) <=
      Y / Real.log Y - (17 / 16 : Real) * (X / Real.log X) := by
  have hXp : 0 < X := by linarith only [hX]
  have hLX : 0 < Real.log X := by linarith only [hLog]
  have hYlower : (55 / 48 : Real) * X <= Y := by linarith only [hX, hLower]
  have hYone : 1 < Y := by linarith only [hX, hYlower]
  have hYp : 0 < Y := by linarith only [hYone]
  have hLY : 0 < Real.log Y := Real.log_pos hYone
  have hRatio : Y / X <= (7 / 6 : Real) := by
    apply (mul_le_mul_iff_of_pos_right hXp).mp
    have hCancel : (Y / X) * X = Y := by field_simp
    rw [hCancel]
    linarith only [hUpper]
  have hLogRatio := Real.log_le_sub_one_of_pos (div_pos hYp hXp)
  rw [Real.log_div hYp.ne' hXp.ne'] at hLogRatio
  have hLogUpper : Real.log Y <= (49 / 48 : Real) * Real.log X := by
    linarith only [hLogRatio, hRatio, hLog]
  have hScaledUpper := mul_le_mul_of_nonneg_left hLogUpper
    (by positivity : 0 <= (107 / 96 : Real) * X)
  have hScaledLower := mul_le_mul_of_nonneg_right hYlower hLX.le
  have hProduct : (107 / 96 : Real) * X * Real.log Y <= Y * Real.log X := by
    nlinarith only [hScaledUpper, hScaledLower, mul_pos hXp hLX]
  have hFraction : (107 / 96 : Real) * (X / Real.log X) <= Y / Real.log Y := by
    apply (mul_le_mul_iff_of_pos_right hLY).mp
    have hCancel : (Y / Real.log Y) * Real.log Y = Y := by field_simp
    rw [hCancel]
    apply (mul_le_mul_iff_of_pos_right hLX).mp
    have hCancel' : ((107 / 96 : Real) * (X / Real.log X) * Real.log Y) *
        Real.log X = (107 / 96 : Real) * X * Real.log Y := by field_simp
    rw [hCancel']
    exact hProduct
  linarith only [hFraction]

theorem lpf_log_rebase_explicit (X0 X b eps : Real)
    (hX0 : 0 < X0) (hX : X0 <= X) (hEps : 0 < eps)
    (hBase : 1 <= eps * (b + Real.log X0)) :
    b + Real.log X <= (b + Real.log X0) * (X / X0) ^ eps := by
  have hXp : 0 < X := hX0.trans_le hX
  have hQ : 1 <= X / X0 := by
    apply (mul_le_mul_iff_of_pos_right hX0).mp
    have hCancel : (X / X0) * X0 = X := by field_simp
    rw [hCancel, one_mul]
    exact hX
  have hQp : 0 < X / X0 := zero_lt_one.trans_le hQ
  have hR : 1 <= (X / X0) ^ eps := Real.one_le_rpow hQ hEps.le
  have hRoot := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hQp eps)
  rw [Real.log_rpow hQp] at hRoot
  have hScaled := mul_le_mul_of_nonneg_right hBase (by linarith : 0 <= (X / X0) ^ eps - 1)
  have hGap : Real.log (X / X0) <=
      (b + Real.log X0) * ((X / X0) ^ eps - 1) := by
    apply (mul_le_mul_iff_of_pos_left hEps).mp
    nlinarith only [hRoot, hScaled]
  rw [Real.log_div hXp.ne' hX0.ne'] at hGap
  nlinarith only [hGap]

theorem lpf_short_preservation_of_complete_margin (X Y eta E F Z : Real)
    (hX : 48 <= X) (hLog : 8 <= Real.log X)
    (hLower : 7 * X / 6 - 1 <= Y) (hUpper : Y <= 7 * X / 6)
    (hEta : 0 <= eta)
    (hE : E <= eta * (X / Real.log X))
    (hRec : F <= (17 / 16 : Real) * E + Z +
      (8192 / 67 : Real) * eta * Real.log X)
    (hSource : Z <= (5 / 192 : Real) * eta * (X / Real.log X))
    (hResidual : (8192 / 67 : Real) * Real.log X <=
      (5 / 192 : Real) * (X / Real.log X)) :
    F <= eta * (Y / Real.log Y) := by
  have hGrowth := mul_le_mul_of_nonneg_left
    (lpf_short_growth_margin_explicit X Y hX hLog hLower hUpper) hEta
  have hResidual' := mul_le_mul_of_nonneg_left hResidual hEta
  have hE' := mul_le_mul_of_nonneg_left hE (by norm_num : (0 : Real) <= 17 / 16)
  nlinarith only [hGrowth, hResidual', hE', hRec, hSource]

theorem lpf_short_growth_margin_nat (M : Nat) (hM : 2 ^ 20 <= M) :
    (5 / 96 : Real) * ((M : Real) / Real.log (M : Real)) <=
      ((7 * M / 6 : Nat) : Real) / Real.log ((7 * M / 6 : Nat) : Real) -
        (17 / 16 : Real) * ((M : Real) / Real.log (M : Real)) := by
  have hMR : (48 : Real) <= (M : Real) := by exact_mod_cast (by omega : 48 <= M)
  have hLogTwo : (1 / 2 : Real) <= Real.log 2 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : Real) < Inv.inv (2 : Real))
    rw [Real.log_inv] at h
    norm_num at h
    linarith only [h]
  have hBase : (8 : Real) <= Real.log ((2 : Real) ^ (20 : Nat)) := by
    rw [Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    linarith only [hLogTwo]
  have hMBase : (2 : Real) ^ (20 : Nat) <= (M : Real) := by exact_mod_cast hM
  have hLog : (8 : Real) <= Real.log (M : Real) :=
    hBase.trans (Real.log_le_log (by positivity) hMBase)
  have hLowerNat : 7 * M <= 6 * (7 * M / 6) + 5 := by omega
  have hUpperNat : 6 * (7 * M / 6) <= 7 * M := by omega
  have hLowerR : (7 : Real) * (M : Real) <=
      6 * ((7 * M / 6 : Nat) : Real) + 5 := by exact_mod_cast hLowerNat
  have hUpperR : (6 : Real) * ((7 * M / 6 : Nat) : Real) <=
      7 * (M : Real) := by exact_mod_cast hUpperNat
  exact lpf_short_growth_margin_explicit (M : Real) ((7 * M / 6 : Nat) : Real)
    hMR hLog (by linarith only [hLowerR]) (by linarith only [hUpperR])

theorem lpf_short_residual_allowance_explicit (X : Real)
    (hX : (2 : Real) ^ (24 : Nat) <= X) :
    (8192 / 67 : Real) * Real.log X <=
      (5 / 192 : Real) * (X / Real.log X) := by
  let B : Real := (2 : Real) ^ (24 : Nat)
  have hB : 0 < B := by dsimp [B]; positivity
  have hXB : B <= X := hX
  have hXp : 0 < X := hB.trans_le hXB
  have hLogTwoLower : (1 / 2 : Real) <= Real.log 2 := by
    have h := Real.log_le_sub_one_of_pos
      (by norm_num : (0 : Real) < Inv.inv (2 : Real))
    rw [Real.log_inv] at h
    norm_num at h
    linarith only [h]
  have hLogTwoUpper : Real.log 2 <= (1 : Real) := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : Real) < 2)
    norm_num at h
    exact h
  have hLogB : And (12 <= Real.log B) (Real.log B <= 24) := by
    dsimp [B]
    rw [Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    constructor <;> linarith only [hLogTwoLower, hLogTwoUpper]
  have hLogX : 0 < Real.log X :=
    (by linarith only [hLogB.1] : 0 < Real.log B).trans_le
      (Real.log_le_log hB hXB)
  have hBase : (1 : Real) <= (1 / 2 : Real) * (0 + Real.log B) := by
    calc
      _ <= (1 / 2 : Real) * 12 := by norm_num
      _ <= _ := mul_le_mul_of_nonneg_left
        (by simpa only [zero_add] using hLogB.1) (by norm_num)
  have hRebase := lpf_log_rebase_explicit B X 0 (1 / 2 : Real)
    hB hXB (by norm_num) hBase
  simp only [zero_add] at hRebase
  rw [<- Real.sqrt_eq_rpow] at hRebase
  have hSq : Real.log X ^ 2 <=
      (Real.log B * Real.sqrt (X / B)) ^ 2 := by
    have h := mul_self_le_mul_self hLogX.le hRebase
    nlinarith only [h]
  rw [mul_pow, Real.sq_sqrt (div_nonneg hXp.le hB.le)] at hSq
  have hBaseSq : Real.log B ^ 2 <= (24 : Real) ^ 2 := by
    nlinarith only [hLogB.1, hLogB.2]
  have hSqBound : Real.log X ^ 2 <= 576 * (X / B) := by
    have h := mul_le_mul_of_nonneg_right hBaseSq
      (div_nonneg hXp.le hB.le)
    nlinarith only [hSq, h]
  have hProduct : Real.log X ^ 2 * B <= 576 * X := by
    calc
      Real.log X ^ 2 * B <= (576 * (X / B)) * B :=
        mul_le_mul_of_nonneg_right hSqBound hB.le
      _ = 576 * X := by field_simp
  have hRaw : (8192 / 67 : Real) * Real.log X ^ 2 <=
      (5 / 192 : Real) * X := by
    dsimp [B] at hProduct
    norm_num at hProduct
    nlinarith only [hProduct, hXp.le]
  apply (mul_le_mul_iff_of_pos_right hLogX).mp
  have hCancel : ((5 / 192 : Real) * (X / Real.log X)) * Real.log X =
      (5 / 192 : Real) * X := by field_simp
  rw [hCancel]
  nlinarith only [hRaw]


end PrimeFactorOscillations.LPF


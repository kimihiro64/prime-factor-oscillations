/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.LPFDivisorMoment

/-! Explicit divisor-square constants preserving their parameter ranges. -/

/-!
# Explicit divisor constant for numerical LPF thresholds
The bound uses a specified numerical expression instead of an arbitrary
existential witness. Huge powers remain symbolic throughout the proof.
-/

set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 100

namespace PrimeFactorOscillations.LPF

theorem lpf_divisors_square_rpow_explicit (K : Nat) (hK : 1 <= K) (n : Nat) :
    (n.divisors.card : Real) ^ 2 <=
      (lpfDivisorPowerConstant K : Real) ^ (2 / (K : Real)) *
        (n : Real) ^ (2 / (K : Real)) := by
  let B : Real := (lpfDivisorPowerConstant K : Real)
  have hB : 0 < B := Nat.cast_pos.mpr (lpfDivisorPowerConstant_pos K)
  have hKpos : (0 : Real) < (K : Real) := Nat.cast_pos.mpr (by omega)
  have hExponent : (0 : Real) <= 2 / (K : Real) := div_nonneg (by norm_num) hKpos.le
  have hCast : (n.divisors.card : Real) ^ K <= B * (n : Real) := by
    have h : ((n.divisors.card ^ K : Nat) : Real) <=
        ((lpfDivisorPowerConstant K * n : Nat) : Real) :=
      Nat.cast_le.mpr (lpf_divisors_card_pow_le n K hK)
    simpa only [Nat.cast_pow, Nat.cast_mul] using h
  have hRoot := Real.rpow_le_rpow (pow_nonneg (Nat.cast_nonneg n.divisors.card) K)
    hCast hExponent
  have hCancel : (K : Real) * (2 / (K : Real)) = 2 := by field_simp
  have hLeft : ((n.divisors.card : Real) ^ K) ^ (2 / (K : Real)) =
      (n.divisors.card : Real) ^ 2 := by
    rw [<- Real.rpow_natCast, <- Real.rpow_mul (Nat.cast_nonneg n.divisors.card)]
    rw [hCancel, Real.rpow_two]
  rw [hLeft, Real.mul_rpow hB.le (Nat.cast_nonneg n)] at hRoot
  exact hRoot

theorem lpf_divisor_power_constant_upper (K : Nat) (hK : K <= 512) :
    lpfDivisorPowerConstant K <= 2 ^ ((10 * K) * 2 ^ K) := by
  have hFact : forall n : Nat, n <= K -> n.factorial <= 512 ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      intro hn
      rw [Nat.factorial_succ, pow_succ]
      calc
        _ <= 512 * 512 ^ n := Nat.mul_le_mul (by omega : n + 1 <= 512) (ih (by omega))
        _ = _ := Nat.mul_comm _ _
  have hBase : K.factorial * 2 ^ K <= 2 ^ (10 * K) := by
    calc
      _ <= 512 ^ K * 2 ^ K := Nat.mul_le_mul_right _ (hFact K le_rfl)
      _ = _ := by
        rw [show (512 : Nat) = 2 ^ (9 : Nat) by decide, <- pow_mul, <- pow_add]
        congr 1
        omega
  unfold lpfDivisorPowerConstant
  calc
    _ <= (2 ^ (10 * K)) ^ (2 ^ K) := Nat.pow_le_pow_left hBase _
    _ = _ := by rw [<- pow_mul]

theorem lpf_divisor_square_constant_upper (K : Nat) (hK : 1 <= K) (hKUpper : K <= 512) :
    (lpfDivisorPowerConstant K : Real) ^ (2 / (K : Real)) <=
      (2 : Real) ^ (20 * 2 ^ K) := by
  have hKPos : (0 : Real) < (K : Real) := Nat.cast_pos.mpr (by omega)
  have hCast : (lpfDivisorPowerConstant K : Real) <=
      (2 : Real) ^ ((10 * K) * 2 ^ K) := by
    exact_mod_cast lpf_divisor_power_constant_upper K hKUpper
  have hRoot := Real.rpow_le_rpow (Nat.cast_nonneg (lpfDivisorPowerConstant K))
    hCast (by positivity : (0 : Real) <= 2 / (K : Real))
  have hPower : ((2 : Real) ^ ((10 * K) * 2 ^ K)) ^ (2 / (K : Real)) =
      (2 : Real) ^ (20 * 2 ^ K) := by
    rw [<- Real.rpow_natCast, <- Real.rpow_mul (by norm_num : (0 : Real) <= 2),
      <- Real.rpow_natCast]
    congr 1
    push_cast
    field_simp
    <;> ring
  rwa [hPower] at hRoot

theorem lpf_divisor_square_constant_320_upper :
    (lpfDivisorPowerConstant 320 : Real) ^ (1 / 160 : Real) <=
      (2 : Real) ^ (20 * 2 ^ (320 : Nat)) := by
  have h := lpf_divisor_square_constant_upper 320 (by decide) (by decide)
  have hExponent : 2 / ((320 : Nat) : Real) = 1 / 160 := by norm_num
  rw [hExponent] at h
  exact h

theorem lpf_divisors_square_numeric_bound (n : Nat) :
    (n.divisors.card : Real) ^ 2 <=
      (2 : Real) ^ (20 * 2 ^ (320 : Nat)) * (n : Real) ^ (1 / 160 : Real) := by
  have h := lpf_divisors_square_rpow_explicit 320 (by decide) n
  have hExponent : 2 / ((320 : Nat) : Real) = 1 / 160 := by norm_num
  rw [hExponent] at h
  exact h.trans (mul_le_mul_of_nonneg_right lpf_divisor_square_constant_320_upper
    (Real.rpow_nonneg (Nat.cast_nonneg n) _))

end PrimeFactorOscillations.LPF

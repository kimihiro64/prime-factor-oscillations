/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianAperiodicUniformEnvelope

/-! # The full growing-parameter aperiodic error rate

Both residual ranges are absorbed in the same bound. The constants
are explicit; the final small-density condition is on A squared
relative to log N, with no fixed-kernel or fixed-rank restriction.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

def hamiltonianAperiodicTailLogThreshold : Real :=
  16 * Real.exp 2 * (Real.exp 2) ^ 2 + 18

def hamiltonianAperiodicErrorConstant (delta : Real) : Real :=
  16 * Real.exp 2 + 1 + 1 / delta

def hamiltonianAperiodicSublogDensity (delta : Real) : Real :=
  min 1 (1 / (18 * hamiltonianAperiodicErrorConstant delta))

theorem hamiltonian_aperiodic_residual_log_envelope
    (n a : Real) (hn : 1 <= n) (ha : 1 <= a)
    (hCap : a <= Real.log n)
    (hLog : hamiltonianAperiodicTailLogThreshold <= Real.log n) :
    hamiltonianAperiodicResidualEnvelope n a <=
      8 * n ^ (-1 / 9 : Real) * Real.exp (16 * Real.exp 2 * a ^ 2) := by
  let C : Real := 16 * Real.exp 2 * (Real.exp 2) ^ 2
  let L : Real := Real.log (2 * n)
  have hnPos : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have ha0 : 0 <= a := by linarith only [ha]
  have hC : 0 <= C := by dsimp [C]; positivity
  have hLog0 : 0 <= Real.log n := Real.log_nonneg hn
  have hLL : Real.log n <= L :=
    Real.log_le_log hnPos (by linarith only [hn])
  have hL : 0 <= L := hLog0.trans hLL
  have hAL : a <= L := hCap.trans hLL
  have hThreshold : C + 18 <= Real.log n := hLog
  have hL1 : 1 <= L := by linarith only [hThreshold, hLL, hC]
  have hMargin : 1 <= L - (C + 16) := by linarith only [hThreshold, hLL]
  have hSquare : L <= L ^ 2 := by
    have h := mul_le_mul_of_nonneg_right hL1 hL
    nlinarith only [h]
  have hCrest : (C + 16) * L ^ 2 - L ^ 3 <= -L := by
    have h := mul_le_mul_of_nonneg_right hMargin (sq_nonneg L)
    nlinarith only [h, hSquare]
  have hASquare : a ^ 2 <= L ^ 2 := by
    have h := mul_le_mul hAL hAL ha0 hL
    nlinarith only [h]
  have hCoefficient : 16 * a * L + C * a ^ 2 <= (C + 16) * L ^ 2 := by
    have hLinear := mul_le_mul_of_nonneg_right hAL (mul_nonneg (by norm_num : (0 : Real) <= 16) hL)
    have hQuadratic := mul_le_mul_of_nonneg_left hASquare hC
    nlinarith only [hLinear, hQuadratic]
  have hExponent : 16 * a * L + C * a ^ 2 - L ^ 3 <= Real.log n * (-1 / 9 : Real) := by
    linarith only [hCoefficient, hCrest, hLL, hLog0]
  have hExp : Real.exp (16 * a * L + C * a ^ 2 - L ^ 3) <= n ^ (-1 / 9 : Real) := by
    rw [Real.rpow_def_of_pos hnPos]
    exact Real.exp_le_exp.mpr hExponent
  have hU : 0 <= 16 * a * L := mul_nonneg (mul_nonneg (by norm_num) ha0) hL
  have hFactor : 2 * Real.exp (16 * a * L) + 1 <= 3 * Real.exp (16 * a * L) := by
    have h := Real.one_le_exp hU
    linarith only [h]
  have hExpAdd : Real.exp (16 * a * L + C * a ^ 2 - L ^ 3) =
      Real.exp (16 * a * L) * Real.exp (-(L ^ 3)) * Real.exp (C * a ^ 2) := by
    rw [show 16 * a * L + C * a ^ 2 - L ^ 3 =
      (16 * a * L + -(L ^ 3)) + C * a ^ 2 by ring, Real.exp_add, Real.exp_add]
  have hTail :
      (2 * Real.exp (16 * a * L) + 1) * Real.exp (-(L ^ 3)) *
        (2 * Real.exp (C * a ^ 2)) <= 6 * n ^ (-1 / 9 : Real) := by
    calc
      _ <= (3 * Real.exp (16 * a * L)) * Real.exp (-(L ^ 3)) *
          (2 * Real.exp (C * a ^ 2)) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hFactor (Real.exp_pos _).le)
          (mul_nonneg (by norm_num) (Real.exp_pos _).le)
      _ = 6 * Real.exp (16 * a * L + C * a ^ 2 - L ^ 3) := by rw [hExpAdd]; ring
      _ <= _ := mul_le_mul_of_nonneg_left hExp (by norm_num)
  have hX : 0 <= n ^ (-1 / 9 : Real) := Real.rpow_nonneg hnPos.le _
  have hY : 1 <= Real.exp (16 * Real.exp 2 * a ^ 2) :=
    Real.one_le_exp (mul_nonneg (mul_nonneg (by norm_num) (Real.exp_pos _).le) (sq_nonneg a))
  have hScaled := mul_le_mul_of_nonneg_left hY
    (mul_nonneg (by norm_num : (0 : Real) <= 6) hX)
  have hOrder : 16 * Real.exp 2 * a ^ 2 * (Real.exp 2) ^ 2 = C * a ^ 2 := by
    dsimp only [C]
    ring
  unfold hamiltonianAperiodicResidualEnvelope
  rw [hOrder]
  change n ^ (-1 / 9 : Real) * (2 * Real.exp (16 * Real.exp 2 * a ^ 2)) +
      (2 * Real.exp (16 * a * L) + 1) * Real.exp (-(L ^ 3)) *
        (2 * Real.exp (C * a ^ 2)) <= _
  nlinarith only [hTail, hScaled]

theorem hamiltonian_aperiodic_relative_log_envelope
    (n a delta : Real) (hn : 1 <= n) (ha : 1 <= a) (hDelta : 0 < delta)
    (hCap : a <= Real.log n)
    (hLog : hamiltonianAperiodicTailLogThreshold <= Real.log n) :
    Real.exp ((a - 1) + (a - 1) / delta) *
        hamiltonianAperiodicResidualEnvelope n a <=
      8 * n ^ (-1 / 9 : Real) *
        Real.exp (hamiltonianAperiodicErrorConstant delta * a ^ 2) := by
  have hRaw := hamiltonian_aperiodic_residual_log_envelope n a hn ha hCap hLog
  have hA : a - 1 <= a ^ 2 := by nlinarith only [sq_nonneg (a - 1), ha]
  have hCoeff : 0 <= 1 + 1 / delta := by positivity
  have hLinear : (a - 1) + (a - 1) / delta <= (1 + 1 / delta) * a ^ 2 := by
    calc
      _ = (1 + 1 / delta) * (a - 1) := by ring
      _ <= _ := mul_le_mul_of_nonneg_left hA hCoeff
  have hProduct : Real.exp ((a - 1) + (a - 1) / delta) *
      Real.exp (16 * Real.exp 2 * a ^ 2) <=
      Real.exp (hamiltonianAperiodicErrorConstant delta * a ^ 2) := by
    rw [<- Real.exp_add]
    apply Real.exp_le_exp.mpr
    dsimp only [hamiltonianAperiodicErrorConstant]
    nlinarith only [hLinear]
  have hX : 0 <= 8 * n ^ (-1 / 9 : Real) :=
    mul_nonneg (by norm_num) (Real.rpow_nonneg (by linarith only [hn]) _)
  calc
    _ <= Real.exp ((a - 1) + (a - 1) / delta) *
        (8 * n ^ (-1 / 9 : Real) * Real.exp (16 * Real.exp 2 * a ^ 2)) :=
      mul_le_mul_of_nonneg_left hRaw (Real.exp_pos _).le
    _ = (8 * n ^ (-1 / 9 : Real)) *
        (Real.exp ((a - 1) + (a - 1) / delta) * Real.exp (16 * Real.exp 2 * a ^ 2)) := by ring
    _ <= _ := mul_le_mul_of_nonneg_left hProduct hX

theorem hamiltonian_aperiodic_density_budget
    (delta : Real) (hDelta : 0 < delta) :
    0 < hamiltonianAperiodicErrorConstant delta /\
      0 < hamiltonianAperiodicSublogDensity delta /\
      hamiltonianAperiodicSublogDensity delta <= 1 /\
      hamiltonianAperiodicErrorConstant delta * hamiltonianAperiodicSublogDensity delta <= 1 / 18 := by
  let C := hamiltonianAperiodicErrorConstant delta
  have hC : 0 < C := by dsimp [C, hamiltonianAperiodicErrorConstant]; positivity
  have hRecip : 0 < 1 / (18 * C) := one_div_pos.mpr (mul_pos (by norm_num) hC)
  have hSmall : 0 < hamiltonianAperiodicSublogDensity delta :=
    lt_min (by norm_num) hRecip
  have hOne : hamiltonianAperiodicSublogDensity delta <= 1 := min_le_left _ _
  have hLast : C * hamiltonianAperiodicSublogDensity delta <= 1 / 18 := by
    have h := mul_le_mul_of_nonneg_left (min_le_right (1 : Real) (1 / (18 * C))) hC.le
    have hCancel : C * (1 / (18 * C)) = 1 / 18 := by field_simp
    rw [hCancel] at h
    exact h
  exact And.intro hC (And.intro hSmall (And.intro hOne hLast))

theorem hamiltonian_aperiodic_power_from_exponent
    (n C a : Real) (hn : 0 < n) (hExponent : C * a ^ 2 <= Real.log n / 18) :
    n ^ (-1 / 9 : Real) * Real.exp (C * a ^ 2) <= n ^ (-1 / 18 : Real) := by
  rw [Real.rpow_def_of_pos hn, Real.rpow_def_of_pos hn, <- Real.exp_add]
  apply Real.exp_le_exp.mpr
  linarith only [hExponent]

end PrimeFactorOscillations

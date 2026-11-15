/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianGammaTaylor

/-! # Explicit inverse-dimension decay of signed Gamma moments

The actual cubic moment has two inverse powers despite its odd degree.
Together with the fourth moment this controls both remaining spectral
Taylor terms in the original permanent core average.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

theorem gammaInverseAverage_third_decay (n : Nat) (hn : 4 <= n) :
    abs (gammaInverseAverage n (fun s : Real => (s - 1) ^ 3)) <=
      16 / (n : Real) ^ 2 := by
  have hN : (4 : Real) <= (n : Real) := by exact_mod_cast hn
  have hN0 : 0 < (n : Real) := by linarith only [hN]
  have hM1 : 0 < (n : Real) - 1 := by linarith only [hN]
  have hM2 : 0 < (n : Real) - 2 := by linarith only [hN]
  have hLower : (n : Real) ^ 2 / 4 <= ((n : Real) - 1) * ((n : Real) - 2) := by
    have h := mul_le_mul
      (show (n : Real) / 2 <= (n : Real) - 1 by linarith only [hN])
      (show (n : Real) / 2 <= (n : Real) - 2 by linarith only [hN])
      (by positivity : (0 : Real) <= (n : Real) / 2) hM1.le
    nlinarith only [h]
  rw [gammaInverseAverage_third_uniform n (by omega),
    abs_of_nonneg (div_nonneg (by norm_num) (mul_nonneg hM1.le hM2.le))]
  calc
    _ <= 4 / ((n : Real) ^ 2 / 4) :=
      div_le_div_of_nonneg_left (by norm_num) (by positivity) hLower
    _ = _ := by field_simp [ne_of_gt hN0]; ring

theorem gammaInverseAverage_fourth_decay (n : Nat) (hn : 6 <= n) :
    gammaInverseAverage n (fun s : Real => (s - 1) ^ 4) <=
      48 / (n : Real) ^ 2 := by
  have hN : (6 : Real) <= (n : Real) := by exact_mod_cast hn
  have hN0 : 0 < (n : Real) := by linarith only [hN]
  have hM1 : 0 < (n : Real) - 1 := by linarith only [hN]
  have hM2 : 0 < (n : Real) - 2 := by linarith only [hN]
  have hM3 : 0 < (n : Real) - 3 := by linarith only [hN]
  have h12 : (n : Real) ^ 2 / 4 <= ((n : Real) - 1) * ((n : Real) - 2) := by
    have h := mul_le_mul
      (show (n : Real) / 2 <= (n : Real) - 1 by linarith only [hN])
      (show (n : Real) / 2 <= (n : Real) - 2 by linarith only [hN])
      (by positivity : (0 : Real) <= (n : Real) / 2) hM1.le
    nlinarith only [h]
  have h123 : (n : Real) ^ 3 / 8 <=
      ((n : Real) - 1) * ((n : Real) - 2) * ((n : Real) - 3) := by
    have h := mul_le_mul h12
      (show (n : Real) / 2 <= (n : Real) - 3 by linarith only [hN])
      (by positivity : (0 : Real) <= (n : Real) / 2) (mul_nonneg hM1.le hM2.le)
    nlinarith only [h]
  have hDen0 : 0 <
      ((n : Real) - 1) * ((n : Real) - 2) * ((n : Real) - 3) :=
    mul_pos (mul_pos hM1 hM2) hM3
  rw [gammaInverseAverage_fourth_uniform n (by omega)]
  calc
    _ <= (6 * (n : Real)) /
        (((n : Real) - 1) * ((n : Real) - 2) * ((n : Real) - 3)) :=
      div_le_div_of_nonneg_right (by linarith only [hN]) hDen0.le
    _ <= (6 * (n : Real)) / ((n : Real) ^ 3 / 8) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) h123
    _ = _ := by field_simp [ne_of_gt hN0]; ring

end PrimeFactorOscillations

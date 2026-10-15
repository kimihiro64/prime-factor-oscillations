/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import PrimeFactorOscillations.Helpers.LPFSievePrimeCutoff

/-!
# Explicit higher-prime-power mass and conversion cutoff

The three-root Chebyshev decomposition is applied once more to each root.
All nine correction terms are retained and bounded uniformly, giving
psi(x) - theta(x) <= 2 * sqrt(x) for x >= 2^20. The one-logarithm
two-position conversion loss is at most 15*M/256 above the same cutoff.
These are component bounds; entry of an actual LPF orbit is separate.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.LPF

noncomputable def primePowerThreeRoots (x : Real) : Real :=
  x ^ ((2 : Real) ^ (-1 : Int)) + x ^ ((3 : Real) ^ (-1 : Int)) +
    x ^ ((5 : Real) ^ (-1 : Int))

theorem psi_linear_refinement (x : Real) (hx : 0 <= x) :
    Chebyshev.psi x <= Real.log 4 * x +
      (Real.log 4 + 4) * primePowerThreeRoots x := by
  have hMass := Chebyshev.psi_sub_theta_le_psi_add_psi_add_psi x
  have hHalf := Chebyshev.psi_le_const_mul_self
    (Real.rpow_nonneg hx ((2 : Real) ^ (-1 : Int)))
  have hThird := Chebyshev.psi_le_const_mul_self
    (Real.rpow_nonneg hx ((3 : Real) ^ (-1 : Int)))
  have hFifth := Chebyshev.psi_le_const_mul_self
    (Real.rpow_nonneg hx ((5 : Real) ^ (-1 : Int)))
  have hTheta := Chebyshev.theta_le_log4_mul_x hx
  dsimp [primePowerThreeRoots]
  norm_num at *
  nlinarith only [hMass, hHalf, hThird, hFifth, hTheta]

theorem primePower_mass_refined (x : Real) (hx : 0 <= x) :
    Chebyshev.psi x - Chebyshev.theta x <=
      Real.log 4 * primePowerThreeRoots x + (Real.log 4 + 4) *
        (primePowerThreeRoots (x ^ ((2 : Real) ^ (-1 : Int))) +
          primePowerThreeRoots (x ^ ((3 : Real) ^ (-1 : Int))) +
          primePowerThreeRoots (x ^ ((5 : Real) ^ (-1 : Int)))) := by
  have hMass := Chebyshev.psi_sub_theta_le_psi_add_psi_add_psi x
  have hHalf := psi_linear_refinement _ (Real.rpow_nonneg hx ((2 : Real) ^ (-1 : Int)))
  have hThird := psi_linear_refinement _ (Real.rpow_nonneg hx ((3 : Real) ^ (-1 : Int)))
  have hFifth := psi_linear_refinement _ (Real.rpow_nonneg hx ((5 : Real) ^ (-1 : Int)))
  dsimp only [primePowerThreeRoots] at *
  norm_num at *
  nlinarith only [hMass, hHalf, hThird, hFifth]

theorem primePower_mass_rational_allowance :
    (10 / 7 : Real) * (1 + 1 / 10 + 1 / 64) +
      (38 / 7 : Real) * (1 / 32 + 2 / 100 + 2 / 256 + 1 / 200 + 2 / 400 + 1 / 512) < 2 := by
  norm_num

private theorem root_gap_lower (x d : Real) (m n : Nat)
    (hx : (2 : Real) ^ 20 <= x) (hd : 0 <= d) (hn : 0 < n)
    (hNumeral : d ^ n <= ((2 : Real) ^ 20) ^ m) :
    d <= x ^ ((m : Real) / (n : Real)) := by
  have hx0 : 0 <= x := (by norm_num : (0 : Real) <= (2 : Real) ^ 20).trans hx
  have hnR : 0 < (n : Real) := by exact_mod_cast hn
  have hnNe : Not ((n : Real) = 0) := ne_of_gt hnR
  have hMul : ((m : Real) / (n : Real)) * (n : Real) = (m : Real) := by field_simp
  have hEq : (x ^ ((m : Real) / (n : Real))) ^ n = x ^ m := by
    rw [<- Real.rpow_natCast _ n, <- Real.rpow_mul hx0, hMul, Real.rpow_natCast]
  have hUpper : ((2 : Real) ^ 20) ^ m <= x ^ m := by gcongr
  by_contra h
  have hLess : x ^ ((m : Real) / (n : Real)) < d := lt_of_not_ge h
  have hBase : 0 <= x ^ ((m : Real) / (n : Real)) := Real.rpow_nonneg hx0 _
  have hPowLess : (x ^ ((m : Real) / (n : Real))) ^ n < d ^ n := by gcongr
  rw [hEq] at hPowLess
  linarith only [hPowLess, hNumeral, hUpper]

private theorem root_term_le_sqrt_div (x d r : Real) (hx : 0 < x)
    (hd : 0 < d) (hLower : d <= x ^ r) :
    x ^ ((1 / 2 : Real) - r) <= Real.sqrt x / d := by
  apply (mul_le_mul_iff_of_pos_right hd).mp
  have hCancel : (Real.sqrt x / d) * d = Real.sqrt x := by field_simp
  rw [hCancel]
  have hSum : ((1 / 2 : Real) - r) + r = (1 / 2 : Real) := by ring
  calc
    _ = x ^ ((1 / 2 : Real) - r) * d := rfl
    _ <= x ^ ((1 / 2 : Real) - r) * x ^ r :=
      mul_le_mul_of_nonneg_left hLower (Real.rpow_nonneg hx.le _)
    _ = x ^ (1 / 2 : Real) := by rw [<- Real.rpow_add hx, hSum]
    _ = Real.sqrt x := (Real.sqrt_eq_rpow x).symm

theorem primePower_mass_flat (x : Real) (hx : 0 <= x) :
    Chebyshev.psi x - Chebyshev.theta x <=
      Real.log 4 * (Real.sqrt x + x ^ (1 / 3 : Real) + x ^ (1 / 5 : Real)) +
        (Real.log 4 + 4) *
          (x ^ (1 / 4 : Real) + 2 * x ^ (1 / 6 : Real) +
            2 * x ^ (1 / 10 : Real) + x ^ (1 / 9 : Real) +
            2 * x ^ (1 / 15 : Real) + x ^ (1 / 25 : Real)) := by
  have h := primePower_mass_refined x hx
  dsimp only [primePowerThreeRoots] at h
  norm_num at h
  simp only [<- Real.rpow_mul hx] at h
  norm_num at h
  rw [Real.sqrt_eq_rpow]
  nlinarith only [h]

theorem primePower_mass_sqrt_explicit (x : Real) (hx : (2 : Real) ^ 20 <= x) :
    Chebyshev.psi x - Chebyshev.theta x <= 2 * Real.sqrt x := by
  have hxPos : 0 < x := lt_of_lt_of_le (by positivity : (0 : Real) < (2 : Real) ^ 20) hx
  have hThird : x ^ (1 / 3 : Real) <= Real.sqrt x / 10 := by
    have hLower := root_gap_lower x 10 1 6 hx (by norm_num) (by decide) (by norm_num)
    norm_num at hLower
    have h := root_term_le_sqrt_div x 10 ((1 : Real) / (6 : Real))
      hxPos (by norm_num) hLower
    convert h using 1 <;> norm_num
  have hFifth : x ^ (1 / 5 : Real) <= Real.sqrt x / 64 := by
    have hLower := root_gap_lower x 64 3 10 hx (by norm_num) (by decide) (by norm_num)
    norm_num at hLower
    have h := root_term_le_sqrt_div x 64 ((3 : Real) / (10 : Real))
      hxPos (by norm_num) hLower
    convert h using 1 <;> norm_num
  have hQuarter : x ^ (1 / 4 : Real) <= Real.sqrt x / 32 := by
    have hLower := root_gap_lower x 32 1 4 hx (by norm_num) (by decide) (by norm_num)
    norm_num at hLower
    have h := root_term_le_sqrt_div x 32 ((1 : Real) / (4 : Real))
      hxPos (by norm_num) hLower
    convert h using 1 <;> norm_num
  have hSixth : x ^ (1 / 6 : Real) <= Real.sqrt x / 100 := by
    have hLower := root_gap_lower x 100 1 3 hx (by norm_num) (by decide) (by norm_num)
    norm_num at hLower
    have h := root_term_le_sqrt_div x 100 ((1 : Real) / (3 : Real))
      hxPos (by norm_num) hLower
    convert h using 1 <;> norm_num
  have hTenth : x ^ (1 / 10 : Real) <= Real.sqrt x / 256 := by
    have hLower := root_gap_lower x 256 2 5 hx (by norm_num) (by decide) (by norm_num)
    norm_num at hLower
    have h := root_term_le_sqrt_div x 256 ((2 : Real) / (5 : Real))
      hxPos (by norm_num) hLower
    convert h using 1 <;> norm_num
  have hNinth : x ^ (1 / 9 : Real) <= Real.sqrt x / 200 := by
    have hLower := root_gap_lower x 200 7 18 hx (by norm_num) (by decide) (by norm_num)
    norm_num at hLower
    have h := root_term_le_sqrt_div x 200 ((7 : Real) / (18 : Real))
      hxPos (by norm_num) hLower
    convert h using 1 <;> norm_num
  have hFifteenth : x ^ (1 / 15 : Real) <= Real.sqrt x / 400 := by
    have hLower := root_gap_lower x 400 13 30 hx (by norm_num) (by decide) (by norm_num)
    norm_num at hLower
    have h := root_term_le_sqrt_div x 400 ((13 : Real) / (30 : Real))
      hxPos (by norm_num) hLower
    convert h using 1 <;> norm_num
  have hTwentyFifth : x ^ (1 / 25 : Real) <= Real.sqrt x / 512 := by
    have hLower := root_gap_lower x 512 23 50 hx (by norm_num) (by decide) (by norm_num)
    norm_num at hLower
    have h := root_term_le_sqrt_div x 512 ((23 : Real) / (50 : Real))
      hxPos (by norm_num) hLower
    convert h using 1 <;> norm_num
  have hLogFourEq : Real.log (4 : Real) = 2 * Real.log (2 : Real) := by
    have h := Real.log_pow (2 : Real) 2
    norm_num at h
    exact h
  have hLogFour : Real.log 4 <= (10 / 7 : Real) := by
    rw [hLogFourEq]
    linarith only [log_two_le_five_sevenths]
  have hConstant : Real.log 4 + 4 <= (38 / 7 : Real) := by linarith only [hLogFour]
  have hLead : Real.sqrt x + x ^ (1 / 3 : Real) + x ^ (1 / 5 : Real) <=
      (1 + 1 / 10 + 1 / 64 : Real) * Real.sqrt x := by
    nlinarith only [hThird, hFifth]
  have hTail : x ^ (1 / 4 : Real) + 2 * x ^ (1 / 6 : Real) +
      2 * x ^ (1 / 10 : Real) + x ^ (1 / 9 : Real) +
      2 * x ^ (1 / 15 : Real) + x ^ (1 / 25 : Real) <=
        (1 / 32 + 2 / 100 + 2 / 256 + 1 / 200 + 2 / 400 + 1 / 512 : Real) * Real.sqrt x := by
    nlinarith only [hQuarter, hSixth, hTenth, hNinth, hFifteenth, hTwentyFifth]
  have hLeadNonneg : 0 <= Real.sqrt x + x ^ (1 / 3 : Real) + x ^ (1 / 5 : Real) := by positivity
  have hTailNonneg : 0 <= x ^ (1 / 4 : Real) + 2 * x ^ (1 / 6 : Real) +
      2 * x ^ (1 / 10 : Real) + x ^ (1 / 9 : Real) +
      2 * x ^ (1 / 15 : Real) + x ^ (1 / 25 : Real) := by positivity
  have hLeading := mul_le_mul hLogFour hLead hLeadNonneg (by norm_num : (0 : Real) <= 10 / 7)
  have hCorrection := mul_le_mul hConstant hTail hTailNonneg (by norm_num : (0 : Real) <= 38 / 7)
  have hScaled := mul_le_mul_of_nonneg_right primePower_mass_rational_allowance.le (Real.sqrt_nonneg x)
  have hMass := primePower_mass_flat x hxPos.le
  nlinarith only [hLeading, hCorrection, hScaled, hMass]

theorem primePower_linear_loss_explicit (M : Nat) (hM : 2 ^ 20 <= M) :
    4 * Real.sqrt (M : Real) * Real.log (M : Real) <=
      (15 / 256 : Real) * (M : Real) := by
  let v := Real.sqrt (Real.sqrt (M : Real))
  have hMPos : (0 : Real) < (M : Real) := by
    exact_mod_cast (by omega : 0 < M)
  have hSPos : 0 < Real.sqrt (M : Real) := Real.sqrt_pos.mpr hMPos
  have hvPos : 0 < v := Real.sqrt_pos.mpr hSPos
  have hv2 : v ^ 2 = Real.sqrt (M : Real) := Real.sq_sqrt hSPos.le
  have hv4 : v ^ 4 = (M : Real) := by
    calc
      _ = (v ^ 2) ^ 2 := by ring
      _ = _ := by rw [hv2, Real.sq_sqrt hMPos.le]
  have hBase : (32 : Real) ^ 4 <= v ^ 4 := by
    rw [hv4]
    exact_mod_cast hM
  have hv : (32 : Real) <= v := by
    rw [hv4] at hBase
    have hRoot := Real.sqrt_le_sqrt (Real.sqrt_le_sqrt hBase)
    have hFirst : Real.sqrt ((32 : Real) ^ 4) = (32 : Real) ^ 2 := by
      rw [show (32 : Real) ^ 4 = ((32 : Real) ^ 2) ^ 2 by ring,
        Real.sqrt_sq (by norm_num)]
    rw [hFirst, Real.sqrt_sq (by norm_num)] at hRoot
    exact hRoot
  let u := v / 32
  have hu : 1 <= u := by dsimp [u]; linarith only [hv]
  have huPos : 0 < u := lt_of_lt_of_le zero_lt_one hu
  have hLogU := Real.log_le_sub_one_of_pos huPos
  have hV : v = u * 2 ^ 5 := by dsimp [u]; norm_num
  have hLogM : Real.log (M : Real) = 4 * Real.log u + 20 * Real.log 2 := by
    rw [<- hv4, Real.log_pow, hV, Real.log_mul (ne_of_gt huPos) (by norm_num), Real.log_pow]
    ring
  have hBound : Real.log (M : Real) <= (100 / 7 : Real) * u := by
    have hTwo := log_two_le_five_sevenths
    rw [hLogM]
    nlinarith only [hLogU, hTwo, hu]
  have hVScaled := mul_le_mul_of_nonneg_right hv hvPos.le
  have hCoef : 4 * Real.log (M : Real) <=
      (15 / 256 : Real) * Real.sqrt (M : Real) := by
    rw [<- hv2]
    dsimp [u] at hBound
    nlinarith only [hBound, hVScaled, hvPos]
  have h := mul_le_mul_of_nonneg_left hCoef (Real.sqrt_nonneg (M : Real))
  nlinarith only [h, Real.sq_sqrt hMPos.le]

end PrimeFactorOscillations.LPF

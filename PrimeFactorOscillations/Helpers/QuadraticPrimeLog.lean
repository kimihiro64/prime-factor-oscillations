/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Definitions.QuadraticPrimeLaw
import PrimeFactorOscillations.Helpers.PrimeProfileTail

/-!
# Exact family logarithmic profiles and explicit tail constants

All primes at most N are in the prefix and every retained tail prime is
strictly greater than N. The convergent profile retains the finite exceptions.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.QuadraticPrimeLaw

open Filter

theorem weight_le (law : QuadraticPrimeLaw) (p : Nat.Primes) :
    law.weight p <= (law.nu + law.error) * primeProfileWeight (p : Nat) := by
  have hv := primeProfileWeight_nonneg (p : Nat)
  have hv1 := primeProfileWeight_le_one p
  have he := (abs_le.mp (law.quadratic_error p)).2
  have hsq : (primeProfileWeight (p : Nat)) ^ 2 <= primeProfileWeight (p : Nat) := by
    nlinarith
  have h := mul_le_mul_of_nonneg_left hsq law.error_nonneg
  nlinarith only [he, h]

theorem logTailConstant_nonneg (law : QuadraticPrimeLaw) (z : Real) (hz : 0 <= z) :
    0 <= law.logTailConstant z := by
  have hD := law.error_nonneg
  have hNu := law.nu_pos
  unfold logTailConstant
  positivity

theorem abs_logFactor_le (law : QuadraticPrimeLaw) (z : Real) (hz : 0 <= z)
    (p : Nat.Primes) :
    abs (law.logFactor z p) <=
      law.logTailConstant z * (primeProfileWeight (p : Nat)) ^ 2 := by
  let v := primeProfileWeight (p : Nat)
  let w := law.weight p
  have hv : 0 <= v := primeProfileWeight_nonneg _
  have hw : 0 <= w := law.weight_nonneg p
  have hD := law.error_nonneg
  have hNu := law.nu_pos
  have hM : 0 <= law.nu + law.error := add_nonneg law.nu_pos.le law.error_nonneg
  have hWeight : w <= (law.nu + law.error) * v := law.weight_le p
  have hSquare : (w * z) ^ 2 <= (law.nu + law.error) ^ 2 * v ^ 2 * z ^ 2 := by
    calc
      (w * z) ^ 2 <= ((law.nu + law.error) * v * z) ^ 2 := by gcongr
      _ = _ := by ring
  have hOne := Real.sub_log_one_add_bounds (w * z) (mul_nonneg hw hz)
  have hTwo := Real.sub_log_one_add_bounds v hv
  have hLow := mul_nonneg (mul_nonneg law.nu_pos.le hz) hTwo.1
  have hHigh := mul_le_mul_of_nonneg_left hTwo.2 (mul_nonneg law.nu_pos.le hz)
  have hE := abs_le.mp (law.quadratic_error p)
  have hELow := mul_le_mul_of_nonneg_right hE.1 hz
  have hEHigh := mul_le_mul_of_nonneg_right hE.2 hz
  have hPos1 : 0 <= z * law.error * v ^ 2 := by positivity
  have hPos2 : 0 <= law.nu * z * v ^ 2 := by positivity
  have hPos3 : 0 <= z ^ 2 * (law.nu + law.error) ^ 2 * v ^ 2 := by positivity
  change abs (Real.log (1 + w * z) - law.nu * z * Real.log (1 + v)) <=
    (z ^ 2 * (law.nu + law.error) ^ 2 / 2 + z * law.error + law.nu * z / 2) * v ^ 2
  change -(law.error * v ^ 2) * z <= (w - law.nu * v) * z at hELow
  change (w - law.nu * v) * z <= law.error * v ^ 2 * z at hEHigh
  apply abs_le.mpr
  constructor
  . nlinarith only [hOne.2, hLow, hSquare, hELow, hPos1, hPos2]
  . nlinarith only [hOne.1, hHigh, hEHigh, hPos1, hPos3]

theorem summable_logFactor (law : QuadraticPrimeLaw) (z : Real) (hz : 0 <= z) :
    Summable (law.logFactor z) := by
  apply (summable_primeProfileWeight_sq.mul_left (law.logTailConstant z)).of_norm_bounded
  intro p
  simpa only [Real.norm_eq_abs] using law.abs_logFactor_le z hz p

theorem logProfile_tail_bound (law : QuadraticPrimeLaw) (N : Nat) (hN : 1 <= N)
    (z : Real) (hz : 0 <= z) :
    abs (law.logProfile z - (primeProfilePrefixSet N).sum (law.logFactor z)) <=
      2 * law.logTailConstant z / N := by
  classical
  have hK := law.logTailConstant_nonneg z hz
  have hFinite (M : Nat) (hNM : N <= M) :
      abs ((primeProfilePrefixSet M).sum (law.logFactor z) -
        (primeProfilePrefixSet N).sum (law.logFactor z)) <=
          2 * law.logTailConstant z / N := by
    let s := primeProfilePrefixSet M \ primeProfilePrefixSet N
    have hTail := sum_primeProfileWeight_sq_tail_le s N hN (by
      intro p hp
      have hn := (Finset.mem_sdiff.mp hp).2
      exact Nat.lt_of_not_ge (fun h => hn ((mem_primeProfilePrefixSet p N).mpr h)))
    rw [<- Finset.sum_sdiff (monotone_primeProfilePrefixSet hNM), add_sub_cancel_right]
    calc
      abs (s.sum (law.logFactor z)) <= s.sum (fun p => abs (law.logFactor z p)) :=
        Finset.abs_sum_le_sum_abs _ _
      _ <= s.sum (fun p => law.logTailConstant z *
          (primeProfileWeight (p : Nat)) ^ 2) :=
        Finset.sum_le_sum (fun p _ => law.abs_logFactor_le z hz p)
      _ = law.logTailConstant z * s.sum (fun p => (primeProfileWeight (p : Nat)) ^ 2) :=
        (Finset.mul_sum _ _ _).symm
      _ <= law.logTailConstant z * (2 / (N : Real)) :=
        mul_le_mul_of_nonneg_left hTail hK
      _ = 2 * law.logTailConstant z / N := by ring
  have hLim := ((law.summable_logFactor z hz).hasSum.comp tendsto_primeProfilePrefixSet).sub_const
    ((primeProfilePrefixSet N).sum (law.logFactor z))
  exact le_of_tendsto hLim.abs (eventually_atTop.mpr (Exists.intro N hFinite))

theorem profile_pos (law : QuadraticPrimeLaw) (z : Real) : 0 < law.profile z :=
  Real.exp_pos _

theorem prefixProduct_pos (law : QuadraticPrimeLaw) (N : Nat) (z : Real)
    (hz : 0 <= z) : 0 < law.prefixProduct N z := by
  apply Finset.prod_pos
  intro p _
  have h := mul_nonneg (law.weight_nonneg p) hz
  linarith

end PrimeFactorOscillations.QuadraticPrimeLaw

/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.ModifiedLcmDefectScale

/-!
# Exact upper reciprocal-square band and its leading constant

The strict upper band is the difference of two convergent prime tails.
Its square-root cutoff and logarithmic scale give the leading constant sqrt(2).
-/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace PrimeFactorOscillations
open Filter Asymptotics

theorem primeReciprocalSquareTail_add_nat_prefix (N : Nat) :
    (Nat.primesLE N).sum (fun p => 1 / (p : Real) ^ (2 : Nat)) +
      primeReciprocalSquareTail N =
        tsum (fun p : Nat.Primes => 1 / (p : Real) ^ (2 : Nat)) := by
  have hSum := @Summable.sum_add_tsum_subtype_compl Real Nat.Primes _ _ _ _ _
    (fun p : Nat.Primes => 1 / (p : Real) ^ (2 : Nat))
    summable_prime_reciprocal_sq (primeProfilePrefixSet N)
  have hPred : (fun p : Nat.Primes => Not (Membership.mem (primeProfilePrefixSet N) p)) =
      (fun p : Nat.Primes => N < (p : Nat)) := by
    funext p
    apply propext
    exact (not_congr (mem_primeProfilePrefixSet p N)).trans not_le
  rw [hPred, primeProfilePrefix_sum_reciprocal_sq] at hSum
  have hSet : (Finset.Icc 0 N).filter Nat.Prime = Nat.primesLE N := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_Icc, Nat.zero_le, true_and, Nat.mem_primesLE]
  rw [hSet] at hSum
  exact hSum

theorem modifiedLcmUpperSquareSum_eq_tail_difference (N : Nat) :
    modifiedLcmUpperSquareSum N =
      primeReciprocalSquareTail (Nat.sqrt (2 * N)) - primeReciprocalSquareTail N := by
  have hY : Nat.sqrt (2 * N) <= N := by
    have h : Nat.sqrt (2 * N) < N + 1 := Nat.sqrt_lt'.mpr (by nlinarith)
    omega
  have hSub : Nat.primesLE (Nat.sqrt (2 * N)) <= Nat.primesLE N := by
    intro p hp
    exact Nat.mem_primesLE.mpr (And.intro ((Nat.le_of_mem_primesLE hp).trans hY)
      (Nat.prime_of_mem_primesLE hp))
  have hBand : (Nat.primesLE N).filter (fun p => 2 * N < p ^ 2) =
      (Nat.primesLE N) \ (Nat.primesLE (Nat.sqrt (2 * N))) := by
    ext p
    have hsqrt : p <= Nat.sqrt (2 * N) <-> p ^ 2 <= 2 * N := by
      simpa only [pow_two] using (Nat.le_sqrt (m := p) (n := 2 * N))
    simp only [Finset.mem_filter, Finset.mem_sdiff, Nat.mem_primesLE]
    constructor
    . intro h
      exact And.intro h.1 (fun hLow => (not_lt_of_ge (hsqrt.mp hLow.1)) h.2)
    . intro h
      refine And.intro h.1 (lt_of_not_ge ?_)
      intro hLow
      exact h.2 (And.intro (hsqrt.mpr hLow) h.1.2)
  have hSum := Finset.sum_sdiff (f := fun p : Nat => 1 / (p : Real) ^ (2 : Nat)) hSub
  have hN := primeReciprocalSquareTail_add_nat_prefix N
  have hRoot := primeReciprocalSquareTail_add_nat_prefix (Nat.sqrt (2 * N))
  unfold modifiedLcmUpperSquareSum
  rw [hBand]
  linarith only [hSum, hN, hRoot]

theorem tendsto_modifiedLcm_square_cutoff :
    Tendsto (fun N : Nat => Nat.sqrt (2 * N)) atTop atTop := by
  apply tendsto_atTop.2
  intro b
  filter_upwards [eventually_ge_atTop (b * b)] with N hN
  apply Nat.le_sqrt.mpr
  omega

theorem tendsto_modifiedLcm_square_cutoff_ratio :
    Tendsto (fun N : Nat => (Nat.sqrt (2 * N) : Real) / Real.sqrt (N : Real))
      atTop (nhds (Real.sqrt 2)) := by
  have hn : Tendsto (fun N : Nat => (N : Real)) atTop atTop := tendsto_natCast_atTop_atTop
  have hInv : Tendsto (fun N : Nat => 1 / Real.sqrt (N : Real)) atTop (nhds (0 : Real)) := by
    simpa only [Function.comp_def, one_div] using
      tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp hn)
  have hGap : Tendsto (fun N : Nat => Real.sqrt 2 -
      (Nat.sqrt (2 * N) : Real) / Real.sqrt (N : Real)) atTop (nhds (0 : Real)) := by
    apply squeeze_zero' ?_ ?_ hInv
    . filter_upwards [eventually_ge_atTop (1 : Nat)] with N hN
      have hx : (0 : Real) < N := by exact_mod_cast (show 0 < N by omega)
      have hRoot : Real.sqrt ((2 * N : Nat) : Real) =
          Real.sqrt 2 * Real.sqrt (N : Real) := by
        simp only [Nat.cast_mul, Nat.cast_ofNat, Real.sqrt_mul (by norm_num : (0 : Real) <= 2)]
      have hLow := (Real.nat_sqrt_le_real_sqrt (a := 2 * N))
      rw [hRoot] at hLow
      have hRatio := div_le_div_of_nonneg_right hLow (Real.sqrt_nonneg (N : Real))
      have hCancel : Real.sqrt 2 * Real.sqrt (N : Real) / Real.sqrt (N : Real) =
          Real.sqrt 2 := by field_simp [(Real.sqrt_pos.mpr hx).ne']
      rw [hCancel] at hRatio
      linarith
    . filter_upwards [eventually_ge_atTop (1 : Nat)] with N hN
      have hx : (0 : Real) < N := by exact_mod_cast (show 0 < N by omega)
      have hRoot : Real.sqrt ((2 * N : Nat) : Real) =
          Real.sqrt 2 * Real.sqrt (N : Real) := by
        simp only [Nat.cast_mul, Nat.cast_ofNat, Real.sqrt_mul (by norm_num : (0 : Real) <= 2)]
      have hUp := (Real.real_sqrt_lt_nat_sqrt_succ (a := 2 * N)).le
      rw [hRoot] at hUp
      have hDiv := div_le_div_of_nonneg_right hUp (Real.sqrt_nonneg (N : Real))
      have hCancel : Real.sqrt 2 * Real.sqrt (N : Real) / Real.sqrt (N : Real) =
          Real.sqrt 2 := by field_simp [(Real.sqrt_pos.mpr hx).ne']
      rw [hCancel, add_div] at hDiv
      linarith
  have h := (tendsto_const_nhds (x := Real.sqrt 2)).sub hGap
  simp only [sub_zero] at h
  apply h.congr'
  filter_upwards [] with N
  ring

theorem tendsto_modifiedLcm_square_cutoff_log_ratio :
    Tendsto (fun N : Nat => Real.log (Nat.sqrt (2 * N) : Real) / Real.log (N : Real))
      atTop (nhds (1 / 2 : Real)) := by
  have hn : Tendsto (fun N : Nat => (N : Real)) atTop atTop := tendsto_natCast_atTop_atTop
  have hSqrt2 : Not (Real.sqrt 2 = 0) := (Real.sqrt_pos.mpr (by norm_num : (0 : Real) < 2)).ne'
  have hLogRatio := (Real.continuousAt_log hSqrt2).tendsto.comp
    tendsto_modifiedLcm_square_cutoff_ratio
  have hInvLog := tendsto_inv_atTop_zero.comp (Real.tendsto_log_atTop.comp hn)
  have hSmall := hLogRatio.mul hInvLog
  simp only [mul_zero] at hSmall
  have h := (tendsto_const_nhds (x := (1 / 2 : Real))).add hSmall
  simp only [add_zero] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop (2 : Nat)] with N hN
  have hx : (0 : Real) < N := by exact_mod_cast (show 0 < N by omega)
  have hy : (0 : Real) < (Nat.sqrt (2 * N) : Real) := by
    exact_mod_cast (Nat.sqrt_pos.mpr (by omega : 0 < 2 * N))
  have hLogN : (1 : Real) < N := by exact_mod_cast (show 1 < N by omega)
  have hLogNe : Not (Real.log (N : Real) = 0) := (Real.log_pos hLogN).ne'
  have hSqrt : Not (Real.sqrt (N : Real) = 0) := (Real.sqrt_pos.mpr hx).ne'
  have hSqLog : 2 * Real.log (Real.sqrt (N : Real)) = Real.log (N : Real) := by
    have h := Real.log_pow (Real.sqrt (N : Real)) 2
    rw [Real.sq_sqrt hx.le] at h
    simpa only [Nat.cast_ofNat] using h.symm
  simp only [Function.comp_def]
  rw [Real.log_div hy.ne' hSqrt]
  field_simp
  nlinarith only [hSqLog]

theorem tendsto_modifiedLcm_upper_tail_scaled :
    Tendsto (fun N : Nat => primeReciprocalSquareTail (Nat.sqrt (2 * N)) *
      Real.sqrt (N : Real) * Real.log (N : Real)) atTop (nhds (Real.sqrt 2)) := by
  have hTail := tendsto_primeReciprocalSquareTail_scaled.comp tendsto_modifiedLcm_square_cutoff
  have hRoot := tendsto_modifiedLcm_square_cutoff_ratio
  have hLog := tendsto_modifiedLcm_square_cutoff_log_ratio
  have hs : Not (Real.sqrt 2 = 0) := (Real.sqrt_pos.mpr (by norm_num : (0 : Real) < 2)).ne'
  have h := (hTail.div hRoot hs).div hLog (by norm_num)
  have hConst : (1 / Real.sqrt 2) / (1 / 2 : Real) = Real.sqrt 2 := by
    field_simp
    nlinarith only [Real.sq_sqrt (by norm_num : (0 : Real) <= 2)]
  rw [hConst] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop (2 : Nat)] with N hN
  have hx : (0 : Real) < N := by exact_mod_cast (show 0 < N by omega)
  have hy : (0 : Real) < (Nat.sqrt (2 * N) : Real) := by
    exact_mod_cast (Nat.sqrt_pos.mpr (by omega : 0 < 2 * N))
  have hyOne : (1 : Real) < (Nat.sqrt (2 * N) : Real) := by
    have hTwo : 2 <= Nat.sqrt (2 * N) := Nat.le_sqrt.mpr (by omega)
    exact_mod_cast (show 1 < Nat.sqrt (2 * N) by omega)
  have hLogY := (Real.log_pos hyOne).ne'
  have hLogN : Not (Real.log (N : Real) = 0) :=
    (Real.log_pos (by exact_mod_cast (show 1 < N by omega))).ne'
  simp only [Function.comp_def, Pi.div_apply]
  field_simp [hy.ne', (Real.sqrt_pos.mpr hx).ne', hLogY, hLogN]

theorem tendsto_primeReciprocalSquareTail_sqrt_scaled :
    Tendsto (fun N : Nat => primeReciprocalSquareTail N *
      Real.sqrt (N : Real) * Real.log (N : Real)) atTop (nhds (0 : Real)) := by
  have hn : Tendsto (fun N : Nat => (N : Real)) atTop atTop := tendsto_natCast_atTop_atTop
  have hInv := tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp hn)
  have h := tendsto_primeReciprocalSquareTail_scaled.mul hInv
  simp only [mul_zero] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop (1 : Nat)] with N hN
  have hx : (0 : Real) < N := by exact_mod_cast (show 0 < N by omega)
  have hCancel : (N : Real) * Inv.inv (Real.sqrt (N : Real)) = Real.sqrt (N : Real) := by
    rw [<- div_eq_mul_inv]
    field_simp [(Real.sqrt_pos.mpr hx).ne']
    nlinarith only [Real.sq_sqrt hx.le]
  simp only [Function.comp_def]
  calc
    _ = primeReciprocalSquareTail N * ((N : Real) * Inv.inv (Real.sqrt (N : Real))) *
        Real.log (N : Real) := by ring
    _ = _ := by rw [hCancel]

theorem tendsto_modifiedLcmUpperSquareSum_scaled :
    Tendsto (fun N : Nat => modifiedLcmUpperSquareSum N *
      Real.sqrt (N : Real) * Real.log (N : Real)) atTop (nhds (Real.sqrt 2)) := by
  have h := tendsto_modifiedLcm_upper_tail_scaled.sub tendsto_primeReciprocalSquareTail_sqrt_scaled
  simp only [sub_zero] at h
  apply h.congr'
  filter_upwards [] with N
  rw [modifiedLcmUpperSquareSum_eq_tail_difference]
  ring

theorem tendsto_modifiedLcm_defect_scaled :
    Tendsto (fun N : Nat => lcmDefectSum (modifiedLcm N) *
      Real.sqrt (N : Real) * Real.log (N : Real)) atTop (nhds (Real.sqrt 2)) := by
  have h := tendsto_modifiedLcmSmallDefect_scaled.add tendsto_modifiedLcmUpperSquareSum_scaled
  simp only [zero_add] at h
  apply h.congr'
  filter_upwards [] with N
  rw [modifiedLcm_defect_exact_split]
  ring

end PrimeFactorOscillations

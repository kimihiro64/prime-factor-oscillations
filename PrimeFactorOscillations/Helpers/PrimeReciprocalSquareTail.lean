/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.PrimeProfileQuadraticTail
import PrimeFactorOscillations.Helpers.PrimeSquareThetaTail

/-!
# The prime reciprocal-square tail

Finite Abel summation, PNT and the existing Robin kernel give the exact
tail representation and leading constant one. Replacing p by p-1 costs
at most 4/N squared; all cutoff conventions and infinite sums are explicit.
-/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace PrimeFactorOscillations
open Filter MeasureTheory Set Robin1984

theorem summable_prime_reciprocal_sq :
    Summable (fun p : Nat.Primes => 1 / (p : Real) ^ (2 : Nat)) := by
  apply summable_primeProfileWeight_sq.of_norm_bounded
  intro p
  have hp : 2 <= (p : Nat) := p.property.two_le
  have hn : (0 : Real) < ((p : Nat) - 1 : Nat) := by
    exact_mod_cast (show 0 < (p : Nat) - 1 by omega)
  have hpn : (((p : Nat) - 1 : Nat) : Real) <= (p : Real) := by
    exact_mod_cast Nat.sub_le (p : Nat) 1
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  dsimp [primeProfileWeight]
  rw [div_pow, one_pow]
  exact one_div_le_one_div_of_le (sq_pos_of_pos hn) (by nlinarith)

theorem primeProfilePrefix_sum_reciprocal_sq (N : Nat) :
    (primeProfilePrefixSet N).sum (fun p : Nat.Primes => 1 / (p : Real) ^ (2 : Nat)) =
      ((Finset.Icc 0 N).filter Nat.Prime).sum (fun p => 1 / (p : Real) ^ (2 : Nat)) := by
  classical
  apply Finset.sum_bij (fun (p : Nat.Primes) _ => (p : Nat))
  . intro p hp
    exact Finset.mem_filter.mpr (And.intro
      (Finset.mem_Icc.mpr (And.intro (Nat.zero_le _) ((mem_primeProfilePrefixSet p N).mp hp)))
      p.property)
  . intro p hp q hq heq
    exact Nat.Primes.coe_nat_injective heq
  . intro n hn
    have hmem := Finset.mem_filter.mp hn
    let p : Nat.Primes := Subtype.mk n hmem.2
    have hp : Membership.mem (primeProfilePrefixSet N) p :=
      (mem_primeProfilePrefixSet p N).mpr (Finset.mem_Icc.mp hmem.1).2
    exact Exists.intro p (Exists.intro hp rfl)
  . intro p hp
    rfl

theorem theta_weight_two_eq_kernel (t : Real) (ht : 0 < t) :
    Chebyshev.theta t * robinRealWeight 2 t =
      Chebyshev.theta t * (1 + 2 * Real.log t) /
        (t ^ (3 : Nat) * (Real.log t) ^ (2 : Nat)) := by
  unfold robinRealWeight
  norm_num only [Nat.cast_ofNat]
  norm_num [Real.rpow_neg, Real.rpow_natCast, inv_pow]
  <;> ring

theorem primeProfilePrefix_sum_sq_abel (N : Nat) (hN : 2 <= N) :
    (primeProfilePrefixSet N).sum (fun p : Nat.Primes => 1 / (p : Real) ^ (2 : Nat)) =
      Chebyshev.theta (N : Real) / ((N : Real) ^ (2 : Nat) * Real.log (N : Real)) +
        intervalIntegral (fun t : Real => Chebyshev.theta t * robinRealWeight 2 t)
          2 (N : Real) volume := by
  have hn : (2 : Real) <= N := by exact_mod_cast hN
  have hAbel := Chebyshev.sum_prime_reciprocal_sq_eq_theta_div_add_integral hn
  rw [Nat.floor_natCast] at hAbel
  rw [primeProfilePrefix_sum_reciprocal_sq, hAbel]
  congr 1
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_of_le hn] at ht
  exact (theta_weight_two_eq_kernel t (by linarith [ht.1])).symm

theorem tendsto_theta_square_boundary_zero :
    Tendsto (fun N : Nat => Chebyshev.theta (N : Real) /
      ((N : Real) ^ (2 : Nat) * Real.log (N : Real))) atTop (nhds 0) := by
  have hn : Tendsto (fun N : Nat => (N : Real)) atTop atTop := tendsto_natCast_atTop_atTop
  have hR : Tendsto (fun x : Real => Chebyshev.theta x / x) atTop (nhds (1 : Real)) :=
    (Asymptotics.isEquivalent_iff_tendsto_one
      (eventually_ne_atTop (0 : Real))).mp primeProfile_theta_isEquivalent_id
  have hInv := tendsto_inv_atTop_zero.comp hn
  have hLog := tendsto_inv_atTop_zero.comp (Real.tendsto_log_atTop.comp hn)
  have h := ((hR.comp hn).mul hInv).mul hLog
  have ht : Tendsto (fun N : Nat => (Chebyshev.theta (N : Real) / (N : Real)) *
      Inv.inv (N : Real) * Inv.inv (Real.log (N : Real))) atTop (nhds 0) := by
    simpa only [Function.comp_def, mul_zero, zero_mul] using h
  apply ht.congr'
  filter_upwards [] with N
  ring

theorem tsum_prime_reciprocal_sq_eq_theta_integral :
    tsum (fun p : Nat.Primes => 1 / (p : Real) ^ (2 : Nat)) =
      primeSquareThetaTail 2 := by
  have hsum := summable_prime_reciprocal_sq.hasSum.comp tendsto_primeProfilePrefixSet
  have hInt := intervalIntegral_tendsto_integral_Ioi 2
    integrableOn_theta_weight_two
    (tendsto_natCast_atTop_atTop : Tendsto (fun N : Nat => (N : Real)) atTop atTop)
  have hLimit := tendsto_theta_square_boundary_zero.add hInt
  have hSame : Tendsto (fun N : Nat =>
      (primeProfilePrefixSet N).sum (fun p : Nat.Primes => 1 / (p : Real) ^ (2 : Nat)))
      atTop (nhds (primeSquareThetaTail 2)) := by
    apply (show Tendsto (fun N : Nat => Chebyshev.theta (N : Real) /
      ((N : Real) ^ (2 : Nat) * Real.log (N : Real)) +
      intervalIntegral (fun t : Real => Chebyshev.theta t * robinRealWeight 2 t)
        2 (N : Real) volume) atTop (nhds (primeSquareThetaTail 2)) from by
      simpa only [zero_add, primeSquareThetaTail] using hLimit).congr'
    filter_upwards [eventually_ge_atTop (2 : Nat)] with N hN
    exact (primeProfilePrefix_sum_sq_abel N hN).symm
  exact tendsto_nhds_unique hsum hSame

def primeReciprocalSquareTail (N : Nat) : Real :=
  tsum (fun p : {p : Nat.Primes // N < (p : Nat)} => 1 / (p.val : Real) ^ (2 : Nat))

theorem primeReciprocalSquareTail_eq_integral (N : Nat) (hN : 2 <= N) :
    primeReciprocalSquareTail N = primeSquareThetaTail (N : Real) -
      Chebyshev.theta (N : Real) / ((N : Real) ^ (2 : Nat) * Real.log (N : Real)) := by
  have hn : (2 : Real) <= N := by exact_mod_cast hN
  have hSum := @Summable.sum_add_tsum_subtype_compl Real Nat.Primes _ _ _ _ _
    (fun p : Nat.Primes => 1 / (p : Real) ^ (2 : Nat))
    summable_prime_reciprocal_sq (primeProfilePrefixSet N)
  have hPred : (fun p : Nat.Primes => Not (Membership.mem (primeProfilePrefixSet N) p)) =
      (fun p : Nat.Primes => N < (p : Nat)) := by
    funext p
    apply propext
    exact (not_congr (mem_primeProfilePrefixSet p N)).trans not_le
  rw [hPred, tsum_prime_reciprocal_sq_eq_theta_integral,
    primeProfilePrefix_sum_sq_abel N hN] at hSum
  have hsplit : intervalIntegral
      (fun t : Real => Chebyshev.theta t * robinRealWeight 2 t) 2 (N : Real) volume +
      primeSquareThetaTail (N : Real) = primeSquareThetaTail 2 := by
    unfold primeSquareThetaTail
    rw [intervalIntegral.integral_of_le hn, <- setIntegral_union
      Ioc_disjoint_Ioi_same measurableSet_Ioi
      (integrableOn_theta_weight_two.mono_set Ioc_subset_Ioi_self)
      (primeSquareThetaTail_integrable hn), Ioc_union_Ioi_eq_Ioi hn]
  change _ + primeReciprocalSquareTail N = _ at hSum
  linarith

theorem tendsto_primeReciprocalSquareTail_scaled :
    Tendsto (fun N : Nat => primeReciprocalSquareTail N *
      ((N : Real) * Real.log (N : Real))) atTop (nhds 1) := by
  have hn : Tendsto (fun N : Nat => (N : Real)) atTop atTop := tendsto_natCast_atTop_atTop
  have hR : Tendsto (fun x : Real => Chebyshev.theta x / x) atTop (nhds (1 : Real)) :=
    (Asymptotics.isEquivalent_iff_tendsto_one
      (eventually_ne_atTop (0 : Real))).mp primeProfile_theta_isEquivalent_id
  have h := (tendsto_primeSquareThetaTail_scaled.comp hn).sub (hR.comp hn)
  have ht : Tendsto (fun N : Nat => primeSquareThetaTail (N : Real) *
      ((N : Real) * Real.log (N : Real)) - Chebyshev.theta (N : Real) / (N : Real))
      atTop (nhds 1) := by
    simpa only [Function.comp_def, show (2 : Real) - 1 = 1 by norm_num] using h
  apply ht.congr'
  filter_upwards [eventually_ge_atTop (2 : Nat)] with N hN
  have hNR : (1 : Real) < N := by exact_mod_cast (show 1 < N by omega)
  have hn0 : Not ((N : Real) = 0) := (zero_lt_one.trans hNR).ne'
  have hl0 : Not (Real.log (N : Real) = 0) := (Real.log_pos hNR).ne'
  rw [primeReciprocalSquareTail_eq_integral N hN]
  field_simp

theorem primeProfileQuadraticTail_shift_bound (N : Nat) (hN : 1 <= N) :
    0 <= primeProfileQuadraticTail N - primeReciprocalSquareTail N /\
      primeProfileQuadraticTail N - primeReciprocalSquareTail N <=
        4 / (N : Real) ^ (2 : Nat) := by
  let T := {p : Nat.Primes // N < (p : Nat)}
  let a : T -> Real := fun p => primeProfileWeight (p.val : Nat)
  let b : T -> Real := fun p => 1 / (p.val : Real)
  have hn : (0 : Real) < N := by exact_mod_cast (show 0 < N by omega)
  have haSum : Summable (fun p : T => (a p) ^ (2 : Nat)) :=
    summable_primeProfileWeight_sq.subtype _
  have hbSum : Summable (fun p : T => (b p) ^ (2 : Nat)) := by
    simpa only [b, T, Function.comp_def, div_pow, one_pow] using summable_prime_reciprocal_sq.subtype (fun p => N < (p : Nat))
  have hDiffSum := haSum.sub hbSum
  have hPoint (p : T) : 0 <= (a p) ^ (2 : Nat) - (b p) ^ (2 : Nat) /\
      (a p) ^ (2 : Nat) - (b p) ^ (2 : Nat) <=
        (2 / (N : Real)) * (a p) ^ (2 : Nat) := by
    have hp2 := p.val.property.two_le
    have hpN := p.property
    have hp0 : (0 : Real) < (p.val : Real) := by exact_mod_cast p.val.property.pos
    have hp1 : (0 : Real) < (((p.val : Nat) - 1 : Nat) : Real) := by
      exact_mod_cast (show 0 < (p.val : Nat) - 1 by omega)
    have hcast : (((p.val : Nat) - 1 : Nat) : Real) = (p.val : Real) - 1 := by
      rw [Nat.cast_sub (by omega), Nat.cast_one]
    have ha0 : 0 <= a p := primeProfileWeight_nonneg _
    have hb0 : 0 <= b p := by dsimp [b]; positivity
    have hba : b p <= a p := by
      dsimp [a, b, primeProfileWeight]
      exact one_div_le_one_div_of_le hp1 (by exact_mod_cast Nat.sub_le (p.val : Nat) 1)
    have haN : a p <= 1 / (N : Real) := by
      dsimp [a, primeProfileWeight]
      exact one_div_le_one_div_of_le hn
        (by exact_mod_cast (show N <= (p.val : Nat) - 1 by omega))
    have hid : a p - b p = a p * b p := by
      dsimp [a, b, primeProfileWeight]
      rw [hcast]
      have hOne : Not ((p.val : Real) - 1 = 0) := by linarith
      field_simp
      <;> ring
    have hd : a p - b p <= (a p) ^ (2 : Nat) := by
      rw [hid]
      nlinarith [mul_le_mul_of_nonneg_left hba ha0]
    refine And.intro (by nlinarith) ?_
    calc
      _ = (a p - b p) * (a p + b p) := by ring
      _ <= (a p) ^ (2 : Nat) * (2 * a p) := mul_le_mul hd
        (by linarith) (by positivity) (sq_nonneg _)
      _ = (2 * a p) * (a p) ^ (2 : Nat) := by ring
      _ <= (2 * (1 / (N : Real))) * (a p) ^ (2 : Nat) :=
        mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)
      _ = _ := by ring
  have hId : primeProfileQuadraticTail N - primeReciprocalSquareTail N =
      tsum (fun p : T => (a p) ^ (2 : Nat) - (b p) ^ (2 : Nat)) := by
    rw [Summable.tsum_sub haSum hbSum]
    simp only [primeProfileQuadraticTail, primeReciprocalSquareTail, a, b, T, div_pow, one_pow]
  rw [hId]
  refine And.intro (tsum_nonneg (fun p => (hPoint p).1)) ?_
  calc
    _ <= tsum (fun p : T => (2 / (N : Real)) * (a p) ^ (2 : Nat)) :=
      Summable.tsum_le_tsum (fun p => (hPoint p).2) hDiffSum (haSum.mul_left _)
    _ = (2 / (N : Real)) * primeProfileQuadraticTail N := by rw [tsum_mul_left]; rfl
    _ <= (2 / (N : Real)) * (2 / (N : Real)) := mul_le_mul_of_nonneg_left
      (primeProfileQuadraticTail_bounds N hN).2 (by positivity)
    _ = _ := by ring

theorem tendsto_primeProfileQuadraticTail_scaled :
    Tendsto (fun N : Nat => primeProfileQuadraticTail N *
      ((N : Real) * Real.log (N : Real))) atTop (nhds 1) := by
  have hLog : Tendsto (fun N : Nat => Real.log (N : Real) / (N : Real))
      atTop (nhds 0) := by
    have h := (isLittleO_log_rpow_atTop (by norm_num : (0 : Real) < 1)).tendsto_div_nhds_zero
    simpa only [Real.rpow_one, Function.comp_def] using
      h.comp (tendsto_natCast_atTop_atTop : Tendsto (fun N : Nat => (N : Real)) atTop atTop)
  have hSmall : Tendsto (fun N : Nat => 4 * Real.log (N : Real) / (N : Real))
      atTop (nhds 0) := by simpa only [mul_div_assoc, mul_zero] using hLog.const_mul 4
  have hDiff : Tendsto (fun N : Nat =>
      (primeProfileQuadraticTail N - primeReciprocalSquareTail N) *
        ((N : Real) * Real.log (N : Real))) atTop (nhds 0) := by
    apply squeeze_zero_norm' (a := fun N : Nat => 4 * Real.log (N : Real) / (N : Real)) ?_ hSmall
    filter_upwards [eventually_ge_atTop (2 : Nat)] with N hN
    have hb := primeProfileQuadraticTail_shift_bound N (by omega)
    have hn : (1 : Real) < N := by exact_mod_cast (show 1 < N by omega)
    have hn0 : 0 < (N : Real) := zero_lt_one.trans hn
    have hl : 0 < Real.log (N : Real) := Real.log_pos hn
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hb.1 (mul_nonneg hn0.le hl.le))]
    calc
      _ <= (4 / (N : Real) ^ (2 : Nat)) * ((N : Real) * Real.log (N : Real)) :=
        mul_le_mul_of_nonneg_right hb.2 (mul_nonneg hn0.le hl.le)
      _ = _ := by field_simp
  have h := hDiff.add tendsto_primeReciprocalSquareTail_scaled
  apply (show Tendsto (fun N : Nat =>
      (primeProfileQuadraticTail N - primeReciprocalSquareTail N) *
        ((N : Real) * Real.log (N : Real)) +
        primeReciprocalSquareTail N * ((N : Real) * Real.log (N : Real)))
        atTop (nhds 1) from by simpa only [zero_add] using h).congr'
  filter_upwards [] with N
  ring


end PrimeFactorOscillations

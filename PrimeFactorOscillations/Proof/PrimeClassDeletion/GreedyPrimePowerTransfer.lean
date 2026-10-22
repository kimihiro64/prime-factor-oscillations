/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Proof.PrimeClassDeletion.GreedyPrimeNegativeArea

/-!
# The full power-scale deletion correction

The actual deleted mass and complete infinite integral are bounded jointly
from a literal count hypothesis. The loss as the exponent approaches one
is retained explicitly.
-/

set_option autoImplicit false
set_option Elab.async false

open Filter MeasureTheory
open PrimeFactorOscillations.PrimeClassSampling
open Robin1984

namespace PrimeFactorOscillations.PrimeClassDeletion

private theorem greedyDeletedPrimeClass_integrand_power_bound
    (a C t : Real) (hC : 0 <= C) (ht : 2 <= t) (hLog : 1 <= Real.log t)
    (hCount : ((primeClassPrefix greedyDeletedPrimeClass (Nat.floor t)).card : Real) <= C * t ^ a) :
    primeClassThetaReal greedyDeletedPrimeClass t * nicolasTailKernel t <=
      (2 * C) * t ^ (a - 2) := by
  have ht0 : 0 < t := by linarith only [ht]
  have hL : 0 < Real.log t := by linarith only [hLog]
  have hMass : primeClassThetaReal greedyDeletedPrimeClass t <= C * t ^ a * Real.log t :=
    (primeClassThetaReal_le_count_mul_log greedyDeletedPrimeClass t ht).trans
      (mul_le_mul_of_nonneg_right hCount hL.le)
  have hInv : 1 / Real.log t <= 1 := (div_le_one hL).mpr hLog
  have hPow : t ^ a / t ^ (2 : Nat) = t ^ (a - 2) := by
    rw [Real.rpow_sub ht0, Real.rpow_two]
  calc
    primeClassThetaReal greedyDeletedPrimeClass t * nicolasTailKernel t <=
        (C * t ^ a * Real.log t) * nicolasTailKernel t :=
      mul_le_mul_of_nonneg_right hMass (nicolasTailKernel_nonneg (by linarith only [ht]))
    _ = (C * (t ^ a / t ^ (2 : Nat))) * (1 + 1 / Real.log t) := by
      unfold nicolasTailKernel
      field_simp [hL.ne', ht0.ne']
    _ <= (C * (t ^ a / t ^ (2 : Nat))) * 2 := by
      apply mul_le_mul_of_nonneg_left (by linarith only [hInv])
      exact mul_nonneg hC (div_nonneg (Real.rpow_nonneg ht0.le a) (sq_nonneg t))
    _ = (2 * C) * t ^ (a - 2) := by rw [hPow]; ring

theorem greedyPrimeNicolasIntegral_power_transfer
    (a C x : Real) (ha : a < 1) (hC : 0 <= C)
    (hx : 2 <= x) (hLog : 1 <= Real.log x)
    (hCount : forall t : Real, x <= t ->
      ((primeClassPrefix greedyDeletedPrimeClass (Nat.floor t)).card : Real) <= C * t ^ a) :
    And (0 <= nicolasK x - greedyPrimeNicolasIntegral x)
      (nicolasK x - greedyPrimeNicolasIntegral x <=
        (2 * C) * x ^ (a - 1) / (1 - a)) := by
  have hx0 : 0 < x := by linarith only [hx]
  have hPower : IntegrableOn (fun t : Real => t ^ (a - 2)) (Set.Ioi x) :=
    integrableOn_Ioi_rpow_of_lt (by linarith only [ha]) hx0
  have hPowerTail : integral (volume.restrict (Set.Ioi x))
      (fun t : Real => t ^ (a - 2)) = x ^ (a - 1) / (1 - a) := by
    rw [integral_Ioi_rpow_of_lt (by linarith only [ha]) hx0]
    rw [show a - 2 + 1 = a - 1 by ring]
    simp only [show 1 - a = -(a - 1) by ring, div_neg, neg_div]
  have hDeleted := (greedyDeletedPrimeClass_nicolas_tail x (by linarith only [hx])).1
  have hUpper : integral (volume.restrict (Set.Ioi x))
      (fun t => primeClassThetaReal greedyDeletedPrimeClass t * nicolasTailKernel t) <=
        (2 * C) * x ^ (a - 1) / (1 - a) := by
    have h := integral_mono_ae hDeleted (hPower.const_mul (2 * C))
      (by
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        change x < t at ht
        exact greedyDeletedPrimeClass_integrand_power_bound a C t hC
          (hx.trans ht.le) ((Real.log_le_log hx0 ht.le).trans' hLog) (hCount t ht.le))
    rw [integral_const_mul, hPowerTail] at h
    simpa only [mul_div_assoc] using h
  have hLower : 0 <= integral (volume.restrict (Set.Ioi x))
      (fun t => primeClassThetaReal greedyDeletedPrimeClass t * nicolasTailKernel t) := by
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    change x < t at ht
    exact mul_nonneg (primeClassThetaReal_nonneg greedyDeletedPrimeClass t)
      (nicolasTailKernel_nonneg (by linarith only [hx, ht]))
  have hTransfer := greedyPrimeNicolasIntegral_transfer x hx
  exact And.intro (by linarith only [hTransfer, hLower])
    (by linarith only [hTransfer, hUpper])

private theorem loglog_difference_upper (A B : Real) (hA : 1 < A) (hB : 1 < B) :
    Real.log (Real.log A) - Real.log (Real.log B) <=
      (A - B) / (B * Real.log B) := by
  have hA0 : 0 < A := by linarith only [hA]
  have hB0 : 0 < B := by linarith only [hB]
  have hLA : 0 < Real.log A := Real.log_pos hA
  have hLB : 0 < Real.log B := Real.log_pos hB
  have hFirst := Real.log_le_sub_one_of_pos (div_pos hLA hLB)
  rw [Real.log_div hLA.ne' hLB.ne'] at hFirst
  have hSecond := Real.log_le_sub_one_of_pos (div_pos hA0 hB0)
  rw [Real.log_div hA0.ne' hB0.ne'] at hSecond
  have hScaled := div_le_div_of_nonneg_right hSecond hLB.le
  have hEq1 : Real.log A / Real.log B - 1 =
      (Real.log A - Real.log B) / Real.log B := by field_simp
  have hEq2 : (A / B - 1) / Real.log B = (A - B) / (B * Real.log B) := by
    field_simp
  rw [hEq1] at hFirst
  rw [hEq2] at hScaled
  exact hFirst.trans hScaled

private theorem greedyPrime_height_correction_upper (x : Real) (hx : 4 <= x)
    (hHalf : x / 2 <= primeClassThetaReal greedyPrimeClass x) :
    Real.log (Real.log (Chebyshev.theta x)) -
        Real.log (Real.log (primeClassThetaReal greedyPrimeClass x)) <=
      4 * (primeClassThetaReal greedyDeletedPrimeClass x / (x * Real.log x)) := by
  let A := Chebyshev.theta x
  let B := primeClassThetaReal greedyPrimeClass x
  let M := primeClassThetaReal greedyDeletedPrimeClass x
  have hx0 : 0 < x := by linarith only [hx]
  have hB : 1 < B := by dsimp only [B]; linarith only [hx, hHalf]
  have hB0 : 0 < B := by linarith only [hB]
  have hM : 0 <= M := primeClassThetaReal_nonneg greedyDeletedPrimeClass x
  have hPart : B + M = A := greedyPrimeClass_thetaReal_add_deleted x
  have hA : 1 < A := by linarith only [hB, hM, hPart]
  have hLx : 0 < Real.log x := Real.log_pos (by linarith only [hx])
  have hLB : 0 < Real.log B := Real.log_pos hB
  have hLog4 : Real.log (4 : Real) = 2 * Real.log (2 : Real) := by
    rw [show (4 : Real) = 2 * 2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
    ring
  have hLogLarge := Real.log_le_log (by norm_num : (0 : Real) < 4) hx
  rw [hLog4] at hLogLarge
  have hLogHalf : Real.log x / 2 <= Real.log B := by
    have h := Real.log_le_log (div_pos hx0 (by norm_num)) hHalf
    rw [Real.log_div hx0.ne' (by norm_num)] at h
    linarith only [h, hLogLarge]
  have hDen : x * Real.log x / 4 <= B * Real.log B := by
    have h := mul_le_mul hHalf hLogHalf (by linarith only [hLx]) hB0.le
    nlinarith only [h]
  have hLogBound := loglog_difference_upper A B hA hB
  have hMass : A - B = M := by linarith only [hPart]
  rw [hMass] at hLogBound
  apply hLogBound.trans
  calc
    M / (B * Real.log B) <= M / (x * Real.log x / 4) :=
      div_le_div_of_nonneg_left hM (by positivity) hDen
    _ = 4 * (M / (x * Real.log x)) := by field_simp

private theorem greedyDeletedPrimeClass_mertens_tail_le_reciprocal (x : Real) :
    -tsum (primeClassMertensTail greedyDeletedPrimeClass x) <=
      tsum (primeClassReciprocalTail greedyDeletedPrimeClass x) := by
  classical
  have hsR : Summable (primeClassReciprocalTail greedyDeletedPrimeClass x) := by
    apply Summable.of_norm_bounded_eventually_nat
      greedyDeletedPrimeClass_reciprocal_summable.norm
    filter_upwards with p
    dsimp only [primeClassReciprocalTail]
    split_ifs
    case pos => exact le_refl _
    case neg => simpa only [norm_zero] using norm_nonneg (classPowerWeight greedyDeletedPrimeClass 1 p)
  have hsT := (primeClassMertensTail_summable greedyDeletedPrimeClass x).neg
  have hPoint : forall p : Nat,
      -primeClassMertensTail greedyDeletedPrimeClass x p <=
        primeClassReciprocalTail greedyDeletedPrimeClass x p := by
    intro p
    by_cases h : And (Membership.mem greedyDeletedPrimeClass p) (x < (p : Real))
    case pos =>
      have hD := h.1
      change And (Nat.Prime p) (Not (greedyPrimeIndices (Nat.count Nat.Prime p))) at hD
      have hp0 : (0 : Real) < p := by exact_mod_cast hD.1.pos
      have hp2 : (2 : Real) <= p := by exact_mod_cast hD.1.two_le
      have hm := Mertens.M_eq_summand_bound p
      rw [abs_of_nonpos (mertensSummand_nonpos p)] at hm
      have hRat : 2 / (p : Real) ^ 2 <= 1 / (p : Real) := by
        calc
          2 / (p : Real) ^ 2 = (2 / (p : Real)) * (1 / (p : Real)) := by field_simp
          _ <= 1 * (1 / (p : Real)) :=
            mul_le_mul_of_nonneg_right ((div_le_one hp0).mpr hp2) (by positivity)
          _ = 1 / (p : Real) := one_mul _
      simp only [primeClassMertensTail, ite_eq_left h, primeClassReciprocalTail,
        ite_eq_left h.2, classPowerWeight, ite_eq_left (And.intro hD.1 h.1), Real.rpow_neg_one]
      simpa only [one_div] using hm.trans hRat
    case neg =>
      simp only [primeClassMertensTail, ite_eq_right h, neg_zero]
      dsimp only [primeClassReciprocalTail]
      split_ifs
      case pos => exact classPowerWeight_nonneg greedyDeletedPrimeClass 1 p
      case neg => exact le_refl 0
  have hSum := Summable.tsum_le_tsum hPoint hsT hsR
  rw [((primeClassMertensTail_summable greedyDeletedPrimeClass x).hasSum.neg).tsum_eq] at hSum
  exact hSum

theorem greedyPrimeCalibratedError_difference_le_four_integral_difference
    (x : Real) (hx : 4 <= x)
    (hHalf : x / 2 <= primeClassThetaReal greedyPrimeClass x) :
    nicolasLogMertensOscillation x - greedyPrimeCalibratedError x <=
      4 * (nicolasK x - greedyPrimeNicolasIntegral x) := by
  have hHeight := greedyPrime_height_correction_upper x hx hHalf
  have hTail := greedyPrimeMissingEulerTail_eq_reciprocal_sub_mertens x
  have hTailBound := greedyDeletedPrimeClass_mertens_tail_le_reciprocal x
  have hR : 0 <= tsum (primeClassReciprocalTail greedyDeletedPrimeClass x) := by
    apply tsum_nonneg
    intro p
    classical
    dsimp only [primeClassReciprocalTail]
    split_ifs
    case pos => exact classPowerWeight_nonneg greedyDeletedPrimeClass 1 p
    case neg => exact le_refl 0
  have hDiff := greedyPrimeCalibratedError_difference x (by linarith only [hx])
  have hTransfer := greedyPrimeNicolasIntegral_transfer x (by linarith only [hx])
  have hAbel := (greedyDeletedPrimeClass_nicolas_tail x (by linarith only [hx])).2
  rw [hAbel] at hTransfer
  linarith only [hHeight, hTail, hTailBound, hR, hDiff, hTransfer]

theorem greedyPrimeCalibratedError_power_transfer
    (a C x : Real) (ha : a < 1) (hC : 0 <= C)
    (hx : 4 <= x) (hLog : 1 <= Real.log x)
    (hHalf : x / 2 <= primeClassThetaReal greedyPrimeClass x)
    (hCount : forall t : Real, x <= t ->
      ((primeClassPrefix greedyDeletedPrimeClass (Nat.floor t)).card : Real) <= C * t ^ a) :
    nicolasLogMertensOscillation x - greedyPrimeCalibratedError x <=
      (8 * C) * x ^ (a - 1) / (1 - a) := by
  have hFour := greedyPrimeCalibratedError_difference_le_four_integral_difference x hx hHalf
  have hK := (greedyPrimeNicolasIntegral_power_transfer a C x ha hC
    (by linarith only [hx]) hLog hCount).2
  calc
    nicolasLogMertensOscillation x - greedyPrimeCalibratedError x <=
        4 * (nicolasK x - greedyPrimeNicolasIntegral x) := hFour
    _ <= 4 * ((2 * C) * x ^ (a - 1) / (1 - a)) :=
      mul_le_mul_of_nonneg_left hK (by norm_num)
    _ = (8 * C) * x ^ (a - 1) / (1 - a) := by ring

end PrimeFactorOscillations.PrimeClassDeletion

/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.PrimeClassSamplingGrowth

/-!
# Early class cardinality and the actual late reciprocal mass

Both estimates consume the already proved class power-sum provider. The
late reciprocal sum keeps its prime-class mask and p > 4R+2 restriction.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.PrimeClassSampling

open PrimeFactorOscillations.PrimeClassDecoder

theorem earlyPrimeClass_card_le
    (P : Set Nat) (sigma : Real) (hs0 : 0 <= sigma)
    (hsum : Summable (classPowerWeight P sigma)) (R : Nat) (hR : 1 <= R) :
    ((primeClassPrefix P (4 * R + 2)).card : Real) <=
      (6 : Real) ^ sigma * tsum (classPowerWeight P sigma) * (R : Real) ^ sigma := by
  classical
  have hRR : (1 : Real) <= (R : Real) := by exact_mod_cast hR
  have hpoint : forall p : Nat, Membership.mem (primeClassPrefix P (4 * R + 2)) p ->
      (1 : Real) <= (6 * (R : Real)) ^ sigma * (p : Real) ^ (-sigma) := by
    intro p hp
    have hIcc := Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1
    have hpPos : (0 : Real) < (p : Real) := by exact_mod_cast (by omega : 0 < p)
    have hpB : (p : Real) <= 4 * (R : Real) + 2 := by exact_mod_cast hIcc.2
    have hpMax : (p : Real) <= 6 * (R : Real) := by linarith
    have hpow := Real.rpow_le_rpow hpPos.le hpMax hs0
    have h := mul_le_mul_of_nonneg_right hpow (Real.rpow_nonneg hpPos.le (-sigma))
    have hid : (p : Real) ^ sigma * (p : Real) ^ (-sigma) = 1 := by
      rw [<- Real.rpow_add hpPos]
      simp only [add_neg_cancel, Real.rpow_zero]
    rwa [hid] at h
  calc
    _ = (primeClassPrefix P (4 * R + 2)).sum (fun _ => (1 : Real)) := by simp
    _ <= (primeClassPrefix P (4 * R + 2)).sum
        (fun p => (6 * (R : Real)) ^ sigma * (p : Real) ^ (-sigma)) :=
      Finset.sum_le_sum hpoint
    _ = (6 * (R : Real)) ^ sigma *
        (primeClassPrefix P (4 * R + 2)).sum (fun p => (p : Real) ^ (-sigma)) :=
      (Finset.mul_sum _ _ _).symm
    _ <= (6 * (R : Real)) ^ sigma * tsum (classPowerWeight P sigma) :=
      mul_le_mul_of_nonneg_left (primeClassPrefix_powerSum_le P sigma (4 * R + 2) hsum)
        (Real.rpow_nonneg (by positivity) sigma)
    _ = _ := by
      rw [Real.mul_rpow (by norm_num : (0 : Real) <= 6) (by positivity : (0 : Real) <= R)]
      ring

theorem latePrimeClass_reciprocal_mass_le
    (P : Set Nat) (sigma : Real) (hs1 : sigma <= 1)
    (hsum : Summable (classPowerWeight P sigma)) (R Y : Nat) (hR : 1 <= R) :
    ((primeClassPrefix P Y).filter (fun p => 4 * R + 2 < p)).sum
        (fun p => 1 / (p : Real)) <=
      (R : Real) ^ (sigma - 1) * tsum (classPowerWeight P sigma) := by
  classical
  have hRpos : (0 : Real) < (R : Real) := by exact_mod_cast (by omega : 0 < R)
  let T := (primeClassPrefix P Y).filter (fun p => 4 * R + 2 < p)
  have hpoint : forall p : Nat, Membership.mem T p ->
      1 / (p : Real) <= (R : Real) ^ (sigma - 1) * (p : Real) ^ (-sigma) := by
    intro p hp
    have hlate := (Finset.mem_filter.mp hp).2
    have hRp : (R : Real) <= (p : Real) := by exact_mod_cast (by omega : R <= p)
    have hpPos : (0 : Real) < (p : Real) := hRpos.trans_le hRp
    have hpow := Real.rpow_le_rpow hRpos.le hRp (sub_nonneg.mpr hs1)
    have hinv := div_le_div_of_nonneg_left (by norm_num : (0 : Real) <= 1)
      (Real.rpow_pos_of_pos hRpos (1 - sigma)) hpow
    have hexp : sigma - 1 = -(1 - sigma) := by ring
    have hneg : (p : Real) ^ (sigma - 1) <= (R : Real) ^ (sigma - 1) := by
      rw [hexp, Real.rpow_neg hpPos.le, Real.rpow_neg hRpos.le]
      simpa only [one_div] using hinv
    have hsplit : 1 / (p : Real) =
        (p : Real) ^ (sigma - 1) * (p : Real) ^ (-sigma) := by
      rw [<- Real.rpow_add hpPos]
      have hid : sigma - 1 + -sigma = (-1 : Real) := by ring
      rw [hid, Real.rpow_neg_one]
      simp only [one_div]
    rw [hsplit]
    exact mul_le_mul_of_nonneg_right hneg (Real.rpow_nonneg hpPos.le (-sigma))
  have hsumT : T.sum (fun p => (p : Real) ^ (-sigma)) <=
      tsum (classPowerWeight P sigma) := by
    apply le_trans _ (primeClassPrefix_powerSum_le P sigma Y hsum)
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    intro p _ _
    exact Real.rpow_nonneg (Nat.cast_nonneg p) _
  calc
    _ <= T.sum (fun p => (R : Real) ^ (sigma - 1) * (p : Real) ^ (-sigma)) :=
      Finset.sum_le_sum hpoint
    _ = (R : Real) ^ (sigma - 1) * T.sum (fun p => (p : Real) ^ (-sigma)) :=
      (Finset.mul_sum _ _ _).symm
    _ <= _ := mul_le_mul_of_nonneg_left hsumT (Real.rpow_nonneg hRpos.le _)

end PrimeFactorOscillations.PrimeClassSampling

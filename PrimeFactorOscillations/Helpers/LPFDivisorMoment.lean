/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.NormNum
import PrimeFactorOscillations.Helpers.LPFDivisorPower
import PrimeFactorOscillations.Helpers.LPFSingularSeries

/-!
# Uniform divisor moments and the complete weighted singular tail

The symbolic natural bound is converted before specializing K=320, giving
tau(n)^2 <= C*n^(1/160) with one constant for all n. Its finite sum consumer
controls the complete weighted tail by A*M^(481/160)/P whenever all positive
targets and the weights are bounded by M and there are at most M targets.
Thus P of order M^(1/40) yields exponent 477/160 on this packet. The minor
packet and the geometric-kernel estimate are separate remaining obligations.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.LPF

theorem lpfDivisorPowerConstant_pos (K : Nat) : 0 < lpfDivisorPowerConstant K := by
  unfold lpfDivisorPowerConstant
  exact pow_pos (Nat.mul_pos K.factorial_pos (pow_pos (by decide) K)) _

-- Keep K symbolic throughout cast and positivity tactics. Specialize only
-- the finished theorem; never normalize the enormous natural constant.
theorem exists_lpf_divisors_square_rpow_bound (K : Nat) (hK : 1 <= K) :
    exists C : Real, And (0 < C)
      (forall n : Nat, (n.divisors.card : Real) ^ 2 <= C * (n : Real) ^ (2 / (K : Real))) := by
  let B : Real := (lpfDivisorPowerConstant K : Real)
  have hB : 0 < B := Nat.cast_pos.mpr (lpfDivisorPowerConstant_pos K)
  have hKpos : (0 : Real) < (K : Real) := Nat.cast_pos.mpr (by omega)
  have hExponent : (0 : Real) <= 2 / (K : Real) := div_nonneg (by norm_num) hKpos.le
  refine Exists.intro (B ^ (2 / (K : Real))) (And.intro (Real.rpow_pos_of_pos hB _) ?_)
  intro n
  have hCast : (n.divisors.card : Real) ^ K <= B * (n : Real) := by
    have h : ((n.divisors.card ^ K : Nat) : Real) <=
        ((lpfDivisorPowerConstant K * n : Nat) : Real) :=
      Nat.cast_le.mpr (lpf_divisors_card_pow_le n K hK)
    simpa only [Nat.cast_pow, Nat.cast_mul] using h
  have hRoot := Real.rpow_le_rpow (pow_nonneg (Nat.cast_nonneg n.divisors.card) K) hCast hExponent
  have hCancel : (K : Real) * (2 / (K : Real)) = 2 := by field_simp
  have hLeft : ((n.divisors.card : Real) ^ K) ^ (2 / (K : Real)) = (n.divisors.card : Real) ^ 2 := by
    rw [<- Real.rpow_natCast, <- Real.rpow_mul (Nat.cast_nonneg n.divisors.card)]
    rw [hCancel, Real.rpow_two]
  rw [hLeft, Real.mul_rpow hB.le (Nat.cast_nonneg n)] at hRoot
  exact hRoot

theorem exists_lpf_divisors_square_power_bound :
    exists C : Real, And (0 < C)
      (forall n : Nat, (n.divisors.card : Real) ^ 2 <= C * (n : Real) ^ (1 / 160 : Real)) := by
  have h := exists_lpf_divisors_square_rpow_bound 320 (by decide)
  norm_num only [Nat.cast_ofNat] at h
  exact h

theorem lpf_divisors_square_sum_of_power_bound (C : Real)
    (hC : 0 <= C)
    (hPoint : forall n : Nat, (n.divisors.card : Real) ^ 2 <= C * (n : Real) ^ (1 / 160 : Real))
    (M : Nat) (T : Finset Nat) (hT : forall n, Membership.mem T n -> n <= M)
    (hCard : T.card <= M) :
    Finset.sum T (fun n => (n.divisors.card : Real) ^ 2) <= C * (M : Real) ^ (161 / 160 : Real) := by
  have hPointM : forall n, Membership.mem T n ->
      (n.divisors.card : Real) ^ 2 <= C * (M : Real) ^ (1 / 160 : Real) := by
    intro n hn
    exact (hPoint n).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (Nat.cast_nonneg n) (by exact_mod_cast hT n hn) (by norm_num)) hC)
  have hSum := Finset.sum_le_sum hPointM
  simp only [Finset.sum_const, nsmul_eq_mul] at hSum
  have hCount : (T.card : Real) <= (M : Real) := by exact_mod_cast hCard
  calc
    _ <= (T.card : Real) * (C * (M : Real) ^ (1 / 160 : Real)) := hSum
    _ <= (M : Real) * (C * (M : Real) ^ (1 / 160 : Real)) :=
      mul_le_mul_of_nonneg_right hCount (mul_nonneg hC (Real.rpow_nonneg (Nat.cast_nonneg M) _))
    _ = C * (M : Real) ^ (161 / 160 : Real) := by
      rw [show (161 / 160 : Real) = 1 + 1 / 160 by norm_num,
        Real.rpow_add' (Nat.cast_nonneg M) (by norm_num : Not ((1 : Real) + 1 / 160 = 0)), Real.rpow_one]
      ring

theorem lpfSingularSeries_tail_square_le (P t : Nat) (hP : 1 <= P) (ht : 0 < t) :
    norm (lpfSingularSeries t - lpfSingularPartial P t) ^ 2 <=
      256 * (t.divisors.card : Real) ^ 2 / (P : Real) := by
  have h := norm_lpfSingularSeries_sub_partial_le P t hP ht
  calc
    _ <= (16 * (t.divisors.card : Real) / Real.sqrt (P : Real)) ^ 2 := by gcongr
    _ = _ := by rw [div_pow, Real.sq_sqrt (Nat.cast_nonneg P)]; ring

theorem lpfSingularSeries_tail_square_sum (C : Real) (hC : 0 <= C)
    (hPoint : forall n : Nat, (n.divisors.card : Real) ^ 2 <= C * (n : Real) ^ (1 / 160 : Real))
    (M P : Nat) (T : Finset Nat) (hP : 1 <= P)
    (hT : forall t, Membership.mem T t -> And (0 < t) (t <= M)) (hCard : T.card <= M) :
    Finset.sum T (fun t => norm (lpfSingularSeries t - lpfSingularPartial P t) ^ 2) <=
      (256 * C / (P : Real)) * (M : Real) ^ (161 / 160 : Real) := by
  have hDiv : (0 : Real) <= 256 / (P : Real) := by positivity
  calc
    _ <= Finset.sum T (fun t => (256 / (P : Real)) * (t.divisors.card : Real) ^ 2) := by
      apply Finset.sum_le_sum
      intro t ht
      convert lpfSingularSeries_tail_square_le P t hP (hT t ht).1 using 1 <;> ring
    _ = (256 / (P : Real)) * Finset.sum T (fun t => (t.divisors.card : Real) ^ 2) :=
      (Finset.mul_sum _ _ _).symm
    _ <= (256 / (P : Real)) * (C * (M : Real) ^ (161 / 160 : Real)) :=
      mul_le_mul_of_nonneg_left (lpf_divisors_square_sum_of_power_bound C hC hPoint M T
        (fun t ht => (hT t ht).2) hCard) hDiv
    _ = _ := by ring

theorem lpfSingularSeries_weighted_tail_square_sum (C : Real) (hC : 0 <= C)
    (hPoint : forall n : Nat, (n.divisors.card : Real) ^ 2 <= C * (n : Real) ^ (1 / 160 : Real))
    (M P : Nat) (T : Finset Nat) (w : Nat -> Complex) (hP : 1 <= P)
    (hT : forall t, Membership.mem T t -> And (0 < t) (t <= M)) (hCard : T.card <= M)
    (hw : forall t, Membership.mem T t -> norm (w t) <= (M : Real)) :
    Finset.sum T (fun t => norm (w t * (lpfSingularSeries t - lpfSingularPartial P t)) ^ 2) <=
      (256 * C / (P : Real)) * (M : Real) ^ (481 / 160 : Real) := by
  have hBound := lpfSingularSeries_tail_square_sum C hC hPoint M P T hP hT hCard
  have hWeight : forall t, Membership.mem T t ->
      norm (w t * (lpfSingularSeries t - lpfSingularPartial P t)) ^ 2 <=
        (M : Real) ^ 2 * norm (lpfSingularSeries t - lpfSingularPartial P t) ^ 2 := by
    intro t ht
    rw [norm_mul, mul_pow]
    exact mul_le_mul_of_nonneg_right (by gcongr; exact hw t ht) (sq_nonneg _)
  calc
    _ <= Finset.sum T (fun t => (M : Real) ^ 2 * norm (lpfSingularSeries t - lpfSingularPartial P t) ^ 2) :=
      Finset.sum_le_sum hWeight
    _ = (M : Real) ^ 2 * Finset.sum T (fun t => norm (lpfSingularSeries t - lpfSingularPartial P t) ^ 2) :=
      (Finset.mul_sum _ _ _).symm
    _ <= (M : Real) ^ 2 * ((256 * C / (P : Real)) * (M : Real) ^ (161 / 160 : Real)) :=
      mul_le_mul_of_nonneg_left hBound (sq_nonneg _)
    _ = _ := by
      have hPower : (M : Real) ^ 2 * (M : Real) ^ (161 / 160 : Real) =
          (M : Real) ^ (481 / 160 : Real) := by
        rw [<- Real.rpow_natCast]
        norm_num only [Nat.cast_ofNat]
        rw [<- Real.rpow_add' (Nat.cast_nonneg M) (by norm_num : Not ((2 : Real) + 161 / 160 = 0))]
        norm_num
      calc
        _ = (256 * C / (P : Real)) * ((M : Real) ^ 2 * (M : Real) ^ (161 / 160 : Real)) := by ring
        _ = _ := by rw [hPower]

theorem exists_lpfSingularSeries_weighted_tail_square_sum :
    exists A : Real, And (0 < A)
      (forall (M P : Nat) (T : Finset Nat) (w : Nat -> Complex), 1 <= P ->
        (forall t, Membership.mem T t -> And (0 < t) (t <= M)) -> T.card <= M ->
        (forall t, Membership.mem T t -> norm (w t) <= (M : Real)) ->
        Finset.sum T (fun t => norm (w t * (lpfSingularSeries t - lpfSingularPartial P t)) ^ 2) <=
          A * (M : Real) ^ (481 / 160 : Real) / (P : Real)) := by
  choose C hC hPoint using exists_lpf_divisors_square_power_bound
  refine Exists.intro (256 * C) (And.intro (mul_pos (by norm_num) hC) ?_)
  intro M P T w hP hT hCard hw
  convert lpfSingularSeries_weighted_tail_square_sum C hC.le hPoint M P T w hP hT hCard hw using 1 <;> ring

end PrimeFactorOscillations.LPF

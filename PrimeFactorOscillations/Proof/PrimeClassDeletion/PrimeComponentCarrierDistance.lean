/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Proof.PrimeClassDeletion.PrimeComponentCarrierNorm
import PrimeFactorOscillations.Proof.PrimeClassDeletion.PrimePowerComponentOverlap

/-!
# Exact geometry of multiplicative prime-component inverses

The common Mobius sign permits an exact distance calculation. For nested
prime classes the distance is exactly the difference of their Euler budgets.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.PrimeClassSampling

theorem classPowerWeight_summable_subset
    (P Q : Set Nat)
    (hPQ : forall p : Nat, Membership.mem P p -> Membership.mem Q p)
    (sigma : Real) (hQ : Summable (classPowerWeight Q sigma)) :
    Summable (classPowerWeight P sigma) := by
  classical
  apply Summable.of_nonneg_of_le (classPowerWeight_nonneg P sigma) ?_ hQ
  intro p
  by_cases hp : And (Nat.Prime p) (Membership.mem P p)
  . have hq := And.intro hp.1 (hPQ p hp.2)
    simp only [classPowerWeight, ite_eq_left hp, ite_eq_left hq, le_refl]
  . have hz : classPowerWeight P sigma p = 0 := by
      simp only [classPowerWeight, ite_eq_right hp]
    rw [hz]
    exact classPowerWeight_nonneg Q sigma p

theorem classPrimePowerPartition_mono
    (P Q : Set Nat)
    (hPQ : forall p : Nat, Membership.mem P p -> Membership.mem Q p)
    (sigma : Real) (hs : 0 < sigma)
    (hP : Summable (classPowerWeight P sigma))
    (hQ : Summable (classPowerWeight Q sigma)) :
    classPrimePowerPartition P sigma <= classPrimePowerPartition Q sigma := by
  exact Summable.tsum_le_tsum (classPrimePowerWeight_mono P Q hPQ sigma)
    (classPrimePowerWeight_summable P sigma hs hP)
    (classPrimePowerWeight_summable Q sigma hs hQ)

private theorem abs_sub_eq_sum_sub_twice_min (a b : Real) :
    abs (a - b) = a + b - 2 * min a b := by
  by_cases h : a <= b
  . rw [min_eq_left h, abs_of_nonpos (sub_nonpos.mpr h)]
    ring
  . have h' : b <= a := le_of_lt (lt_of_not_ge h)
    rw [min_eq_right h', abs_of_nonneg (sub_nonneg.mpr h')]
    ring

theorem classPrimeComponentInverse_distance_apply
    (P Q : Set Nat) (sigma : Real) (hs : 0 < sigma)
    (hP : Summable (classPowerWeight P sigma))
    (hQ : Summable (classPowerWeight Q sigma)) (n : Nat) :
    norm (classPrimeComponentInverseArithmetic P sigma n -
      classPrimeComponentInverseArithmetic Q sigma n) =
        norm (classPrimeComponentInverseArithmetic P sigma n) +
        norm (classPrimeComponentInverseArithmetic Q sigma n) -
        (2 * min (classPrimePowerPartition P sigma)
          (classPrimePowerPartition Q sigma)) *
            classPrimeComponentAbsMobiusArithmetic (Set.inter P Q) sigma n := by
  classical
  have hZP : 0 <= classPrimePowerPartition P sigma :=
    (classPrimePowerWeight_tsum_pos P sigma hs hP).le
  have hZQ : 0 <= classPrimePowerPartition Q sigma :=
    (classPrimePowerWeight_tsum_pos Q sigma hs hQ).le
  rw [classPrimeComponentInverseArithmetic_norm P sigma hs hP,
    classPrimeComponentInverseArithmetic_norm Q sigma hs hQ]
  simp only [classPrimeComponentAbsMobiusArithmetic_apply]
  rw [classPrimeComponentInverseArithmetic_apply,
    classPrimeComponentInverseArithmetic_apply]
  by_cases hp : classPrimePowerSupported P n
  . by_cases hq : classPrimePowerSupported Q n
    . have hi := (classPrimePowerSupported_inter P Q n).mpr (And.intro hp hq)
      have hwP : classPrimePowerWeight P sigma n = (n : Real) ^ (-sigma) := by
        simp only [classPrimePowerWeight, ite_eq_left hp]
      have hwQ : classPrimePowerWeight Q sigma n = (n : Real) ^ (-sigma) := by
        simp only [classPrimePowerWeight, ite_eq_left hq]
      have hwI : classPrimePowerWeight (Set.inter P Q) sigma n =
          (n : Real) ^ (-sigma) := by
        simp only [classPrimePowerWeight, ite_eq_left hi]
      rw [hwP, hwQ, hwI]
      have hc : 0 <= (n : Real) ^ (-sigma) := Real.rpow_nonneg (Nat.cast_nonneg n) _
      have heq :
          classPrimePowerPartition P sigma * (ArithmeticFunction.moebius n : Real) *
              (n : Real) ^ (-sigma) -
            classPrimePowerPartition Q sigma * (ArithmeticFunction.moebius n : Real) *
              (n : Real) ^ (-sigma) =
          (classPrimePowerPartition P sigma - classPrimePowerPartition Q sigma) *
            (ArithmeticFunction.moebius n : Real) * (n : Real) ^ (-sigma) := by ring
      rw [heq, Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hc,
        abs_sub_eq_sum_sub_twice_min]
      ring
    . have hi : Not (classPrimePowerSupported (Set.inter P Q) n) :=
        fun h => hq ((classPrimePowerSupported_inter P Q n).mp h).2
      have hwQ : classPrimePowerWeight Q sigma n = 0 := by
        simp only [classPrimePowerWeight, ite_eq_right hq]
      have hwI : classPrimePowerWeight (Set.inter P Q) sigma n = 0 := by
        simp only [classPrimePowerWeight, ite_eq_right hi]
      rw [hwQ, hwI]
      simp only [mul_zero, sub_zero, add_zero]
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hZP,
        abs_of_nonneg (classPrimePowerWeight_nonneg P sigma n)]
      ring
  . have hi : Not (classPrimePowerSupported (Set.inter P Q) n) :=
      fun h => hp ((classPrimePowerSupported_inter P Q n).mp h).1
    have hwP : classPrimePowerWeight P sigma n = 0 := by
      simp only [classPrimePowerWeight, ite_eq_right hp]
    have hwI : classPrimePowerWeight (Set.inter P Q) sigma n = 0 := by
      simp only [classPrimePowerWeight, ite_eq_right hi]
    rw [hwP, hwI]
    simp only [mul_zero, zero_sub, zero_add, sub_zero]
    rw [norm_neg, Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hZQ,
      abs_of_nonneg (classPrimePowerWeight_nonneg Q sigma n)]
    ring

theorem classPrimeComponentAbsMobius_tsum_eq_budget_div_partition
    (P : Set Nat) (sigma : Real) (hs : 0 < sigma)
    (hP : Summable (classPowerWeight P sigma)) :
    tsum (classPrimeComponentAbsMobiusArithmetic P sigma) =
      classPrimePowerErrorConstant P sigma / classPrimePowerPartition P sigma := by
  have hZ : Not (classPrimePowerPartition P sigma = 0) :=
    ne_of_gt (classPrimePowerWeight_tsum_pos P sigma hs hP)
  have hnorm := classPrimeComponentInverseArithmetic_tsum_norm P sigma hs hP
  simp_rw [classPrimeComponentInverseArithmetic_norm P sigma hs hP] at hnorm
  rw [tsum_mul_left] at hnorm
  apply (eq_div_iff hZ).mpr
  rw [mul_comm]
  exact hnorm

theorem classPrimeComponentInverse_distance_hasSum
    (P Q : Set Nat) (sigma : Real) (hs : 0 < sigma)
    (hP : Summable (classPowerWeight P sigma))
    (hQ : Summable (classPowerWeight Q sigma)) :
    HasSum (fun n : Nat => norm (classPrimeComponentInverseArithmetic P sigma n -
      classPrimeComponentInverseArithmetic Q sigma n))
      (classPrimePowerErrorConstant P sigma + classPrimePowerErrorConstant Q sigma -
        (2 * min (classPrimePowerPartition P sigma)
          (classPrimePowerPartition Q sigma)) *
            (classPrimePowerErrorConstant (Set.inter P Q) sigma /
              classPrimePowerPartition (Set.inter P Q) sigma)) := by
  have hI := classPowerWeight_summable_subset (Set.inter P Q) P
    (fun p hp => hp.1) sigma hP
  have hNP := classPrimeComponentInverseArithmetic_norm_summable P sigma hs hP
  have hNQ := classPrimeComponentInverseArithmetic_norm_summable Q sigma hs hQ
  have hNI := classPrimeComponentAbsMobiusArithmetic_summable (Set.inter P Q) sigma hs hI
  have hseries := (hNP.hasSum.add hNQ.hasSum).sub
    (hNI.hasSum.mul_left (2 * min (classPrimePowerPartition P sigma)
      (classPrimePowerPartition Q sigma)))
  have hfun : (fun n : Nat => norm (classPrimeComponentInverseArithmetic P sigma n -
      classPrimeComponentInverseArithmetic Q sigma n)) =
      (fun n : Nat => norm (classPrimeComponentInverseArithmetic P sigma n) +
        norm (classPrimeComponentInverseArithmetic Q sigma n) -
        (2 * min (classPrimePowerPartition P sigma)
          (classPrimePowerPartition Q sigma)) *
            classPrimeComponentAbsMobiusArithmetic (Set.inter P Q) sigma n) :=
    funext (classPrimeComponentInverse_distance_apply P Q sigma hs hP hQ)
  rw [classPrimeComponentInverseArithmetic_tsum_norm P sigma hs hP,
    classPrimeComponentInverseArithmetic_tsum_norm Q sigma hs hQ,
    classPrimeComponentAbsMobius_tsum_eq_budget_div_partition (Set.inter P Q) sigma hs hI]
    at hseries
  rw [hfun]
  exact hseries

theorem classPrimeComponentInverse_l1_distance
    (P Q : Set Nat) (sigma : Real) (hs : 0 < sigma)
    (hP : Summable (classPowerWeight P sigma))
    (hQ : Summable (classPowerWeight Q sigma)) :
    tsum (fun n : Nat => norm (classPrimeComponentInverseArithmetic P sigma n -
      classPrimeComponentInverseArithmetic Q sigma n)) =
      classPrimePowerErrorConstant P sigma + classPrimePowerErrorConstant Q sigma -
        (2 * min (classPrimePowerPartition P sigma)
          (classPrimePowerPartition Q sigma)) *
            (classPrimePowerErrorConstant (Set.inter P Q) sigma /
              classPrimePowerPartition (Set.inter P Q) sigma) :=
  (classPrimeComponentInverse_distance_hasSum P Q sigma hs hP hQ).tsum_eq

theorem classPrimeComponentInverse_l1_distance_of_subset
    (P Q : Set Nat)
    (hPQ : forall p : Nat, Membership.mem P p -> Membership.mem Q p)
    (sigma : Real) (hs : 0 < sigma)
    (hP : Summable (classPowerWeight P sigma))
    (hQ : Summable (classPowerWeight Q sigma)) :
    tsum (fun n : Nat => norm (classPrimeComponentInverseArithmetic P sigma n -
      classPrimeComponentInverseArithmetic Q sigma n)) =
        classPrimePowerErrorConstant Q sigma - classPrimePowerErrorConstant P sigma := by
  have hi : Set.inter P Q = P := by
    ext p
    exact Iff.intro (fun h => h.1) (fun h => And.intro h (hPQ p h))
  have hZ := classPrimePowerPartition_mono P Q hPQ sigma hs hP hQ
  have hZP : Not (classPrimePowerPartition P sigma = 0) :=
    ne_of_gt (classPrimePowerWeight_tsum_pos P sigma hs hP)
  rw [classPrimeComponentInverse_l1_distance P Q sigma hs hP hQ, hi, min_eq_left hZ]
  field_simp [hZP]
  <;> ring

end PrimeFactorOscillations.PrimeClassSampling

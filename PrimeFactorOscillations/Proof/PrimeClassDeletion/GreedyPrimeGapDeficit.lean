/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Proof.PrimeClassDeletion.GreedyPrimeEulerTailBound

/-!
# The geometric supplies for the selected Nicolas integral

The literal cap bounds the number of relevant selected jumps. Away from
their short forward intervals it gives a definite theta deficit.
-/

set_option autoImplicit false
set_option Elab.async false

open PrimeFactorOscillations.PrimeClassSampling
open Robin1984

namespace PrimeFactorOscillations.PrimeClassDeletion

theorem primeClassThetaReal_eq_of_no_selected_prime
    (P : Set Nat) (a b : Real) (ha : 0 <= a) (hab : a <= b)
    (hgap : forall p : Nat, Nat.Prime p -> Membership.mem P p ->
      a < (p : Real) -> (p : Real) <= b -> False) :
    primeClassThetaReal P b = primeClassThetaReal P a := by
  classical
  have hPrefix : primeClassPrefix P (Nat.floor b) = primeClassPrefix P (Nat.floor a) := by
    apply Finset.ext
    intro p
    constructor
    case mp =>
      intro hp
      have hm := (primeClassPrefix_mem_iff P (Nat.floor b) p).mp hp
      have hpb : (p : Real) <= b :=
        (Nat.cast_le.mpr hm.2.1).trans (Nat.floor_le (ha.trans hab))
      have hpa : (p : Real) <= a := by
        by_contra h
        exact hgap p hm.2.2.1 hm.2.2.2 (lt_of_not_ge h) hpb
      exact (primeClassPrefix_mem_iff P (Nat.floor a) p).mpr
        (And.intro hm.1 (And.intro (Nat.le_floor hpa) hm.2.2))
    case mpr =>
      intro hp
      have hm := (primeClassPrefix_mem_iff P (Nat.floor a) p).mp hp
      exact (primeClassPrefix_mem_iff P (Nat.floor b) p).mpr
        (And.intro hm.1 (And.intro (hm.2.1.trans (Nat.floor_mono hab)) hm.2.2))
  change (primeClassPrefix P (Nat.floor b)).sum (fun p => Real.log (p : Real)) =
    (primeClassPrefix P (Nat.floor a)).sum (fun p => Real.log (p : Real))
  rw [hPrefix]

theorem greedyPrimeClass_deficit_of_no_selected_prime
    (t h : Real) (ht : 0 <= t - h)
    (hgap : forall p : Nat, Nat.Prime p -> Membership.mem greedyPrimeClass p ->
      t - h < (p : Real) -> (p : Real) <= t -> False)
    (hh : 0 <= h) :
    h <= t - primeClassThetaReal greedyPrimeClass t := by
  have hEq := primeClassThetaReal_eq_of_no_selected_prime greedyPrimeClass
    (t - h) t ht (by linarith only [hh]) hgap
  rw [hEq]
  have hCap := greedyPrimeClass_thetaReal_le (t - h) ht
  linarith only [hCap]

noncomputable def greedyPrimeAreaPrimes (x : Real) : Finset Nat := by
  classical
  exact (primeClassPrefix greedyPrimeClass (Nat.floor (2 * x))).filter
    (fun p => x / 2 <= (p : Real))

theorem greedyPrimeAreaPrimes_log_budget (x : Real) (hx : 4 <= x) :
    ((greedyPrimeAreaPrimes x).card : Real) * Real.log x <= 4 * x := by
  classical
  have hx0 : 0 < x := by linarith only [hx]
  have hLog4 : Real.log (4 : Real) = 2 * Real.log (2 : Real) := by
    rw [show (4 : Real) = 2 * 2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
    ring
  have hLarge := Real.log_le_log (by norm_num : (0 : Real) < 4) hx
  rw [hLog4] at hLarge
  have hTerm : forall p, Membership.mem (greedyPrimeAreaPrimes x) p ->
      Real.log x / 2 <= Real.log (p : Real) := by
    intro p hp
    have hm := Finset.mem_filter.mp hp
    have hLog := Real.log_le_log (div_pos hx0 (by norm_num)) hm.2
    rw [Real.log_div hx0.ne' (by norm_num)] at hLog
    linarith only [hLog, hLarge]
  have hMass : ((greedyPrimeAreaPrimes x).card : Real) * (Real.log x / 2) <= 2 * x := by
    calc
      ((greedyPrimeAreaPrimes x).card : Real) * (Real.log x / 2) =
          (greedyPrimeAreaPrimes x).sum (fun _ => Real.log x / 2) := by
        simp only [Finset.sum_const, nsmul_eq_mul]
      _ <= (greedyPrimeAreaPrimes x).sum (fun p => Real.log (p : Real)) :=
        Finset.sum_le_sum (fun p hp => hTerm p hp)
      _ <= (primeClassPrefix greedyPrimeClass (Nat.floor (2 * x))).sum
          (fun p => Real.log (p : Real)) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
          (fun p hp => (Finset.mem_filter.mp hp).1)
        intro p hp _
        have hm := (primeClassPrefix_mem_iff greedyPrimeClass (Nat.floor (2 * x)) p).mp hp
        exact Real.log_nonneg (by exact_mod_cast (show 1 <= p by omega))
      _ <= 2 * x := greedyPrimeClass_thetaReal_le (2 * x) (by linarith only [hx])
  linarith only [hMass]

theorem nicolasTailKernel_dyadic_lower (x t : Real) (hx : 4 <= x)
    (ht : And (x <= t) (t <= 2 * x)) :
    1 / (8 * x ^ 2 * Real.log x) <= nicolasTailKernel t := by
  have hx0 : 0 < x := by linarith only [hx]
  have ht0 : 0 < t := hx0.trans_le ht.1
  have hLx : 0 < Real.log x := Real.log_pos (by linarith only [hx])
  have hLt : 0 < Real.log t := Real.log_pos (by linarith only [hx, ht.1])
  have hLog2 : Real.log (2 : Real) <= Real.log x :=
    Real.log_le_log (by norm_num) (by linarith only [hx])
  have hLogT := Real.log_le_log ht0 ht.2
  rw [Real.log_mul (by norm_num) hx0.ne'] at hLogT
  have hSquare : t ^ 2 <= 4 * x ^ 2 := by
    have h := mul_self_le_mul_self ht0.le ht.2
    nlinarith only [h]
  have hDen : t ^ 2 * Real.log t <= 8 * x ^ 2 * Real.log x := by
    have h := mul_le_mul hSquare (show Real.log t <= 2 * Real.log x by
      linarith only [hLogT, hLog2]) hLt.le (by positivity : (0 : Real) <= 4 * x ^ 2)
    nlinarith only [h]
  calc
    1 / (8 * x ^ 2 * Real.log x) <= 1 / (t ^ 2 * Real.log t) :=
      div_le_div_of_nonneg_left (by norm_num) (mul_pos (pow_pos ht0 2) hLt) hDen
    _ = (1 / Real.log t) / t ^ 2 := by
      field_simp
    _ <= nicolasTailKernel t := by
      apply div_le_div_of_nonneg_right _ (sq_nonneg t)
      have h : 0 <= 1 / (Real.log t) ^ 2 := by positivity
      linarith only [h]

end PrimeFactorOscillations.PrimeClassDeletion

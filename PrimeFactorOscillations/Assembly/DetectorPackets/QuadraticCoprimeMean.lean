/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Assembly.DetectorPackets.IntegerQuadraticMask
import PrimeFactorOscillations.Assembly.DetectorPackets.IntegerQuadraticSieve

/-!
# QuadraticCoprimeMean

Maintained extraction of completed detector/packet proof components.
All original theorem hypotheses and retained proof bodies are preserved.
This module alone asserts no improved zero-free boundary.
-/

set_option autoImplicit false
set_option Elab.async false

/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described by LICENSE.
Authors: Prime Factor Oscillations contributors
-/


noncomputable section
open scoped BigOperators Classical

namespace PrimeFactorOscillations.QuadraticCoprimeMean

open QuadraticCarrierPacket IntegerQuadraticSieve IntegerQuadraticMask

theorem finite_coprime_mask (N n m : Nat) (hm : 0 < m) (hmN : m <= N) :
    (if Nat.Coprime n m then (1 : Complex) else 0) =
      (Finset.Ioc 0 N).sum (fun d => (ArithmeticFunction.moebius d : Complex) *
        (if Dvd.dvd d n /\ Dvd.dvd d m then 1 else 0)) := by
  have hsub : forall d, Membership.mem m.divisors d ->
      Membership.mem (Finset.Ioc 0 N) d := by
    intro d hd
    exact Finset.mem_Ioc.mpr (And.intro (Nat.pos_of_mem_divisors hd)
      ((Nat.le_of_dvd hm (Nat.mem_divisors.mp hd).1).trans hmN))
  calc
    _ = m.divisors.sum (fun d => (ArithmeticFunction.moebius d : Complex) *
        (if Dvd.dvd d n then 1 else 0)) := coprime_mask m n hm
    _ = m.divisors.sum (fun d => (ArithmeticFunction.moebius d : Complex) *
        (if Dvd.dvd d n /\ Dvd.dvd d m then 1 else 0)) := by
      apply Finset.sum_congr rfl
      intro d hd
      simp only [(Nat.mem_divisors.mp hd).1, and_true]
    _ = _ := by
      apply Finset.sum_subset hsub
      intro d hd hnot
      have hdm : Not (Dvd.dvd d m) := by
        intro h
        exact hnot (Nat.mem_divisors.mpr (And.intro h (Nat.ne_of_gt hm)))
      simp only [hdm, and_false, ite_false, mul_zero]

def multipleSum (d : Nat) (s : Finset Nat) (a : Nat -> Complex) : Complex :=
  s.sum (fun n => if Dvd.dvd d n then a n else 0)

def coprimeForm (s t : Finset Nat) (a b : Nat -> Complex) : Complex :=
  s.sum (fun n => t.sum (fun m => if Nat.Coprime n m then a n * b m else 0))

theorem multipleSum_lcm (d e : Nat) (s : Finset Nat) (a : Nat -> Complex) :
    multipleSum d s (fun n => if Dvd.dvd e n then a n else 0) =
      multipleSum (Nat.lcm d e) s a := by
  unfold multipleSum
  apply Finset.sum_congr rfl
  intro n hn
  simp only [Nat.lcm_dvd_iff]
  by_cases hd : Dvd.dvd d n <;> by_cases he : Dvd.dvd e n <;> simp [hd, he]

theorem coprimeForm_factorization (N : Nat) (s t : Finset Nat)
    (ht : forall m, Membership.mem t m -> 0 < m /\ m <= N)
    (a b : Nat -> Complex) :
    coprimeForm s t a b =
      (Finset.Ioc 0 N).sum (fun d =>
        (ArithmeticFunction.moebius d : Complex) *
          multipleSum d s a * multipleSum d t b) := by
  have hterm (n m : Nat) (hm : Membership.mem t m) :
      (if Nat.Coprime n m then a n * b m else 0) =
        (Finset.Ioc 0 N).sum (fun d =>
          (ArithmeticFunction.moebius d : Complex) *
            (if Dvd.dvd d n then a n else 0) *
            (if Dvd.dvd d m then b m else 0)) := by
    calc
      _ = (if Nat.Coprime n m then (1 : Complex) else 0) * (a n * b m) := by
        split_ifs <;> simp
      _ = _ := by
        rw [finite_coprime_mask N n m (ht m hm).1 (ht m hm).2, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro d hd
        by_cases hdn : Dvd.dvd d n <;> by_cases hdm : Dvd.dvd d m
        <;> simp [hdn, hdm, mul_assoc]
  unfold coprimeForm
  calc
    _ = s.sum (fun n => t.sum (fun m =>
        (Finset.Ioc 0 N).sum (fun d =>
          (ArithmeticFunction.moebius d : Complex) *
            (if Dvd.dvd d n then a n else 0) *
            (if Dvd.dvd d m then b m else 0)))) := by
      apply Finset.sum_congr rfl
      intro n hn
      apply Finset.sum_congr rfl
      intro m hm
      exact hterm n m hm
    _ = (Finset.Ioc 0 N).sum (fun d => s.sum (fun n => t.sum (fun m =>
        (ArithmeticFunction.moebius d : Complex) *
          (if Dvd.dvd d n then a n else 0) *
          (if Dvd.dvd d m then b m else 0)))) := by
      simp_rw [Finset.sum_comm (s := t) (t := Finset.Ioc 0 N)]
      rw [Finset.sum_comm (s := s) (t := Finset.Ioc 0 N)]
    _ = _ := by
      simp only [multipleSum, Finset.mul_sum, Finset.sum_mul, mul_assoc]
      apply Finset.sum_congr rfl
      intro d hd
      exact Finset.sum_comm

theorem moebius_norm_le_one (d : Nat) :
    norm (ArithmeticFunction.moebius d : Complex) <= 1 := by
  rcases ArithmeticFunction.moebius_eq_or d with h0 | h1 | hm
  . simp [h0]
  . simp [h1]
  . simp [hm]

theorem coprimeForm_norm_bound (N : Nat) (s t : Finset Nat)
    (ht : forall m, Membership.mem t m -> 0 < m /\ m <= N)
    (a b : Nat -> Complex) :
    norm (coprimeForm s t a b) <=
      (Finset.Ioc 0 N).sum (fun d =>
        norm (multipleSum d s a) * norm (multipleSum d t b)) := by
  rw [coprimeForm_factorization N s t ht a b]
  calc
    _ <= (Finset.Ioc 0 N).sum (fun d =>
        norm ((ArithmeticFunction.moebius d : Complex) *
          multipleSum d s a * multipleSum d t b)) := norm_sum_le _ _
    _ <= _ := by
      apply Finset.sum_le_sum
      intro d hd
      rw [norm_mul, norm_mul]
      calc
        _ <= (1 : Real) * norm (multipleSum d s a) * norm (multipleSum d t b) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (moebius_norm_le_one d) (norm_nonneg _))
            (norm_nonneg _)
        _ = _ := by ring

def multipleJacobiSum (d : Nat) (s : Finset Nat) (a : Nat -> Complex)
    (r : Nat) : Complex :=
  multipleSum d s (fun n => a n * kernel r n)

def multipleEnergy (rows s : Finset Nat) (a : Nat -> Complex) (d : Nat) : Real :=
  rows.sum (fun r => norm (multipleJacobiSum d s a r) ^ 2)

theorem coprime_jacobi_mean_bound (N : Nat) (rows s t : Finset Nat)
    (ht : forall m, Membership.mem t m -> 0 < m /\ m <= N)
    (a b : Nat -> Complex) :
    rows.sum (fun r => norm
      (coprimeForm s t (fun n => a n * kernel r n) (fun m => b m * kernel r m))) <=
      (Finset.Ioc 0 N).sum (fun d =>
        Real.sqrt (multipleEnergy rows s a d) *
          Real.sqrt (multipleEnergy rows t b d)) := by
  calc
    _ <= rows.sum (fun r => (Finset.Ioc 0 N).sum (fun d =>
        norm (multipleJacobiSum d s a r) * norm (multipleJacobiSum d t b r))) := by
      apply Finset.sum_le_sum
      intro r hr
      exact coprimeForm_norm_bound N s t ht _ _
    _ = (Finset.Ioc 0 N).sum (fun d => rows.sum (fun r =>
        norm (multipleJacobiSum d s a r) * norm (multipleJacobiSum d t b r))) :=
      Finset.sum_comm
    _ <= _ := by
      apply Finset.sum_le_sum
      intro d hd
      exact Real.sum_mul_le_sqrt_mul_sqrt rows _ _

theorem multipleEnergy_operator_bound (rows s : Finset Nat)
    (a : Nat -> Complex) (d : Nat) :
    multipleEnergy rows s a d <=
      norm (OAI.FiniteSieveOperator.operator
        (matrix (fun r : rows => (r : Nat)) (fun n : s => (n : Nat)))) ^ 2 *
      s.sum (fun n => if Dvd.dvd d n then norm (a n) ^ 2 else 0) := by
  let A : Matrix rows s Complex :=
    matrix (fun r : rows => (r : Nat)) (fun n : s => (n : Nat))
  let u : s -> Complex := fun n => if Dvd.dvd d (n : Nat) then a n else 0
  have h := OAI.FiniteSieveOperator.energy_bound A u
  have hin (r : rows) :
      Finset.univ.sum (fun n : s => A r n * u n) =
        multipleJacobiSum d s a r := by
    change Finset.univ.sum (fun n : s =>
      kernel (r : Nat) (n : Nat) * (if Dvd.dvd d (n : Nat) then a n else 0)) = _
    rw [Finset.sum_coe_sort s (fun n : Nat =>
      kernel (r : Nat) n * (if Dvd.dvd d n then a n else 0))]
    unfold multipleJacobiSum multipleSum
    apply Finset.sum_congr rfl
    intro n hn
    by_cases hd : Dvd.dvd d n <;> simp [hd, mul_comm]
  have hu : Finset.univ.sum (fun n : s => norm (u n) ^ 2) =
      s.sum (fun n => if Dvd.dvd d n then norm (a n) ^ 2 else 0) := by
    change Finset.univ.sum (fun n : s =>
      norm (if Dvd.dvd d (n : Nat) then a n else 0) ^ 2) = _
    rw [Finset.sum_coe_sort s (fun n : Nat =>
      norm (if Dvd.dvd d n then a n else 0) ^ 2)]
    apply Finset.sum_congr rfl
    intro n hn
    by_cases hd : Dvd.dvd d n <;> simp [hd]
  simp_rw [hin] at h
  rw [hu, Finset.sum_coe_sort rows (fun r : Nat =>
    norm (multipleJacobiSum d s a r) ^ 2)] at h
  exact h


def quotientCols (e : Nat) (s : Finset Nat) : Finset Nat :=
  (s.filter (fun n => Dvd.dvd e n)).image (fun n => n / e)

theorem sum_divisible_quotient {R : Type*} [AddCommMonoid R]
    (e : Nat) (s : Finset Nat) (F : Nat -> R) :
    s.sum (fun n => if Dvd.dvd e n then F n else 0) =
      (quotientCols e s).sum (fun k => F (e * k)) := by
  rw [<- Finset.sum_filter]
  apply Finset.sum_bij (fun n hn => n / e)
  . intro n hn
    exact Finset.mem_image.mpr (Exists.intro n (And.intro hn rfl))
  . intro n hn m hm hnm
    have hn0 := (Finset.mem_filter.mp hn).2
    have hm0 := (Finset.mem_filter.mp hm).2
    calc
      n = e * (n / e) := (Nat.mul_div_cancel' hn0).symm
      _ = e * (m / e) := congrArg (fun k : Nat => e * k) hnm
      _ = m := Nat.mul_div_cancel' hm0
  . intro k hk
    choose n hn using Finset.mem_image.mp hk
    exact Exists.intro n (Exists.intro hn.1 hn.2)
  . intro n hn
    rw [Nat.mul_div_cancel' (Finset.mem_filter.mp hn).2]

theorem quotientCols_pos (e : Nat) (s : Finset Nat)
    (hs : forall n, Membership.mem s n -> 0 < n)
    (k : Nat) (hk : Membership.mem (quotientCols e s) k) : 0 < k := by
  choose n hn using Finset.mem_image.mp hk
  have hns := (Finset.mem_filter.mp hn.1).1
  have hdiv := (Finset.mem_filter.mp hn.1).2
  have hnpos := hs n hns
  have heq : e * k = n := by rw [<- hn.2, Nat.mul_div_cancel' hdiv]
  by_contra h
  have hk0 : k = 0 := Nat.eq_zero_of_not_pos h
  rw [hk0, mul_zero] at heq
  omega

theorem jacobi_dilation (e : Nat) (he : 0 < e) (s : Finset Nat)
    (hs : forall n, Membership.mem s n -> 0 < n)
    (a : Nat -> Complex) (r : Nat) :
    multipleJacobiSum e s a r =
      kernel r e * (quotientCols e s).sum (fun k => a (e * k) * kernel r k) := by
  unfold multipleJacobiSum multipleSum
  rw [sum_divisible_quotient e s (fun n => a n * kernel r n), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [kernel_mul_right r e k (Nat.ne_of_gt he)
    (Nat.ne_of_gt (quotientCols_pos e s hs k hk))]
  ring

theorem multipleEnergy_dilation_bound (rows s : Finset Nat)
    (a : Nat -> Complex) (e : Nat) (he : 0 < e)
    (hs : forall n, Membership.mem s n -> 0 < n) :
    multipleEnergy rows s a e <=
      norm (OAI.FiniteSieveOperator.operator
        (matrix (fun r : rows => (r : Nat))
          (fun k : quotientCols e s => (k : Nat)))) ^ 2 *
      s.sum (fun n => if Dvd.dvd e n then norm (a n) ^ 2 else 0) := by
  have hdilate : multipleEnergy rows s a e <=
      multipleEnergy rows (quotientCols e s) (fun k => a (e * k)) 1 := by
    unfold multipleEnergy
    apply Finset.sum_le_sum
    intro r hr
    have hn : norm (multipleJacobiSum e s a r) <=
        norm ((quotientCols e s).sum (fun k => a (e * k) * kernel r k)) := by
      rw [jacobi_dilation e he s hs a r, norm_mul]
      calc
        _ <= (1 : Real) *
            norm ((quotientCols e s).sum (fun k => a (e * k) * kernel r k)) :=
          mul_le_mul_of_nonneg_right (kernel_norm_le_one r e) (norm_nonneg _)
        _ = _ := one_mul _
    have hsq := mul_self_le_mul_self (norm_nonneg _) hn
    simpa only [multipleJacobiSum, multipleSum, one_dvd, ite_true, pow_two] using hsq
  have hop := multipleEnergy_operator_bound rows (quotientCols e s)
    (fun k => a (e * k)) 1
  simp only [one_dvd, ite_true] at hop
  rw [sum_divisible_quotient e s (fun n => norm (a n) ^ 2)]
  exact hdilate.trans hop

theorem quotientCols_scaled_interval (e : Nat) (he : 0 < e)
    (s : Finset Nat) (N : Real)
    (hs : forall n, Membership.mem s n -> N < (n : Real) /\ (n : Real) <= 2 * N)
    (k : Nat) (hk : Membership.mem (quotientCols e s) k) :
    N / (e : Real) < (k : Real) /\ (k : Real) <= (2 * N) / (e : Real) := by
  choose n hn using Finset.mem_image.mp hk
  have hns := (Finset.mem_filter.mp hn.1).1
  have hdiv := (Finset.mem_filter.mp hn.1).2
  have heq : e * k = n := by rw [<- hn.2, Nat.mul_div_cancel' hdiv]
  have heqR : (e : Real) * (k : Real) = (n : Real) := by exact_mod_cast heq
  have heR : (0 : Real) < (e : Real) := by exact_mod_cast he
  have hdivR : (n : Real) / (e : Real) = (k : Real) := by
    rw [<- heqR]
    field_simp [Nat.ne_of_gt he]
  have hlo := div_lt_div_of_pos_right (hs n hns).1 heR
  have hhi := div_le_div_of_nonneg_right (hs n hns).2 (le_of_lt heR)
  rw [hdivR] at hlo hhi
  exact And.intro hlo hhi


theorem multipleEnergy_nonneg (rows s : Finset Nat) (a : Nat -> Complex) (d : Nat) :
    0 <= multipleEnergy rows s a d :=
  Finset.sum_nonneg (fun r hr => sq_nonneg _)

theorem coprime_jacobi_total_energy_bound (N : Nat) (rows s t : Finset Nat)
    (ht : forall m, Membership.mem t m -> 0 < m /\ m <= N)
    (a b : Nat -> Complex) :
    rows.sum (fun r => norm
      (coprimeForm s t (fun n => a n * kernel r n) (fun m => b m * kernel r m))) <=
      Real.sqrt ((Finset.Ioc 0 N).sum (fun d => multipleEnergy rows s a d)) *
        Real.sqrt ((Finset.Ioc 0 N).sum (fun d => multipleEnergy rows t b d)) := by
  apply (coprime_jacobi_mean_bound N rows s t ht a b).trans
  have hcs := Real.sum_mul_le_sqrt_mul_sqrt (Finset.Ioc 0 N)
    (fun d => Real.sqrt (multipleEnergy rows s a d))
    (fun d => Real.sqrt (multipleEnergy rows t b d))
  have ha (d : Nat) : Real.sqrt (multipleEnergy rows s a d) ^ 2 =
      multipleEnergy rows s a d := Real.sq_sqrt (multipleEnergy_nonneg rows s a d)
  have hb (d : Nat) : Real.sqrt (multipleEnergy rows t b d) ^ 2 =
      multipleEnergy rows t b d := Real.sq_sqrt (multipleEnergy_nonneg rows t b d)
  simpa only [ha, hb] using hcs

def divisorCount (N n : Nat) : Nat :=
  ((Finset.Ioc 0 N).filter (fun d => Dvd.dvd d n)).card

def divisorWeightedMass (N e : Nat) (s : Finset Nat) (a : Nat -> Complex) : Real :=
  s.sum (fun n => if Dvd.dvd e n then (divisorCount N n : Real) * norm (a n) ^ 2 else 0)

theorem divisorCount_eq_card_divisors (N n : Nat) (hn : 0 < n) (hnN : n <= N) :
    divisorCount N n = n.divisors.card := by
  have hsets : (Finset.Ioc 0 N).filter (fun d => Dvd.dvd d n) = n.divisors := by
    apply Finset.ext
    intro d
    constructor
    . intro hd
      exact Nat.mem_divisors.mpr
        (And.intro (Finset.mem_filter.mp hd).2 (Nat.ne_of_gt hn))
    . intro hd
      apply Finset.mem_filter.mpr
      exact And.intro (Finset.mem_Ioc.mpr
        (And.intro (Nat.pos_of_mem_divisors hd)
          ((Nat.le_of_dvd hn (Nat.mem_divisors.mp hd).1).trans hnN)))
        (Nat.mem_divisors.mp hd).1
  unfold divisorCount
  rw [hsets]

theorem divisor_incidence_mass (N e : Nat) (s : Finset Nat) (a : Nat -> Complex) :
    (Finset.Ioc 0 N).sum (fun d => s.sum (fun n =>
      if Dvd.dvd d n /\ Dvd.dvd e n then norm (a n) ^ 2 else 0)) =
        divisorWeightedMass N e s a := by
  rw [Finset.sum_comm]
  unfold divisorWeightedMass
  apply Finset.sum_congr rfl
  intro n hn
  by_cases he : Dvd.dvd e n
  . simp only [he, and_true, ite_true]
    rw [<- Finset.sum_filter]
    simp only [Finset.sum_const, nsmul_eq_mul, divisorCount]
  . simp only [he, and_false, ite_false, Finset.sum_const_zero]

theorem multipleEnergy_swap_masks (rows s : Finset Nat) (a : Nat -> Complex) (d e : Nat) :
    multipleEnergy rows s (fun n => if Dvd.dvd e n then a n else 0) d =
      multipleEnergy rows s (fun n => if Dvd.dvd d n then a n else 0) e := by
  unfold multipleEnergy multipleJacobiSum multipleSum
  apply Finset.sum_congr rfl
  intro r hr
  apply congrArg (fun z : Complex => norm z ^ 2)
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hd : Dvd.dvd d n <;> by_cases he : Dvd.dvd e n <;> simp [hd, he]

theorem masked_total_energy_dilation_bound (N e : Nat) (he : 0 < e)
    (rows s : Finset Nat) (a : Nat -> Complex)
    (hs : forall n, Membership.mem s n -> 0 < n) :
    (Finset.Ioc 0 N).sum (fun d =>
      multipleEnergy rows s (fun n => if Dvd.dvd e n then a n else 0) d) <=
        norm (OAI.FiniteSieveOperator.operator
          (matrix (fun r : rows => (r : Nat))
            (fun k : quotientCols e s => (k : Nat)))) ^ 2 *
          divisorWeightedMass N e s a := by
  rw [<- divisor_incidence_mass N e s a, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro d hd
  rw [multipleEnergy_swap_masks rows s a d e]
  have h := multipleEnergy_dilation_bound rows s
    (fun n => if Dvd.dvd d n then a n else 0) e he hs
  have hm (n : Nat) :
      (if Dvd.dvd e n then norm (if Dvd.dvd d n then a n else 0) ^ 2 else 0) =
        (if Dvd.dvd d n /\ Dvd.dvd e n then norm (a n) ^ 2 else 0) := by
    by_cases hdn : Dvd.dvd d n <;> by_cases hen : Dvd.dvd e n <;> simp [hdn, hen]
  simpa only [hm] using h

theorem coprime_masked_mean_operator_bound (N e1 e2 : Nat) (he1 : 0 < e1) (he2 : 0 < e2)
    (rows s t : Finset Nat) (a b : Nat -> Complex)
    (hs : forall n, Membership.mem s n -> 0 < n)
    (ht : forall m, Membership.mem t m -> 0 < m /\ m <= N) :
    rows.sum (fun r => norm (coprimeForm s t
      (fun n => (if Dvd.dvd e1 n then a n else 0) * kernel r n)
      (fun m => (if Dvd.dvd e2 m then b m else 0) * kernel r m))) <=
      Real.sqrt (norm (OAI.FiniteSieveOperator.operator
          (matrix (fun r : rows => (r : Nat))
            (fun k : quotientCols e1 s => (k : Nat)))) ^ 2 *
          divisorWeightedMass N e1 s a) *
        Real.sqrt (norm (OAI.FiniteSieveOperator.operator
          (matrix (fun r : rows => (r : Nat))
            (fun k : quotientCols e2 t => (k : Nat)))) ^ 2 *
          divisorWeightedMass N e2 t b) := by
  apply (coprime_jacobi_total_energy_bound N rows s t ht
    (fun n => if Dvd.dvd e1 n then a n else 0)
    (fun m => if Dvd.dvd e2 m then b m else 0)).trans
  exact mul_le_mul
    (Real.sqrt_le_sqrt (masked_total_energy_dilation_bound N e1 he1 rows s a hs))
    (Real.sqrt_le_sqrt (masked_total_energy_dilation_bound N e2 he2 rows t b
      (fun m hm => (ht m hm).1)))
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

end PrimeFactorOscillations.QuadraticCoprimeMean

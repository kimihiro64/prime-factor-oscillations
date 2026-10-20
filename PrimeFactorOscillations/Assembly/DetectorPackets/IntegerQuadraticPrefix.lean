/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Assembly.DetectorPackets.QuadraticCoprimeMean

/-!
# IntegerQuadraticPrefix

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

namespace PrimeFactorOscillations.IntegerQuadraticPrefix

open QuadraticCarrierPacket IntegerQuadraticInitial IntegerQuadraticSieve

theorem initial_with_one {M N : Nat} (hM : 0 < M) (hN : 0 < N)
    (a : Nat -> Complex)
    (hs : forall q, Membership.mem (Finset.Icc 1 N) q ->
      Not (a q = 0) -> Odd q /\ Squarefree q) :
    Finset.univ.sum (fun u : Fin M =>
      norm ((Finset.Icc 1 N).sum (fun q => a q * kernel u.val q)) ^ 2) <=
      74 * ((M : Real) + (N : Real) ^ 2) *
        (Finset.Icc 1 N).sum (fun q => norm (a q) ^ 2) := by
  let b : Nat -> Complex := fun q => if q = 1 then 0 else a q
  have h1 : Membership.mem (Finset.Icc 1 N) 1 := by
    apply Finset.mem_Icc.mpr
    exact And.intro (by omega) (by omega)
  have hbGood : forall q, Membership.mem (Finset.Icc 1 N) q ->
      Not (b q = 0) -> Good q := by
    intro q hq hbq
    have hq1 : Not (q = 1) := by
      intro h
      apply hbq
      simp [b, h]
    have haq : Not (a q = 0) := by
      intro ha
      apply hbq
      simp [b, ha]
    exact And.intro (by have := (Finset.mem_Icc.mp hq).1; omega) (hs q hq haq)
  have hbMass : (Finset.Icc 1 N).sum (fun q => norm (b q) ^ 2) <=
      (Finset.Icc 1 N).sum (fun q => norm (a q) ^ 2) := by
    apply Finset.sum_le_sum
    intro q hq
    by_cases hq1 : q = 1
    . simp [b, hq1, sq_nonneg]
    . simp [b, hq1]
  have hbase := (initial_quadratic_sieve hM hN b hbGood).trans
    (mul_le_mul_of_nonneg_left hbMass (by positivity))
  have hmass0 : 0 <= (Finset.Icc 1 N).sum (fun q => norm (a q) ^ 2) :=
    Finset.sum_nonneg (fun q hq => sq_nonneg _)
  have hmass1 : norm (a 1) ^ 2 <=
      (Finset.Icc 1 N).sum (fun q => norm (a q) ^ 2) :=
    Finset.single_le_sum (fun q hq => sq_nonneg (norm (a q))) h1
  have hsplit (u : Nat) :
      (Finset.Icc 1 N).sum (fun q => a q * kernel u q) =
        (Finset.Icc 1 N).sum (fun q => b q * kernel u q) + a 1 := by
    calc
      _ = (Finset.Icc 1 N).sum (fun q =>
          b q * kernel u q + (if q = 1 then a 1 else 0)) := by
        apply Finset.sum_congr rfl
        intro q hq
        by_cases hq1 : q = 1
        . subst q
          simp [b, kernel]
        . simp [b, hq1]
      _ = _ := by
        rw [Finset.sum_add_distrib, Finset.sum_ite_eq']
        simp only [h1, ite_true]
  have hpoint (u : Nat) :
      norm ((Finset.Icc 1 N).sum (fun q => a q * kernel u q)) ^ 2 <=
        2 * norm ((Finset.Icc 1 N).sum (fun q => b q * kernel u q)) ^ 2 +
          2 * norm (a 1) ^ 2 := by
    rw [hsplit]
    have hsq := mul_self_le_mul_self (norm_nonneg _)
      (norm_add_le ((Finset.Icc 1 N).sum (fun q => b q * kernel u q)) (a 1))
    nlinarith [sq_nonneg
      (norm ((Finset.Icc 1 N).sum (fun q => b q * kernel u q)) - norm (a 1))]
  calc
    _ <= Finset.univ.sum (fun u : Fin M =>
        2 * norm ((Finset.Icc 1 N).sum (fun q => b q * kernel u.val q)) ^ 2 +
          2 * norm (a 1) ^ 2) := Finset.sum_le_sum (fun u hu => hpoint u.val)
    _ = 2 * Finset.univ.sum (fun u : Fin M =>
        norm ((Finset.Icc 1 N).sum (fun q => b q * kernel u.val q)) ^ 2) +
          2 * (M : Real) * norm (a 1) ^ 2 := by
      rw [Finset.sum_add_distrib, <- Finset.mul_sum]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring
    _ <= 2 * (36 * ((M : Real) + (N : Real) ^ 2) *
        (Finset.Icc 1 N).sum (fun q => norm (a q) ^ 2)) +
          2 * (M : Real) * (Finset.Icc 1 N).sum (fun q => norm (a q) ^ 2) :=
      add_le_add (mul_le_mul_of_nonneg_left hbase (by norm_num))
        (mul_le_mul_of_nonneg_left hmass1 (by positivity))
    _ <= _ := by
      nlinarith [mul_nonneg (sq_nonneg (N : Real)) hmass0]

theorem finite_energy {M N : Nat} (hM : 0 < M) (hN : 0 < N)
    (rows s : Finset Nat) (a : Nat -> Complex)
    (hr : forall r, Membership.mem rows r -> r < M)
    (hs : forall n, Membership.mem s n -> Membership.mem (Finset.Icc 1 N) n)
    (hgood : forall n, Membership.mem s n -> Odd n /\ Squarefree n) :
    rows.sum (fun r => norm (s.sum (fun n => a n * kernel r n)) ^ 2) <=
      74 * ((M : Real) + (N : Real) ^ 2) * s.sum (fun n => norm (a n) ^ 2) := by
  let aa : Nat -> Complex := fun n => if Membership.mem s n then a n else 0
  have haa : forall q, Membership.mem (Finset.Icc 1 N) q ->
      Not (aa q = 0) -> Odd q /\ Squarefree q := by
    intro q hq haq
    have hqs : Membership.mem s q := by
      by_contra h
      apply haq
      simp [aa, h]
    exact hgood q hqs
  have hsum (r : Nat) : (Finset.Icc 1 N).sum (fun n => aa n * kernel r n) =
      s.sum (fun n => a n * kernel r n) := by
    calc
      _ = s.sum (fun n => aa n * kernel r n) :=
        (Finset.sum_subset hs (fun n hn hns => by simp [aa, hns])).symm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro n hn
        simp only [aa, hn, ite_true]
  have hmass : (Finset.Icc 1 N).sum (fun n => norm (aa n) ^ 2) =
      s.sum (fun n => norm (a n) ^ 2) := by
    calc
      _ = s.sum (fun n => norm (aa n) ^ 2) :=
        (Finset.sum_subset hs (fun n hn hns => by simp [aa, hns])).symm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro n hn
        simp only [aa, hn, ite_true]
  have hrsub : forall r, Membership.mem rows r -> Membership.mem (Finset.range M) r :=
    fun r h => Finset.mem_range.mpr (hr r h)
  calc
    _ <= (Finset.range M).sum (fun r => norm (s.sum (fun n => a n * kernel r n)) ^ 2) :=
      Finset.sum_le_sum_of_subset_of_nonneg hrsub (fun r hr hnot => sq_nonneg _)
    _ = Finset.univ.sum (fun u : Fin M =>
        norm ((Finset.Icc 1 N).sum (fun n => aa n * kernel u.val n)) ^ 2) := by
      rw [Fin.sum_univ_eq_sum_range
        (fun r : Nat => norm ((Finset.Icc 1 N).sum (fun n => aa n * kernel r n)) ^ 2) M]
      apply Finset.sum_congr rfl
      intro r hr
      rw [hsum]
    _ <= 74 * ((M : Real) + (N : Real) ^ 2) *
        (Finset.Icc 1 N).sum (fun n => norm (aa n) ^ 2) :=
      initial_with_one hM hN aa haa
    _ = _ := by rw [hmass]


theorem operator_norm_sq_of_energy {m n : Type*}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (A : Matrix m n Complex) (C : Real) (hC : 0 <= C)
    (hE : forall a : n -> Complex,
      Finset.univ.sum (fun i => norm (Finset.univ.sum (fun j => A i j * a j)) ^ 2) <=
        C * Finset.univ.sum (fun j => norm (a j) ^ 2)) :
    norm (OAI.FiniteSieveOperator.operator A) ^ 2 <= C := by
  have hn : norm (OAI.FiniteSieveOperator.operator A) <= Real.sqrt C := by
    apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg C)
    intro x
    have hx : norm (OAI.FiniteSieveOperator.operator A x) ^ 2 <= C * norm x ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
      simpa only [OAI.FiniteSieveOperator.operator_apply] using hE (fun j => x j)
    have hsq := Real.sqrt_le_sqrt hx
    rw [Real.sqrt_sq (norm_nonneg _), Real.sqrt_mul hC,
      Real.sqrt_sq (norm_nonneg x)] at hsq
    exact hsq
  have hsq := mul_self_le_mul_self (norm_nonneg _) hn
  simpa only [<- pow_two, Real.sq_sqrt hC] using hsq

theorem matrix_norm_sq_of_finite_energy (rows s : Finset Nat) (C : Real) (hC : 0 <= C)
    (hE : forall a : Nat -> Complex,
      rows.sum (fun r => norm (s.sum (fun n => a n * kernel r n)) ^ 2) <=
        C * s.sum (fun n => norm (a n) ^ 2)) :
    norm (OAI.FiniteSieveOperator.operator
      (matrix (fun r : rows => (r : Nat)) (fun n : s => (n : Nat)))) ^ 2 <= C := by
  apply operator_norm_sq_of_energy _ C hC
  intro u
  let a : Nat -> Complex := fun n =>
    if h : Membership.mem s n then u (Subtype.mk n h) else 0
  have hin (n : s) : a n = u n := by simp [a, n.property]
  have hinner (r : rows) :
      Finset.univ.sum (fun n : s =>
        matrix (fun r : rows => (r : Nat)) (fun n : s => (n : Nat)) r n * u n) =
          s.sum (fun n => a n * kernel r n) := by
    simp_rw [<- hin]
    change Finset.univ.sum (fun n : s => kernel (r : Nat) (n : Nat) * a n) = _
    rw [Finset.sum_coe_sort s (fun n : Nat => kernel (r : Nat) n * a n)]
    apply Finset.sum_congr rfl
    intro n hn
    ring
  have hmass : Finset.univ.sum (fun n : s => norm (u n) ^ 2) =
      s.sum (fun n => norm (a n) ^ 2) := by
    simp_rw [<- hin]
    exact Finset.sum_coe_sort s (fun n : Nat => norm (a n) ^ 2)
  calc
    _ = rows.sum (fun r => norm (s.sum (fun n => a n * kernel r n)) ^ 2) := by
      simp_rw [hinner]
      exact Finset.sum_coe_sort rows
        (fun r : Nat => norm (s.sum (fun n => a n * kernel r n)) ^ 2)
    _ <= C * s.sum (fun n => norm (a n) ^ 2) := hE a
    _ = _ := by rw [hmass]

theorem finite_operator_norm_bound {M N : Nat} (hM : 0 < M) (hN : 0 < N)
    (rows s : Finset Nat)
    (hr : forall r, Membership.mem rows r -> r < M)
    (hs : forall n, Membership.mem s n -> Membership.mem (Finset.Icc 1 N) n)
    (hgood : forall n, Membership.mem s n -> Odd n /\ Squarefree n) :
    norm (OAI.FiniteSieveOperator.operator
      (matrix (fun r : rows => (r : Nat)) (fun n : s => (n : Nat)))) ^ 2 <=
        74 * ((M : Real) + (N : Real) ^ 2) := by
  apply matrix_norm_sq_of_finite_energy _ _ _ (by positivity)
  intro a
  exact finite_energy hM hN rows s a hr hs hgood

theorem matrix_norm_sq_monotone (rows rows' s s' : Finset Nat)
    (hr : forall r, Membership.mem rows r -> Membership.mem rows' r)
    (hs : forall n, Membership.mem s n -> Membership.mem s' n) :
    norm (OAI.FiniteSieveOperator.operator
      (matrix (fun r : rows => (r : Nat)) (fun n : s => (n : Nat)))) ^ 2 <=
        norm (OAI.FiniteSieveOperator.operator
          (matrix (fun r : rows' => (r : Nat)) (fun n : s' => (n : Nat)))) ^ 2 := by
  apply matrix_norm_sq_of_finite_energy _ _ _ (sq_nonneg _)
  intro a
  let aa : Nat -> Complex := fun n => if Membership.mem s n then a n else 0
  have hsum (r : Nat) : s'.sum (fun n => aa n * kernel r n) =
      s.sum (fun n => a n * kernel r n) := by
    calc
      _ = s.sum (fun n => aa n * kernel r n) :=
        (Finset.sum_subset hs (fun n hn hns => by simp [aa, hns])).symm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro n hn
        simp only [aa, hn, ite_true]
  have hmass : s'.sum (fun n => norm (aa n) ^ 2) =
      s.sum (fun n => norm (a n) ^ 2) := by
    calc
      _ = s.sum (fun n => norm (aa n) ^ 2) :=
        (Finset.sum_subset hs (fun n hn hns => by simp [aa, hns])).symm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro n hn
        simp only [aa, hn, ite_true]
  have h := QuadraticCoprimeMean.multipleEnergy_operator_bound rows' s' aa 1
  simp only [QuadraticCoprimeMean.multipleEnergy, QuadraticCoprimeMean.multipleJacobiSum,
    QuadraticCoprimeMean.multipleSum, one_dvd, ite_true] at h
  simp_rw [hsum] at h
  rw [hmass] at h
  exact (Finset.sum_le_sum_of_subset_of_nonneg hr
    (fun r hr hnot => sq_nonneg _)).trans h

def columns (N : Nat) : Finset Nat :=
  (Finset.Icc 1 N).filter (fun n => Odd n /\ Squarefree n)

def prefixNorm (M N : Nat) : Real :=
  norm (OAI.FiniteSieveOperator.operator
    (matrix (fun r : columns M => (r : Nat)) (fun n : columns N => (n : Nat)))) ^ 2

theorem columns_monotone {N N' : Nat} (hN : N <= N') :
    forall n, Membership.mem (columns N) n -> Membership.mem (columns N') n := by
  intro n hn
  have h := Finset.mem_filter.mp hn
  exact Finset.mem_filter.mpr (And.intro
    (Finset.mem_Icc.mpr (And.intro (Finset.mem_Icc.mp h.1).1
      ((Finset.mem_Icc.mp h.1).2.trans hN))) h.2)

theorem prefixNorm_monotone {M M' N N' : Nat} (hM : M <= M') (hN : N <= N') :
    prefixNorm M N <= prefixNorm M' N' :=
  matrix_norm_sq_monotone _ _ _ _ (columns_monotone hM) (columns_monotone hN)

theorem prefixNorm_initial {M N : Nat} (hM : 0 < M) (hN : 0 < N) :
    prefixNorm M N <= 148 * ((M : Real) + (N : Real) ^ 2) := by
  have h := finite_operator_norm_bound (Nat.succ_pos M) hN (columns M) (columns N)
    (fun r hr => by have := (Finset.mem_Icc.mp (Finset.mem_filter.mp hr).1).2; omega)
    (fun n hn => (Finset.mem_filter.mp hn).1)
    (fun n hn => (Finset.mem_filter.mp hn).2)
  apply h.trans
  have hM1 : (1 : Real) <= (M : Real) := by exact_mod_cast hM
  push_cast
  nlinarith [sq_nonneg (N : Real)]

theorem prefixNorm_zero_right (M : Nat) : prefixNorm M 0 = 0 := by
  apply le_antisymm
  . apply matrix_norm_sq_of_finite_energy _ _ 0 (by norm_num)
    intro a
    simp [columns]
  . exact sq_nonneg _

theorem prefixNorm_zero_left (N : Nat) : prefixNorm 0 N = 0 := by
  apply le_antisymm
  . apply matrix_norm_sq_of_finite_energy _ _ 0 (by norm_num)
    intro a
    simp [columns]
  . exact sq_nonneg _


open QuadraticCoprimeMean

theorem prefixNorm_initial_all (M N : Nat) :
    prefixNorm M N <= 148 * ((M : Real) + (N : Real) ^ 2) := by
  by_cases hM : M = 0
  . subst M
    rw [prefixNorm_zero_left]
    positivity
  by_cases hN : N = 0
  . subst N
    rw [prefixNorm_zero_right]
    positivity
  exact prefixNorm_initial (Nat.pos_of_ne_zero hM) (Nat.pos_of_ne_zero hN)

theorem quotientCols_subset_columns (e N : Nat) (s : Finset Nat)
    (hs : forall n, Membership.mem s n -> Membership.mem (columns N) n) :
    forall k, Membership.mem (quotientCols e s) k ->
      Membership.mem (columns (N / e)) k := by
  intro k hk
  choose n hn using Finset.mem_image.mp hk
  have hns := (Finset.mem_filter.mp hn.1).1
  have hdiv := (Finset.mem_filter.mp hn.1).2
  have hdata := Finset.mem_filter.mp (hs n hns)
  have heq : e * k = n := by rw [<- hn.2, Nat.mul_div_cancel' hdiv]
  have hkn : Dvd.dvd k n := Exists.intro e (by rw [<- heq]; ring)
  have hodd : Odd k := by
    have hm : Odd (e * k) := by rw [heq]; exact hdata.2.1
    exact (Nat.odd_mul.mp hm).2
  have hsq : Squarefree k := Squarefree.squarefree_of_dvd hkn hdata.2.2
  have hkpos : 0 < k := quotientCols_pos e s
    (fun n hn => by have := (Finset.mem_Icc.mp (Finset.mem_filter.mp (hs n hn)).1).1; omega)
    k hk
  have hkN := Nat.div_le_div_right (c := e) (Finset.mem_Icc.mp hdata.1).2
  rw [hn.2] at hkN
  exact Finset.mem_filter.mpr (And.intro
    (Finset.mem_Icc.mpr (And.intro hkpos hkN)) (And.intro hodd hsq))

theorem quotient_operator_le_prefixNorm (M N e : Nat) (rows s : Finset Nat)
    (hr : forall r, Membership.mem rows r -> Membership.mem (columns M) r)
    (hs : forall n, Membership.mem s n -> Membership.mem (columns N) n) :
    norm (OAI.FiniteSieveOperator.operator
      (matrix (fun r : rows => (r : Nat)) (fun k : quotientCols e s => (k : Nat)))) ^ 2 <=
        prefixNorm M (N / e) :=
  matrix_norm_sq_monotone _ _ _ _ hr (quotientCols_subset_columns e N s hs)

theorem quotient_operator_initial (M N e : Nat) (rows s : Finset Nat)
    (hr : forall r, Membership.mem rows r -> Membership.mem (columns M) r)
    (hs : forall n, Membership.mem s n -> Membership.mem (columns N) n) :
    norm (OAI.FiniteSieveOperator.operator
      (matrix (fun r : rows => (r : Nat)) (fun k : quotientCols e s => (k : Nat)))) ^ 2 <=
        148 * ((M : Real) + ((N / e : Nat) : Real) ^ 2) :=
  (quotient_operator_le_prefixNorm M N e rows s hr hs).trans
    (prefixNorm_initial_all M (N / e))

theorem divisorWeightedMass_nonneg (N e : Nat) (s : Finset Nat) (a : Nat -> Complex) :
    0 <= divisorWeightedMass N e s a := by
  unfold divisorWeightedMass
  apply Finset.sum_nonneg
  intro n hn
  split_ifs
  . exact mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)
  . exact le_refl 0

theorem coprime_mean_prefix_bound (M N1 N2 e1 e2 : Nat) (he1 : 0 < e1) (he2 : 0 < e2)
    (rows s t : Finset Nat) (a b : Nat -> Complex)
    (hr : forall r, Membership.mem rows r -> Membership.mem (columns M) r)
    (hs : forall n, Membership.mem s n -> Membership.mem (columns N1) n)
    (ht : forall m, Membership.mem t m -> Membership.mem (columns N2) m) :
    rows.sum (fun r => norm (coprimeForm s t
      (fun n => (if Dvd.dvd e1 n then a n else 0) * kernel r n)
      (fun m => (if Dvd.dvd e2 m then b m else 0) * kernel r m))) <=
      Real.sqrt (prefixNorm M (N1 / e1) * divisorWeightedMass (max N1 N2) e1 s a) *
        Real.sqrt (prefixNorm M (N2 / e2) * divisorWeightedMass (max N1 N2) e2 t b) := by
  have hspos : forall n, Membership.mem s n -> 0 < n := by
    intro n hn
    have := (Finset.mem_Icc.mp (Finset.mem_filter.mp (hs n hn)).1).1
    omega
  have htbound : forall m, Membership.mem t m -> 0 < m /\ m <= max N1 N2 := by
    intro m hm
    have h := Finset.mem_Icc.mp (Finset.mem_filter.mp (ht m hm)).1
    exact And.intro (by omega) (h.2.trans (Nat.le_max_right N1 N2))
  apply (coprime_masked_mean_operator_bound (max N1 N2) e1 e2 he1 he2
    rows s t a b hspos htbound).trans
  exact mul_le_mul
    (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right
      (quotient_operator_le_prefixNorm M N1 e1 rows s hr hs)
      (divisorWeightedMass_nonneg _ _ _ _)))
    (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right
      (quotient_operator_le_prefixNorm M N2 e2 rows t hr ht)
      (divisorWeightedMass_nonneg _ _ _ _)))
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

theorem coprime_mean_initial_bound (M N1 N2 e1 e2 : Nat) (he1 : 0 < e1) (he2 : 0 < e2)
    (rows s t : Finset Nat) (a b : Nat -> Complex)
    (hr : forall r, Membership.mem rows r -> Membership.mem (columns M) r)
    (hs : forall n, Membership.mem s n -> Membership.mem (columns N1) n)
    (ht : forall m, Membership.mem t m -> Membership.mem (columns N2) m) :
    rows.sum (fun r => norm (coprimeForm s t
      (fun n => (if Dvd.dvd e1 n then a n else 0) * kernel r n)
      (fun m => (if Dvd.dvd e2 m then b m else 0) * kernel r m))) <=
      Real.sqrt (148 * ((M : Real) + ((N1 / e1 : Nat) : Real) ^ 2) *
          divisorWeightedMass (max N1 N2) e1 s a) *
        Real.sqrt (148 * ((M : Real) + ((N2 / e2 : Nat) : Real) ^ 2) *
          divisorWeightedMass (max N1 N2) e2 t b) := by
  apply (coprime_mean_prefix_bound M N1 N2 e1 e2 he1 he2 rows s t a b hr hs ht).trans
  exact mul_le_mul
    (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right (prefixNorm_initial_all M (N1 / e1))
      (divisorWeightedMass_nonneg _ _ _ _)))
    (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right (prefixNorm_initial_all M (N2 / e2))
      (divisorWeightedMass_nonneg _ _ _ _)))
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

end PrimeFactorOscillations.IntegerQuadraticPrefix

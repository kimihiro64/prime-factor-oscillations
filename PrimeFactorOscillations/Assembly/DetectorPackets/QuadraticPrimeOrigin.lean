/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Assembly.DetectorPackets.IntegerQuadraticCorrelationPoisson

/-!
# QuadraticPrimeOrigin

Maintained extraction of completed detector/packet proof components.
All original theorem hypotheses and retained proof bodies are preserved.
This module alone asserts no improved zero-free boundary.
-/

set_option autoImplicit false
set_option Elab.async false

/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

/-!
# One-sided bound for the phase-separated prime origin correction

The raw Gauss phase and Jacobi zero mask are retained. This proves a
negative-square bound for the separated origin block. Identifying that
block with a complete Poisson remainder is a separate analytic step.
-/


noncomputable section
namespace PrimeFactorOscillations.QuadraticPrimeOrigin

open IntegerQuadraticCharacter IntegerQuadraticSquarefree IntegerQuadraticInitial
open IntegerQuadraticCorrelationPoisson

def offDiagonal (s : Finset Nat) (a : Nat -> Complex) : Complex :=
  s.sum (fun p => s.sum (fun q => if p = q then 0 else a p * star (a q)))

def origin (s : Finset Nat) (a : Nat -> Complex) (c : Real) : Complex :=
  -(c : Complex) * (Finset.range 8).sum
    (fun r => offDiagonal (s.filter (fun p => p % 8 = r)) a)

def normalizedGauss (p : Nat) : Complex :=
  if hp : Good p then
    letI : NeZero p := NeZero.mk (by omega)
    gaussSum (character p hp.1) ZMod.stdAddChar / (p : Complex)
  else 0

def coefficient (lambda : Nat -> Complex) (b : Int) (p : Nat) : Complex :=
  lambda p * normalizedGauss p * intKernel b p

theorem small_prime_product_divisor (p q d L : Nat)
    (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hL1 : 1 <= L) (hLp : L < p) (hLq : L < q)
    (hd : Dvd.dvd d (p * q)) (hdL : d <= L) : d = 1 := by
  have hd0 : Not (d = 0) := by
    intro hz
    rw [hz, zero_dvd_iff] at hd
    exact (mul_ne_zero hp.ne_zero hq.ne_zero) hd
  have hdpos : 0 < d := Nat.pos_of_ne_zero hd0
  have hcp : Nat.Coprime d p := by
    rcases (Nat.dvd_prime hp).mp (Nat.gcd_dvd_right d p) with h | h
    . exact h
    . have hpd : Dvd.dvd p d := by
        rw [<- h]
        exact Nat.gcd_dvd_left d p
      have hl := Nat.le_of_dvd hdpos hpd
      omega
  have hdq : Dvd.dvd d q := hcp.dvd_of_dvd_mul_left hd
  rcases (Nat.dvd_prime hq).mp hdq with h | h
  . exact h
  . omega

theorem truncated_prime_moebius (p q L : Nat)
    (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hL1 : 1 <= L) (hLp : L < p) (hLq : L < q) :
    ((p * q).divisors.filter (fun d => d <= L)).sum
      (fun d => (ArithmeticFunction.moebius d : Complex)) = 1 := by
  classical
  have heq : (p * q).divisors.filter (fun d => d <= L) = {1} := by
    apply Finset.ext
    intro d
    simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    . intro hd
      exact small_prime_product_divisor p q d L hp hq hL1 hLp hLq
        (Nat.mem_divisors.mp hd.1).1 hd.2
    . intro hd
      subst d
      exact And.intro (Nat.mem_divisors.mpr (And.intro (one_dvd _)
        (mul_ne_zero hp.ne_zero hq.ne_zero))) hL1
  rw [heq]
  norm_num

theorem offDiagonal_eq (s : Finset Nat) (a : Nat -> Complex) :
    offDiagonal s a = s.sum a * star (s.sum a) -
      s.sum (fun p => a p * star (a p)) := by
  classical
  have ht (p q : Nat) :
      (if p = q then (0 : Complex) else a p * star (a q)) =
        a p * star (a q) - (if p = q then a p * star (a p) else 0) := by
    by_cases h : p = q <;> simp [h]
  calc
    _ = s.sum (fun p => s.sum (fun q => a p * star (a q))) -
        s.sum (fun p => s.sum (fun q => if p = q then a p * star (a p) else 0)) := by
      unfold offDiagonal
      simp_rw [ht, Finset.sum_sub_distrib]
    _ = _ := by
      congr 1
      . have hc : star (s.sum a) = s.sum (fun q => star (a q)) := by simp
        rw [hc, Finset.sum_mul_sum]
      . apply Finset.sum_congr rfl
        intro p hp
        simp [hp]

theorem negative_offDiagonal_re (s : Finset Nat) (a : Nat -> Complex) :
    (-offDiagonal s a).re <= s.sum (fun p => norm (a p) ^ 2) := by
  have hsqu (z : Complex) : (z * star z).re = norm z ^ 2 := by
    calc
      _ = Complex.normSq z := by simp [Complex.mul_re, Complex.normSq]
      _ = _ := Complex.normSq_eq_norm_sq z
  have hsum : (s.sum (fun p => a p * star (a p))).re =
      s.sum (fun p => norm (a p) ^ 2) := by
    calc
      _ = s.sum (fun p => (a p * star (a p)).re) :=
        map_sum Complex.reAddGroupHom _ _
      _ = _ := by
        apply Finset.sum_congr rfl
        intro p hp
        exact hsqu (a p)
  have hre : (-offDiagonal s a).re =
      s.sum (fun p => norm (a p) ^ 2) - norm (s.sum a) ^ 2 := by
    rw [offDiagonal_eq, Complex.neg_re, Complex.sub_re, hsum, hsqu]
    ring
  rw [hre]
  nlinarith [sq_nonneg (norm (s.sum a))]

theorem class_mass (s : Finset Nat) (f : Nat -> Real) :
    (Finset.range 8).sum (fun r => (s.filter (fun p => p % 8 = r)).sum f) =
      s.sum f := by
  classical
  simp_rw [Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p hp
  have hm : Membership.mem (Finset.range 8) (p % 8) :=
    Finset.mem_range.mpr (Nat.mod_lt p (by decide))
  simp [hm]

theorem origin_re_le (s : Finset Nat) (a : Nat -> Complex)
    (c : Real) (hc : 0 <= c) :
    (origin s a c).re <= c * s.sum (fun p => norm (a p) ^ 2) := by
  have heq : (origin s a c).re =
      c * (Finset.range 8).sum (fun r =>
        (-offDiagonal (s.filter (fun p => p % 8 = r)) a).re) := by
    simp [origin, Complex.mul_re, map_sum, Finset.sum_neg_distrib]
  rw [heq, <- class_mass s (fun p => norm (a p) ^ 2)]
  apply mul_le_mul_of_nonneg_left _ hc
  apply Finset.sum_le_sum
  intro r hr
  exact negative_offDiagonal_re _ a

theorem normalizedGauss_norm_sq (p : Nat) (hp : Good p) :
    norm (normalizedGauss p) ^ 2 = 1 / (p : Real) := by
  letI : NeZero p := NeZero.mk (by omega)
  have hG := squarefree_gauss_norm_sq p hp.1 hp.2.1 hp.2.2
    ZMod.stdAddChar (ZMod.isPrimitive_stdAddChar p)
  have hp0 : Not ((p : Real) = 0) := by exact_mod_cast NeZero.ne p
  unfold normalizedGauss
  rw [dif_pos hp, norm_div, div_pow]
  have hnorm : norm (p : Complex) = (p : Real) := by simp
  rw [hnorm, hG]
  field_simp

theorem int_kernel_norm_le_one (b : Int) (p : Nat) :
    norm (intKernel b p) <= 1 := by
  rcases jacobiSym.trichotomy b p with h | h | h
  all_goals simp [intKernel, h]

theorem coefficient_norm_sq (lambda : Nat -> Complex) (b : Int)
    (p : Nat) (hp : Good p) :
    norm (coefficient lambda b p) ^ 2 <= norm (lambda p) ^ 2 / (p : Real) := by
  have hk := int_kernel_norm_le_one b p
  have hksq : norm (intKernel b p) ^ 2 <= 1 := by
    nlinarith [norm_nonneg (intKernel b p)]
  calc
    _ = (norm (lambda p) ^ 2 / (p : Real)) * norm (intKernel b p) ^ 2 := by
      simp only [coefficient, norm_mul, mul_pow, normalizedGauss_norm_sq p hp]
      ring
    _ <= (norm (lambda p) ^ 2 / (p : Real)) * 1 :=
      mul_le_mul_of_nonneg_left hksq (div_nonneg (sq_nonneg _) (Nat.cast_nonneg p))
    _ = _ := mul_one _

theorem prime_origin_upper (s : Finset Nat)
    (lambda : Nat -> Complex) (b : Int) (c N : Real) (hc : 0 <= c) (hN : 0 < N)
    (hgood : forall p, Membership.mem s p -> Good p)
    (hlower : forall p, Membership.mem s p -> N <= (p : Real)) :
    (origin s (coefficient lambda b) c).re <=
      (c / N) * s.sum (fun p => norm (lambda p) ^ 2) := by
  calc
    _ <= c * s.sum (fun p => norm (coefficient lambda b p) ^ 2) :=
      origin_re_le s _ c hc
    _ <= c * s.sum (fun p => norm (lambda p) ^ 2 / N) := by
      apply mul_le_mul_of_nonneg_left _ hc
      apply Finset.sum_le_sum
      intro p hp
      exact (coefficient_norm_sq lambda b p (hgood p hp)).trans
        (div_le_div_of_nonneg_left (sq_nonneg _) hN (hlower p hp))
    _ = _ := by rw [<- Finset.sum_div]; ring

end PrimeFactorOscillations.QuadraticPrimeOrigin


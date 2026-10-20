/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.DirichletCharacter.Bounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# SignedQuarticKernel

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
# Exact signed kernel for the quartic compensated character packet

The complete positive supply, negative allowance and finite Mobius convolution
are retained. The declarations supply the arithmetic input to a joint estimate;
they assert no power saving or zero exclusion.
-/


noncomputable section
namespace PrimeFactorOscillations.SignedQuarticKernel

def hyperbola (N : Nat) : Finset (Prod Nat Nat) :=
  ((Finset.Icc 1 N).product (Finset.Icc 1 N)).filter
    (fun p => p.1 * p.2 <= N)

theorem sum_divisor_pairs (N : Nat) (F : Prod Nat Nat -> Real) :
    (Finset.Icc 1 N).sum (fun n => n.divisorsAntidiagonal.sum F) =
      (hyperbola N).sum F := by
  classical
  rw [Finset.sum_sigma']
  apply Finset.sum_bij (fun x _ => x.2)
  . intro x hx
    have hs := Finset.mem_sigma.mp hx
    have hn := Finset.mem_Icc.mp hs.1
    have hp := Nat.mem_divisorsAntidiagonal.mp hs.2
    have ha : Not (x.2.1 = 0) := by
      intro hz
      have he := hp.1
      rw [hz, zero_mul] at he
      exact hp.2 he.symm
    have hb : Not (x.2.2 = 0) := by
      intro hz
      have he := hp.1
      rw [hz, mul_zero] at he
      exact hp.2 he.symm
    have hadvd : Dvd.dvd x.2.1 x.1 := by
      rw [<- hp.1]
      exact dvd_mul_right _ _
    have hbdvd : Dvd.dvd x.2.2 x.1 := by
      rw [<- hp.1]
      exact dvd_mul_left _ _
    apply Finset.mem_filter.mpr
    refine And.intro (Finset.mem_product.mpr (And.intro ?_ ?_)) ?_
    . exact Finset.mem_Icc.mpr (And.intro (Nat.one_le_iff_ne_zero.mpr ha)
        ((Nat.le_of_dvd hn.1 hadvd).trans hn.2))
    . exact Finset.mem_Icc.mpr (And.intro (Nat.one_le_iff_ne_zero.mpr hb)
        ((Nat.le_of_dvd hn.1 hbdvd).trans hn.2))
    . exact hp.1.le.trans hn.2
  . intro x hx y hy hxy
    have hp := (Nat.mem_divisorsAntidiagonal.mp (Finset.mem_sigma.mp hx).2).1
    have hq := (Nat.mem_divisorsAntidiagonal.mp (Finset.mem_sigma.mp hy).2).1
    cases x with
    | mk n p =>
      cases y with
      | mk m q =>
        dsimp at hxy hp hq
        cases hxy
        have hnm : n = m := hp.symm.trans hq
        cases hnm
        rfl
  . intro p hp
    have hs := Finset.mem_filter.mp hp
    have hab := Finset.mem_product.mp hs.1
    have ha := Finset.mem_Icc.mp hab.1
    have hb := Finset.mem_Icc.mp hab.2
    have hpos : 0 < p.1 * p.2 := Nat.mul_pos ha.1 hb.1
    have hn : Membership.mem (Finset.Icc 1 N) (p.1 * p.2) :=
      Finset.mem_Icc.mpr (And.intro hpos hs.2)
    have hd : Membership.mem (p.1 * p.2).divisorsAntidiagonal p :=
      Nat.mem_divisorsAntidiagonal.mpr
        (And.intro rfl (Nat.ne_of_gt hpos))
    exact Exists.intro (Sigma.mk (p.1 * p.2) p)
      (Exists.intro (Finset.mem_sigma.mpr (And.intro hn hd)) rfl)
  . intro x hx
    rfl

def weightedChebyshev (w : Nat -> Real) (N : Nat) : Real :=
  (Finset.Icc 1 N).sum (fun n => w n * ArithmeticFunction.vonMangoldt n)

def compensated (w : Nat -> Real) (A B : Nat) (c : Real) : Real :=
  weightedChebyshev w A - c * weightedChebyshev w B

def differenceKernel (A : Nat) (c : Real) (n : Nat) : Real :=
  (if n <= A then 1 else 0) - c

theorem compensated_eq_kernel (w : Nat -> Real) (A B : Nat) (c : Real)
    (hAB : A <= B) :
    compensated w A B c =
      (Finset.Icc 1 B).sum (fun n =>
        w n * ArithmeticFunction.vonMangoldt n * differenceKernel A c n) := by
  classical
  have hfilter : (Finset.Icc 1 B).filter (fun n => n <= A) = Finset.Icc 1 A := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_Icc]
    constructor
    . intro h
      exact And.intro h.1.1 h.2
    . intro h
      exact And.intro (And.intro h.1 (h.2.trans hAB)) h.2
  have htrunc :
      (Finset.Icc 1 B).sum (fun n =>
        if n <= A then w n * ArithmeticFunction.vonMangoldt n else 0) =
      weightedChebyshev w A := by
    rw [<- Finset.sum_filter, hfilter]
    rfl
  unfold differenceKernel
  simp_rw [mul_sub, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_sub_distrib, htrunc, <- Finset.sum_mul]
  unfold compensated weightedChebyshev
  ring

theorem weighted_kernel_moebius (w K : Nat -> Real) (B : Nat) :
    (Finset.Icc 1 B).sum (fun n =>
      w n * ArithmeticFunction.vonMangoldt n * K n) =
    -(hyperbola B).sum (fun p =>
      (ArithmeticFunction.moebius p.1 : Real) * Real.log (p.1 : Real) *
        w (p.1 * p.2) * K (p.1 * p.2)) := by
  let F : Prod Nat Nat -> Real := fun p =>
    (ArithmeticFunction.moebius p.1 : Real) * Real.log (p.1 : Real) *
      w (p.1 * p.2) * K (p.1 * p.2)
  have hterm (n : Nat) :
      n.divisorsAntidiagonal.sum F =
        -ArithmeticFunction.vonMangoldt n * w n * K n := by
    calc
      _ = n.divisorsAntidiagonal.sum (fun p =>
          (ArithmeticFunction.moebius p.1 : Real) * Real.log (p.1 : Real) *
            w n * K n) := by
        apply Finset.sum_congr rfl
        intro p hp
        dsimp [F]
        rw [(Nat.mem_divisorsAntidiagonal.mp hp).1]
      _ = (n.divisorsAntidiagonal.sum (fun p =>
          (ArithmeticFunction.moebius p.1 : Real) * Real.log (p.1 : Real))) *
            w n * K n := by
        rw [Finset.sum_mul, Finset.sum_mul]
      _ = _ := by
        rw [Nat.sum_divisorsAntidiagonal (fun a _ =>
          (ArithmeticFunction.moebius a : Real) * Real.log (a : Real))]
        have hm : n.divisors.sum (fun a =>
            (ArithmeticFunction.moebius a : Real) * Real.log (a : Real)) =
            -ArithmeticFunction.vonMangoldt n :=
          ArithmeticFunction.sum_moebius_mul_log_eq
        rw [hm]
  calc
    _ = (Finset.Icc 1 B).sum (fun n => -n.divisorsAntidiagonal.sum F) := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [hterm]
      ring
    _ = -(hyperbola B).sum F := by
      rw [Finset.sum_neg_distrib, sum_divisor_pairs]

theorem compensated_moebius (w : Nat -> Real) (A B : Nat) (c : Real)
    (hAB : A <= B) :
    compensated w A B c =
      -(hyperbola B).sum (fun p =>
        (ArithmeticFunction.moebius p.1 : Real) * Real.log (p.1 : Real) *
          w (p.1 * p.2) * differenceKernel A c (p.1 * p.2)) := by
  rw [compensated_eq_kernel w A B c hAB]
  exact weighted_kernel_moebius w (differenceKernel A c) B

theorem compensated_supply (w : Nat -> Real) (A B : Nat) (c : Real)
    (hAB : A <= B) :
    compensated w A B c =
      (1-c) * weightedChebyshev w A -
        c * ((Finset.Icc 1 B) \ (Finset.Icc 1 A)).sum
          (fun n => w n * ArithmeticFunction.vonMangoldt n) := by
  have hs : Finset.Icc 1 A <= Finset.Icc 1 B := by
    intro n hn
    have h := Finset.mem_Icc.mp hn
    exact Finset.mem_Icc.mpr (And.intro h.1 (h.2.trans hAB))
  have hsplit := Finset.sum_sdiff
    (f := fun n => w n * ArithmeticFunction.vonMangoldt n) hs
  unfold compensated weightedChebyshev
  rw [<- hsplit]
  ring

def characterWeight {q : Nat} (chi : DirichletCharacter Complex q) (n : Nat) : Real :=
  2 + 2 * (chi n).re

theorem characterWeight_nonneg {q : Nat} (chi : DirichletCharacter Complex q) (n : Nat) :
    0 <= characterWeight chi n := by
  have h := (Complex.abs_re_le_norm (chi n)).trans (chi.norm_le_one _)
  have hr := (abs_le.mp h).1
  unfold characterWeight
  linarith

theorem characterWeight_product {q : Nat} (chi : DirichletCharacter Complex q)
    (a b : Nat) :
    characterWeight chi (a*b) = 2 + 2 * (chi a * chi b).re := by
  simp only [characterWeight, Nat.cast_mul, map_mul]

theorem quartic_character_kernel {q : Nat} (chi : DirichletCharacter Complex q)
    (N : Nat) (hN : 1 <= N) :
    compensated (characterWeight chi) N (N^4) (Inv.inv ((N : Real)^3)) =
      -(hyperbola (N^4)).sum (fun p =>
        (ArithmeticFunction.moebius p.1 : Real) * Real.log (p.1 : Real) *
          (2 + 2 * (chi p.1 * chi p.2).re) *
            differenceKernel N (Inv.inv ((N : Real)^3)) (p.1 * p.2)) := by
  have hstep (k : Nat) : N^k <= N^(k+1) := by
    calc
      _ = N^k * 1 := by rw [mul_one]
      _ <= N^k * N := Nat.mul_le_mul_left _ hN
      _ = _ := (pow_succ N k).symm
  have hp : N <= N^4 := by
    simpa using (hstep 1).trans ((hstep 2).trans (hstep 3))
  simpa only [characterWeight_product] using
    compensated_moebius (characterWeight chi) N (N^4) (Inv.inv ((N : Real)^3)) hp

end PrimeFactorOscillations.SignedQuarticKernel

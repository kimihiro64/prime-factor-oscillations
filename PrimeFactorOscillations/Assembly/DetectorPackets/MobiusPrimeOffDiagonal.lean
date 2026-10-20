/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Assembly.DetectorPackets.MobiusSignedDivisorTail

/-!
# MobiusPrimeOffDiagonal

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

set_option maxHeartbeats 800000

noncomputable section
open scoped BigOperators Classical

namespace PrimeFactorOscillations.MobiusPrimeOffDiagonal

open QuadraticCoprimeMean

def primeIndex (N : Nat) : Finset Nat :=
  (Finset.Ioc 1 N).filter Nat.Prime

def primeBlock (v : Nat -> Complex) (p n : Nat) : Complex :=
  if Membership.mem n.primeFactors p then
    (ArithmeticFunction.moebius n : Complex) * v n *
      ((Real.log (p : Real) / Real.log (n : Real) : Real) : Complex)
  else 0

theorem squarefree_log_partition (n : Nat) (hn : Squarefree n) (h1 : 1 < n) :
    n.primeFactors.sum (fun p => Real.log (p : Real) / Real.log (n : Real)) = 1 := by
  have hlog : Not (Real.log (n : Real) = 0) := by
    exact ne_of_gt (Real.log_pos (by exact_mod_cast h1))
  have hprod : n.primeFactors.prod (fun p => (p : Real)) = (n : Real) := by
    simpa only [Nat.cast_prod] using
      congrArg (fun k : Nat => (k : Real)) (Nat.prod_primeFactors_of_squarefree hn)
  have hsum : n.primeFactors.sum (fun p => Real.log (p : Real)) =
      Real.log (n : Real) := by
    rw [<- hprod, Real.log_prod]
    intro p hp
    exact_mod_cast (Nat.mem_primeFactors.mp hp).1.ne_zero
  rw [<- Finset.sum_div, hsum, div_self hlog]

theorem sum_primeBlock (N n : Nat) (hn : 0 < n) (hN : n <= N)
    (v : Nat -> Complex) (hv : v 1 = 0) :
    (primeIndex N).sum (fun p => primeBlock v p n) =
      (ArithmeticFunction.moebius n : Complex) * v n := by
  by_cases h1 : n = 1
  . subst n
    simp [primeBlock, hv]
  by_cases hsq : Squarefree n
  . have hlarge : 1 < n := by omega
    have hsub : forall p, Membership.mem n.primeFactors p ->
        Membership.mem (primeIndex N) p := by
      intro p hp
      have hmem := Nat.mem_primeFactors.mp hp
      apply Finset.mem_filter.mpr
      exact And.intro (Finset.mem_Ioc.mpr
        (And.intro hmem.1.one_lt ((Nat.le_of_dvd hn hmem.2.1).trans hN))) hmem.1
    have hreduce :
        (primeIndex N).sum (fun p => primeBlock v p n) =
          n.primeFactors.sum (fun p => primeBlock v p n) := by
      symm
      apply Finset.sum_subset hsub
      intro p hp hnot
      simp only [primeBlock, ite_eq_right hnot]
    rw [hreduce]
    have hcomplex :
        n.primeFactors.sum (fun p =>
          ((Real.log (p : Real) / Real.log (n : Real) : Real) : Complex)) = 1 := by
      exact_mod_cast squarefree_log_partition n hsq hlarge
    calc
      _ = n.primeFactors.sum (fun p =>
          (ArithmeticFunction.moebius n : Complex) * v n *
            ((Real.log (p : Real) / Real.log (n : Real) : Real) : Complex)) := by
        apply Finset.sum_congr rfl
        intro p hp
        exact ite_eq_left hp
      _ = (ArithmeticFunction.moebius n : Complex) * v n *
          n.primeFactors.sum (fun p =>
            ((Real.log (p : Real) / Real.log (n : Real) : Real) : Complex)) := by
        rw [Finset.mul_sum]
      _ = _ := by rw [hcomplex, mul_one]
  . have hzero := ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsq
    simp [primeBlock, hzero]

theorem primeBlock_common_divisor_zero (S T : Finset Nat) (v w : Nat -> Complex)
    (p : Nat) (hp : 1 < p) :
    coprimeForm S T (primeBlock v p) (fun n => star (primeBlock w p n)) = 0 := by
  unfold coprimeForm
  apply Finset.sum_eq_zero
  intro n hn
  apply Finset.sum_eq_zero
  intro m hm
  by_cases hcop : Nat.Coprime n m
  . rw [ite_eq_left hcop]
    by_cases hpn : Membership.mem n.primeFactors p
    . by_cases hpm : Membership.mem m.primeFactors p
      . have hdiv : Dvd.dvd p (Nat.gcd n m) :=
          Nat.dvd_gcd (Nat.mem_primeFactors.mp hpn).2.1
            (Nat.mem_primeFactors.mp hpm).2.1
        rw [hcop.gcd_eq_one] at hdiv
        have heq : p = 1 := Nat.dvd_one.mp hdiv
        omega
      . simp [primeBlock, hpm]
    . simp [primeBlock, hpn]
  . exact ite_eq_right hcop

theorem coprimeForm_sum_left (P S T : Finset Nat)
    (a : Nat -> Nat -> Complex) (b : Nat -> Complex) :
    coprimeForm S T (fun n => P.sum (fun p => a p n)) b =
      P.sum (fun p => coprimeForm S T (a p) b) := by
  unfold coprimeForm
  calc
    _ = S.sum (fun n => T.sum (fun m => P.sum (fun p =>
        if Nat.Coprime n m then a p n * b m else 0))) := by
      apply Finset.sum_congr rfl
      intro n hn
      apply Finset.sum_congr rfl
      intro m hm
      by_cases h : Nat.Coprime n m <;> simp [h, Finset.sum_mul]
    _ = _ := by
      simp_rw [Finset.sum_comm (s := T) (t := P)]
      rw [Finset.sum_comm (s := S) (t := P)]

theorem coprimeForm_sum_right (P S T : Finset Nat)
    (a : Nat -> Complex) (b : Nat -> Nat -> Complex) :
    coprimeForm S T a (fun n => P.sum (fun p => b p n)) =
      P.sum (fun p => coprimeForm S T a (b p)) := by
  unfold coprimeForm
  calc
    _ = S.sum (fun n => T.sum (fun m => P.sum (fun p =>
        if Nat.Coprime n m then a n * b p m else 0))) := by
      apply Finset.sum_congr rfl
      intro n hn
      apply Finset.sum_congr rfl
      intro m hm
      by_cases h : Nat.Coprime n m <;> simp [h, Finset.mul_sum]
    _ = _ := by
      simp_rw [Finset.sum_comm (s := T) (t := P)]
      rw [Finset.sum_comm (s := S) (t := P)]

theorem exact_prime_off_diagonal (N : Nat) (S : Finset Nat)
    (hS : forall n, Membership.mem S n -> 0 < n /\ n <= N)
    (v : Nat -> Complex) (hv : v 1 = 0) :
    coprimeForm S S
        (fun n => (ArithmeticFunction.moebius n : Complex) * v n)
        (fun n => star ((ArithmeticFunction.moebius n : Complex) * v n)) =
      (primeIndex N).sum (fun p => (primeIndex N).sum (fun q =>
        if p = q then 0 else
          coprimeForm S S (primeBlock v p) (fun n => star (primeBlock v q n)))) := by
  have hreplace :
      coprimeForm S S
        (fun n => (ArithmeticFunction.moebius n : Complex) * v n)
        (fun n => star ((ArithmeticFunction.moebius n : Complex) * v n)) =
      coprimeForm S S
        (fun n => (primeIndex N).sum (fun p => primeBlock v p n))
        (fun n => (primeIndex N).sum (fun p => star (primeBlock v p n))) := by
    unfold coprimeForm
    apply Finset.sum_congr rfl
    intro n hn
    apply Finset.sum_congr rfl
    intro m hm
    dsimp only
    rw [sum_primeBlock N n (hS n hn).1 (hS n hn).2 v hv]
    have hstar : (primeIndex N).sum (fun p => star (primeBlock v p m)) =
        star ((ArithmeticFunction.moebius m : Complex) * v m) := by
      calc
        _ = star ((primeIndex N).sum (fun p => primeBlock v p m)) :=
          (map_sum (starRingEnd Complex) (fun p => primeBlock v p m) (primeIndex N)).symm
        _ = _ := congrArg star (sum_primeBlock N m (hS m hm).1 (hS m hm).2 v hv)
    rw [hstar]
  rw [hreplace, coprimeForm_sum_left]
  apply Finset.sum_congr rfl
  intro p hp
  rw [coprimeForm_sum_right]
  apply Finset.sum_congr rfl
  intro q hq
  by_cases heq : p = q
  . subst q
    rw [ite_eq_left rfl]
    exact primeBlock_common_divisor_zero S S v v p
      (Finset.mem_Ioc.mp (Finset.mem_filter.mp hp).1).1
  . exact (ite_eq_right heq).symm

end PrimeFactorOscillations.MobiusPrimeOffDiagonal


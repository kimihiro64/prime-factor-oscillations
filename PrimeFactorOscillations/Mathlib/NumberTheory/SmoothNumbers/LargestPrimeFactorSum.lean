/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Order.Interval.Finset.Nat
import PrimeFactorOscillations.Mathlib.NumberTheory.SmoothNumbers.LargestPrimeFactor

/-!
# Disjoint largest-prime-factor sums

Each positive integer above the smoothness cutoff has the unique representation
m * p where p is prime, y < p, and largestPrimeFactor m <= p. The cofactor runs
through 1 <= m <= X / y, and every row retains its exact inclusive upper endpoint.

The resulting identities hold for arbitrary additive weights. They distinguish
an ordinary multiplicative twist from a twist of the largest factor itself.
-/

set_option autoImplicit false
set_option Elab.async false

namespace Nat

def largestPrimeFactorRow (X y m : Nat) : Finset Nat :=
  (Finset.Icc (max (y + 1) (largestPrimeFactor m)) (X / m)).filter Nat.Prime

theorem mem_largestPrimeFactorRow {X y m p : Nat} (hm : 0 < m) :
    Membership.mem (largestPrimeFactorRow X y m) p <->
      Nat.Prime p /\ y < p /\ largestPrimeFactor m <= p /\ m * p <= X := by
  simp [largestPrimeFactorRow, Finset.mem_Icc,
    Nat.le_div_iff_mul_le hm, Nat.mul_comm, and_left_comm, and_comm]

theorem largestPrimeFactor_owner {n : Nat} (hn : 1 < n) :
    0 < n / largestPrimeFactor n /\
      n / largestPrimeFactor n * largestPrimeFactor n = n /\
      largestPrimeFactor (n / largestPrimeFactor n) <= largestPrimeFactor n := by
  have hp := largestPrimeFactor_prime hn
  have hd := largestPrimeFactor_dvd hn
  refine And.intro (Nat.div_pos (Nat.le_of_dvd (Nat.zero_lt_of_lt hn) hd) hp.pos) ?_
  exact And.intro (Nat.div_mul_cancel hd)
    (largestPrimeFactor_mono_dvd (Nat.div_dvd_of_dvd hd) (Nat.ne_zero_of_lt hn))


/-- Each nonsmooth integer is counted exactly once, by its largest prime and remaining cofactor. -/
theorem sum_largePrimeFactor_eq {A : Type*} [AddCommMonoid A]
    (f : Nat -> A) (X y : Nat) (hy : 1 <= y) :
    Finset.sum ((Finset.Icc 1 X).filter (fun n => y < largestPrimeFactor n)) f =
      Finset.sum (Finset.Icc 1 (X / y)) (fun m =>
        Finset.sum (largestPrimeFactorRow X y m) (fun p => f (m * p))) := by
  symm
  rw [<- Finset.sum_sigma (Finset.Icc 1 (X / y)) (largestPrimeFactorRow X y)
    (fun a : Sigma (fun _ : Nat => Nat) => f (a.1 * a.2))]
  refine Finset.sum_bij (fun a _ => a.1 * a.2) ?_ ?_ ?_ ?_
  next =>
    intro a ha
    have hma := (Finset.mem_sigma.mp ha).1
    have hm : 0 < a.1 := lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hma).1
    have hp := (mem_largestPrimeFactorRow hm).mp (Finset.mem_sigma.mp ha).2
    apply Finset.mem_filter.mpr
    refine And.intro (Finset.mem_Icc.mpr (And.intro ?_ hp.2.2.2)) ?_
    next =>
      exact Nat.succ_le_of_lt (Nat.mul_pos hm hp.1.pos)
    next =>
      rw [largestPrimeFactor_mul_prime (Nat.ne_zero_of_lt hm) hp.1 hp.2.2.1]
      exact hp.2.1
  next =>
    intro a ha b hb hab
    have hma : 0 < a.1 :=
      lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp (Finset.mem_sigma.mp ha).1).1
    have hmb : 0 < b.1 :=
      lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp (Finset.mem_sigma.mp hb).1).1
    have hpa := (mem_largestPrimeFactorRow hma).mp (Finset.mem_sigma.mp ha).2
    have hpb := (mem_largestPrimeFactorRow hmb).mp (Finset.mem_sigma.mp hb).2
    have hpab : a.2 = b.2 := by
      calc
        a.2 = largestPrimeFactor (a.1 * a.2) :=
          (largestPrimeFactor_mul_prime (Nat.ne_zero_of_lt hma) hpa.1 hpa.2.2.1).symm
        _ = largestPrimeFactor (b.1 * b.2) := congrArg largestPrimeFactor hab
        _ = b.2 :=
          largestPrimeFactor_mul_prime (Nat.ne_zero_of_lt hmb) hpb.1 hpb.2.2.1
    have hmab : a.1 = b.1 := Nat.eq_of_mul_eq_mul_right hpb.1.pos (by
      simpa only [hpab] using hab)
    exact Sigma.ext hmab (heq_of_eq hpab)
  next =>
    intro n hn
    have hnI := Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1
    have hyn := (Finset.mem_filter.mp hn).2
    have hlpn : largestPrimeFactor n <= n := by
      apply (largestPrimeFactor_le_iff _ _).mpr
      exact And.intro hnI.1 (fun _ hp => le_of_mem_primeFactors hp)
    have hn2 : 1 < n := (lt_of_le_of_lt hy hyn).trans_le hlpn
    have owner := largestPrimeFactor_owner hn2
    let a : Sigma (fun _ : Nat => Nat) := Sigma.mk (n / largestPrimeFactor n) (largestPrimeFactor n)
    have hmem : Membership.mem
        ((Finset.Icc 1 (X / y)).sigma (largestPrimeFactorRow X y)) a := by
      apply Finset.mem_sigma.mpr
      refine And.intro (Finset.mem_Icc.mpr (And.intro owner.1 ?_)) ?_
      next =>
        apply (Nat.le_div_iff_mul_le (lt_of_lt_of_le Nat.zero_lt_one hy)).mpr
        calc
          n / largestPrimeFactor n * y <=
              n / largestPrimeFactor n * largestPrimeFactor n :=
            Nat.mul_le_mul_left _ hyn.le
          _ = n := owner.2.1
          _ <= X := hnI.2
      next =>
        apply (mem_largestPrimeFactorRow owner.1).mpr
        exact And.intro (largestPrimeFactor_prime hn2)
          (And.intro hyn (And.intro owner.2.2 (owner.2.1.le.trans hnI.2)))
    exact Exists.intro a (Exists.intro hmem owner.2.1)
  next =>
    intro a ha
    rfl


/-- Inclusive smoothness and the disjoint largest-factor rows partition the positive interval. -/
theorem sum_smoothNumbersUpTo_add_largestPrimeFactor_rows {A : Type*} [AddCommMonoid A]
    (f : Nat -> A) (X y : Nat) (hy : 1 <= y) :
    Finset.sum (smoothNumbersUpTo X (y + 1)) f +
      Finset.sum (Finset.Icc 1 (X / y)) (fun m =>
        Finset.sum (largestPrimeFactorRow X y m) (fun p => f (m * p))) =
      Finset.sum (Finset.Icc 1 X) f := by
  have hset : smoothNumbersUpTo X (y + 1) =
      (Finset.Icc 1 X).filter (fun n => largestPrimeFactor n <= y) := by
    ext n
    rw [mem_smoothNumbersUpTo, Finset.mem_filter, Finset.mem_Icc]
    constructor
    next =>
      intro h
      have hn := ne_zero_of_mem_smoothNumbers h.2
      exact And.intro (And.intro (Nat.pos_of_ne_zero hn) h.1)
        ((mem_smoothNumbers_iff_largestPrimeFactor_le hn hy).mp h.2)
    next =>
      intro h
      exact And.intro h.1.2
        ((mem_smoothNumbers_iff_largestPrimeFactor_le
          (Nat.ne_zero_of_lt h.1.1) hy).mpr h.2)
  rw [hset, <- sum_largePrimeFactor_eq f X y hy]
  simpa only [not_le] using
    Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 X)
      (fun n => largestPrimeFactor n <= y) f

/-- Twisting the largest factor itself removes the cofactor weight, with no approximation. -/
theorem sum_largePrimeFactor_twist_eq {A : Type*} [AddCommMonoid A]
    (f : Nat -> A) (X y : Nat) (hy : 1 <= y) :
    Finset.sum ((Finset.Icc 1 X).filter (fun n => y < largestPrimeFactor n))
      (fun n => f (largestPrimeFactor n)) =
      Finset.sum (Finset.Icc 1 (X / y)) (fun m =>
        Finset.sum (largestPrimeFactorRow X y m) f) := by
  rw [sum_largePrimeFactor_eq _ X y hy]
  apply Finset.sum_congr rfl
  intro m hm
  have hmpos : 0 < m := (Finset.mem_Icc.mp hm).1
  apply Finset.sum_congr rfl
  intro p hp
  have h := (mem_largestPrimeFactorRow hmpos).mp hp
  rw [largestPrimeFactor_mul_prime (Nat.ne_zero_of_lt hmpos) h.1 h.2.2.1]

end Nat

/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.PrimeClassDecoderIntegerSignal

/-!
# Adjacent integer signs recover the actual prime-class label

The prefix count changes by exactly one at a class prime and by zero
otherwise. Both integer signs are retained when reading that increment.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.PrimeClassSampling

open PrimeFactorOscillations.PrimeClassDecoder

noncomputable def primeClassLabelBit (P : Set Nat) (p : Nat) : Nat := by
  classical
  exact if And (Nat.Prime p) (Membership.mem P p) then 1 else 0

theorem primeClassPrefix_succ_card
    (P : Set Nat) (n : Nat) (hn : 1 <= n) :
    (primeClassPrefix P (n + 1)).card = (primeClassPrefix P n).card +
      primeClassLabelBit P (n + 1) := by
  classical
  have hbase : Finset.Icc 2 (n + 1) = insert (n + 1) (Finset.Icc 2 n) := by
    apply Finset.ext
    intro p
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  have hnot : Not (Membership.mem ((Finset.Icc 2 n).filter
      (fun p => And (Nat.Prime p) (Membership.mem P p))) (n + 1)) := by
    intro h
    have hup := (Finset.mem_Icc.mp (Finset.mem_filter.mp h).1).2
    omega
  unfold primeClassPrefix primeClassLabelBit
  rw [hbase, Finset.filter_insert]
  by_cases hA : And (Nat.Prime (n + 1)) (Membership.mem P (n + 1))
  case pos => simp only [ite_eq_left hA, Finset.card_insert_of_notMem hnot]
  case neg => simp only [ite_eq_right hA, Nat.add_zero]

theorem parity_aligned_mul_neg_iff
    (A : Prop) [Decidable A] (k : Nat) (a b : Real)
    (ha : 0 < (-1 : Real) ^ k * a)
    (hb : 0 < (-1 : Real) ^ (k + (if A then 1 else 0)) * b) :
    a * b < 0 <-> A := by
  have hq : (-1 : Real) ^ k * (-1 : Real) ^ k = 1 := by
    calc
      _ = ((-1 : Real) ^ k) ^ 2 := by ring
      _ = ((-1 : Real) ^ 2) ^ k := by rw [<- pow_mul, <- pow_mul, Nat.mul_comm k 2]
      _ = _ := by norm_num
  by_cases hA : A
  case pos =>
    rw [ite_eq_left hA, pow_succ] at hb
    have hprod := mul_pos ha hb
    have hid : ((-1 : Real) ^ k * a) * (((-1 : Real) ^ k * (-1)) * b) = -(a * b) := by
      calc
        _ = -((-1 : Real) ^ k * (-1 : Real) ^ k) * (a * b) := by ring
        _ = _ := by rw [hq]; ring
    rw [hid] at hprod
    exact iff_of_true (by linarith) hA
  case neg =>
    rw [ite_eq_right hA, Nat.add_zero] at hb
    have hprod := mul_pos ha hb
    have hid : ((-1 : Real) ^ k * a) * ((-1 : Real) ^ k * b) = a * b := by
      calc
        _ = ((-1 : Real) ^ k * (-1 : Real) ^ k) * (a * b) := by ring
        _ = _ := by rw [hq, one_mul]
    rw [hid] at hprod
    exact iff_of_false (not_lt_of_ge hprod.le) hA

theorem integerProbe_adjacent_neg_iff
    (P : Set Nat) (N M R n : Nat) (hn : 1 <= n) (hnR : n <= R)
    (hpos : forall j : Nat, j <= R ->
      0 < (-1 : Real) ^ (primeClassPrefix P (j + 1)).card *
        (integerProbe M (sampleCount P N) j : Real)) :
    integerProbe M (sampleCount P N) (n - 1) * integerProbe M (sampleCount P N) n < 0 <->
      And (Nat.Prime (n + 1)) (Membership.mem P (n + 1)) := by
  classical
  have hprev := hpos (n - 1) (by omega)
  have hnext := hpos n hnR
  rw [Nat.sub_add_cancel hn] at hprev
  rw [primeClassPrefix_succ_card P n hn] at hnext
  unfold primeClassLabelBit at hnext
  have hscalar := parity_aligned_mul_neg_iff
    (And (Nat.Prime (n + 1)) (Membership.mem P (n + 1))) (primeClassPrefix P n).card
    (integerProbe M (sampleCount P N) (n - 1) : Real)
    (integerProbe M (sampleCount P N) n : Real) hprev hnext
  have hcast : (integerProbe M (sampleCount P N) (n - 1) : Real) *
      (integerProbe M (sampleCount P N) n : Real) < 0 <->
      integerProbe M (sampleCount P N) (n - 1) * integerProbe M (sampleCount P N) n < 0 := by
    norm_cast
  exact hcast.symm.trans hscalar

end PrimeFactorOscillations.PrimeClassSampling

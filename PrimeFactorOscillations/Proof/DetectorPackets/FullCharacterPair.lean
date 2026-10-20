/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.Tactic.Ring

/-!
# FullCharacterPair

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


noncomputable section

namespace PrimeFactorOscillations.FullCharacterPair

theorem finite_pair_diagonal
    (q : Nat) [NeZero q] (S : Finset Nat)
    (hunit : forall a, Membership.mem S a -> IsUnit (a : ZMod q))
    (hinj : forall a, Membership.mem S a ->
      forall b, Membership.mem S b -> (a : ZMod q) = (b : ZMod q) -> a = b)
    (f g : Nat -> Complex) :
    Finset.univ.sum (fun xi : DirichletCharacter Complex q =>
      (S.sum (fun a => f a * xi (Inv.inv (a : ZMod q)))) *
      (S.sum (fun b => g b * xi (b : ZMod q)))) =
      (q.totient : Complex) * S.sum (fun a => f a * g a) := by
  classical
  calc
    Finset.univ.sum (fun xi : DirichletCharacter Complex q =>
        (S.sum (fun a => f a * xi (Inv.inv (a : ZMod q)))) *
        (S.sum (fun b => g b * xi (b : ZMod q)))) =
      S.sum (fun a => S.sum (fun b =>
        (f a * g b) * Finset.univ.sum (fun xi : DirichletCharacter Complex q =>
          xi (Inv.inv (a : ZMod q)) * xi (b : ZMod q)))) := by
        simp_rw [Finset.sum_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro a ha
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro b hb
        apply Finset.sum_congr rfl
        intro xi hxi
        ring
    _ = S.sum (fun a => (q.totient : Complex) * (f a * g a)) := by
      apply Finset.sum_congr rfl
      intro a ha
      simp_rw [DirichletCharacter.sum_char_inv_mul_char_eq Complex (hunit a ha)]
      rw [Finset.sum_eq_single a]
      next =>
        simp
        ring
      next =>
        intro b hb hba
        have hab : Not ((a : ZMod q) = (b : ZMod q)) := by
          intro heq
          exact hba (hinj a ha b hb heq).symm
        simp [hab]
      next =>
        intro hnot
        exact (hnot ha).elim
    _ = (q.totient : Complex) * S.sum (fun a => f a * g a) := by
      rw [Finset.mul_sum]

def mu (n : Nat) : Complex :=
  ((ArithmeticFunction.moebius n : Int) : Complex)

theorem annular_moebius_character_pair
    (N q r : Nat) (hN : 0 < N) (hq : Nat.Prime q) (hsize : 2 * N <= q)
    (chi : DirichletCharacter Complex r) :
    Finset.univ.sum (fun xi : DirichletCharacter Complex q =>
      ((Finset.Ico N (2 * N)).sum
        (fun a => mu a * xi (Inv.inv (a : ZMod q)))) *
      ((Finset.Ico N (2 * N)).sum
        (fun b => chi b * xi (b : ZMod q)))) =
      (q.totient : Complex) *
        (Finset.Ico N (2 * N)).sum (fun a => mu a * chi a) := by
  classical
  have : NeZero q := NeZero.mk hq.ne_zero
  have : Fact (Nat.Prime q) := Fact.mk hq
  apply finite_pair_diagonal q (Finset.Ico N (2 * N))
  next =>
    intro a ha
    have haBounds := Finset.mem_Ico.mp ha
    have halt : a < q := lt_of_lt_of_le haBounds.2 hsize
    have hapos : 0 < a := lt_of_lt_of_le hN haBounds.1
    apply isUnit_iff_ne_zero.mpr
    intro hz
    have hmod := (ZMod.natCast_eq_natCast_iff' a 0 q).mp
      (by simpa only [Nat.cast_zero] using hz)
    have ha0 : a = 0 := by
      simpa only [Nat.mod_eq_of_lt halt, Nat.zero_mod] using hmod
    exact (Nat.ne_of_gt hapos) ha0
  next =>
    intro a ha b hb heq
    have halt : a < q := lt_of_lt_of_le (Finset.mem_Ico.mp ha).2 hsize
    have hblt : b < q := lt_of_lt_of_le (Finset.mem_Ico.mp hb).2 hsize
    have hmod := (ZMod.natCast_eq_natCast_iff' a b q).mp heq
    simpa only [Nat.mod_eq_of_lt halt, Nat.mod_eq_of_lt hblt] using hmod

end PrimeFactorOscillations.FullCharacterPair

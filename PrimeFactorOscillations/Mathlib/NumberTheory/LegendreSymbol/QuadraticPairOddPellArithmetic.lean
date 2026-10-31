/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Mathlib.NumberTheory.LegendreSymbol.QuadraticPairOddPellSectors
import PrimeFactorOscillations.Mathlib.NumberTheory.LegendreSymbol.QuadraticPairSquareExtremal

/-!
# Arithmetic inputs to the odd Pell semigroup optimum

Positive naturals admit an odd part and a power-of-two factor.
Odd gcds are bounded by that part, and one odd product simultaneously
attains the two required gcd maxima. The finite-field character phase
modulo four is recovered from the already proved exact core-count law.
These inputs do not by themselves assert the optimized weighted mean.
-/

set_option autoImplicit false
set_option Elab.async false

namespace FiniteField

theorem oddPell_exists_two_part (n : Nat) (hn : 0<n) :
    exists s : Nat, exists u : Nat, Odd u /\ n=2^s*u := by
  classical
  revert hn
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    apply Or.elim (Nat.even_or_odd n)
    . intro he
      let a : Nat := Classical.choose he
      have ha : n=a+a := Classical.choose_spec he
      have hapos : 0<a := by omega
      have halt : a<n := by omega
      have hex := ih a halt hapos
      let s : Nat := Classical.choose hex
      have hexu : exists u : Nat, Odd u /\ a=2^s*u := Classical.choose_spec hex
      let u : Nat := Classical.choose hexu
      have hu : Odd u /\ a=2^s*u := Classical.choose_spec hexu
      apply Exists.intro (s+1)
      apply Exists.intro u
      apply And.intro hu.1
      calc
        n=a+a := ha
        _ = 2*a := by omega
        _ = 2*(2^s*u) := by rw [hu.2]
        _ = 2^(s+1)*u := by rw [pow_succ]; ring
    . intro ho
      exact Exists.intro 0 (Exists.intro n (And.intro ho (by simp)))

theorem oddPell_gcd_odd_bound (n s u m : Nat)
    (hn : n=2^s*u) (hu : Odd u) (hm : Odd m) :
    n.gcd m<=u := by
  have hc : Nat.Coprime (2^s) m :=
    Nat.Coprime.pow_left s (Nat.coprime_two_left.mpr hm)
  have hu0 : 0<u := by
    let a : Nat := Classical.choose hu
    have ha : u=2*a+1 := Classical.choose_spec hu
    omega
  rw [hn,Nat.Coprime.gcd_mul_left_cancel u hc]
  exact Nat.le_of_dvd hu0 (Nat.gcd_dvd_left u m)

theorem oddPell_gcd_odd_product_left (n s u v : Nat)
    (hn : n=2^s*u) (hu : Odd u) (hv : Odd v) :
    n.gcd (u*v)=u := by
  have hc : Nat.Coprime (2^s) (u*v) :=
    Nat.Coprime.pow_left s (Nat.coprime_two_left.mpr (hu.mul hv))
  rw [hn,Nat.Coprime.gcd_mul_left_cancel u hc]
  apply Nat.gcd_eq_left_iff_dvd.mpr
  exact Exists.intro v rfl

theorem oddPell_gcd_odd_product_right (n s u v : Nat)
    (hn : n=2^s*v) (hu : Odd u) (hv : Odd v) :
    n.gcd (u*v)=v := by
  simpa only [Nat.mul_comm v u] using
    (oddPell_gcd_odd_product_left n s v u hn hv hu)

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem oddPell_character_mod_four (hF : Not (ringChar F=2)) :
    ((quadraticChar F) (-1)=1 /\ Fintype.card F%4=1) \/
      ((quadraticChar F) (-1)=-1 /\ Fintype.card F%4=3) := by
  have htwo : Not ((2 : F)=0) := _root_.FiniteField.two_ne_zero_of_odd hF
  have hi := sum_squarePairCore_indicator hF (2 : F) htwo
  have hs := quadraticChar_sq_one (neg_ne_zero.mpr (one_ne_zero : Not ((1 : F)=0)))
  have hp : ((quadraticChar F) (-1)-1)*((quadraticChar F) (-1)+1)=0 := by
    nlinarith only [hs]
  apply Or.elim (mul_eq_zero.mp hp)
  . intro he
    have ht : (quadraticChar F) (-1)=1 := sub_eq_zero.mp he
    apply Or.inl
    apply And.intro ht
    rw [ht] at hi
    omega
  . intro he
    have ht : (quadraticChar F) (-1)=-1 := eq_neg_of_add_eq_zero_left he
    apply Or.inr
    apply And.intro ht
    rw [ht] at hi
    omega

end FiniteField

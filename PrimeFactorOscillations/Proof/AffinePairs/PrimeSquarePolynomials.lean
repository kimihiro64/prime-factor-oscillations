import PrimeFactorOscillations.Mathlib.NumberTheory.LegendreSymbol.QuadraticSquareDensity
import PrimeFactorOscillations.Proof.AffinePairs.PrimeSquareSieve

/-! # Prime-relative sparsity of affine and split quadratic square values

Positive leading coefficients and distinct roots are fixed. All exceptional
test primes are excluded by one fixed cutoff; sampled primes are not excluded.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations

open scoped Classical
attribute [local instance] Classical.propDecidable

theorem tendsto_prime_affine_square_values_zero (t a : Nat) (ht : 0 < t) :
    Filter.Tendsto (fun N : Nat =>
      (((Nat.primesLE N).filter (fun (n : Nat) =>
        IsSquare ((t : Int) * ((n : Int) - (a : Int))))).card : Real) /
          (Nat.primeCounting N : Real)) Filter.atTop (nhds 0) := by
  apply tendsto_prime_square_values_zero_of_unit_tests
    (fun n => (t : Int) * ((n : Int) - (a : Int)))
    (fun ell x => (t : ZMod ell) * (x - (a : ZMod ell)))
    (max 11 (t + 1))
  . intro ell n
    simp only [Int.cast_mul, Int.cast_sub, Int.cast_natCast]
  . intro ell hprime hell
    have : Fact (Nat.Prime ell) := Fact.mk hprime
    have : NeZero ell := NeZero.mk hprime.ne_zero
    have htcast : Not ((t : ZMod ell) = 0) := by
      intro hz
      have hd := (CharP.cast_eq_zero_iff (ZMod ell) ell t).mp hz
      have hle := Nat.le_of_dvd ht hd
      omega
    have hodd : Not (ringChar (ZMod ell) = 2) := by
      rw [ZMod.ringChar_zmod_n]
      omega
    have hsize : 11 <= Fintype.card (ZMod ell) := by
      rw [ZMod.card]
      omega
    have hbound := FiniteField.four_affine_unit_square_card_le_three hodd hsize
      (t : ZMod ell) (-((t : ZMod ell) * (a : ZMod ell))) htcast
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype, Nat.totient_prime hprime]
    simpa only [ZMod.card, sub_eq_add_neg, mul_add, mul_neg] using hbound

theorem tendsto_prime_split_quadratic_square_values_zero
    (t a b : Nat) (ht : 0 < t) (hab : Not (a = b)) :
    Filter.Tendsto (fun N : Nat =>
      (((Nat.primesLE N).filter (fun (n : Nat) =>
        IsSquare ((t : Int) * ((n : Int) - (a : Int)) *
          ((n : Int) - (b : Int))))).card : Real) /
          (Nat.primeCounting N : Real)) Filter.atTop (nhds 0) := by
  apply tendsto_prime_square_values_zero_of_unit_tests
    (fun n => (t : Int) * ((n : Int) - (a : Int)) * ((n : Int) - (b : Int)))
    (fun ell x => (t : ZMod ell) * (x - (a : ZMod ell)) * (x - (b : ZMod ell)))
    (max 11 (t + a + b + 1))
  . intro ell n
    simp only [Int.cast_mul, Int.cast_sub, Int.cast_natCast]
  . intro ell hprime hell
    have : Fact (Nat.Prime ell) := Fact.mk hprime
    have : NeZero ell := NeZero.mk hprime.ne_zero
    have htcast : Not ((t : ZMod ell) = 0) := by
      intro hz
      have hd := (CharP.cast_eq_zero_iff (ZMod ell) ell t).mp hz
      have hle := Nat.le_of_dvd ht hd
      omega
    have ha : a < ell := by omega
    have hb : b < ell := by omega
    have habcast : Not ((a : ZMod ell) = (b : ZMod ell)) := by
      intro heq
      have hv := congrArg ZMod.val heq
      simp only [ZMod.val_natCast, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at hv
      exact hab hv
    have hodd : Not (ringChar (ZMod ell) = 2) := by
      rw [ZMod.ringChar_zmod_n]
      omega
    have hsize : 11 <= Fintype.card (ZMod ell) := by
      rw [ZMod.card]
      omega
    have hbound := FiniteField.four_split_quadratic_unit_square_card_le_three
      hodd hsize (t : ZMod ell) (a : ZMod ell) (b : ZMod ell) htcast habcast
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype, Nat.totient_prime hprime]
    simpa only [ZMod.card] using hbound

end PrimeFactorOscillations

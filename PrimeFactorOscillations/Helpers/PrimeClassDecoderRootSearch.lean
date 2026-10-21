/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.PrimeClassDecoderRationalCutoffs

/-!
# A root search that stops after the actual cutoff

The fuel is an a priori termination bound, not the number of tests.
Starting at zero, the algorithm makes at most root+1 power tests.
Thus the executable cutoff need not scan down from the much larger Y.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.PrimeClassDecoder

structure IntegerRootSearchState where
  value : Nat
  tests : Nat

def integerRootForward (Y b r : Nat) : Nat -> IntegerRootSearchState
  | 0 => { value := r, tests := 0 }
  | fuel + 1 =>
    if (r + 1) ^ b <= Y then
      let next := integerRootForward Y b (r + 1) fuel
      { value := next.value, tests := next.tests + 1 }
    else
      { value := r, tests := 1 }

def fastIntegerRootCutoff (Y b : Nat) : Nat :=
  (integerRootForward Y b 0 (Y + 1)).value

def fastRationalDecoderRadius (a b N : Nat) : Nat :=
  fastIntegerRootCutoff (binaryCutoff N ^ a) b

theorem integerRootCutoff_predicate_iff (Y b r : Nat) (hb : 1 <= b) :
    r ^ b <= Y <-> r <= integerRootCutoff Y b := by
  apply Iff.intro
  case mp => exact integerRootCutoff_maximal Y b r hb
  case mpr =>
    intro hr
    have hpow : r ^ b <= (integerRootCutoff Y b) ^ b := by gcongr
    exact hpow.trans (integerRootCutoff_pow_le Y b hb)

theorem integerRootForward_value
    (Y b r fuel : Nat) (hb : 1 <= b) (hr : r <= integerRootCutoff Y b) :
    (integerRootForward Y b r fuel).value = min (integerRootCutoff Y b) (r + fuel) := by
  induction fuel generalizing r with
  | zero => simpa only [integerRootForward, Nat.add_zero] using (Nat.min_eq_right hr).symm
  | succ fuel ih =>
    by_cases hp : (r + 1) ^ b <= Y
    case pos =>
      have hnext : r + 1 <= integerRootCutoff Y b :=
        (integerRootCutoff_predicate_iff Y b (r + 1) hb).mp hp
      simp only [integerRootForward, hp, ite_true]
      rw [ih (r + 1) hnext]
      congr 1
      omega
    case neg =>
      have hnext : Not (r + 1 <= integerRootCutoff Y b) := by
        intro h
        exact hp ((integerRootCutoff_predicate_iff Y b (r + 1) hb).mpr h)
      have heq : r = integerRootCutoff Y b := by omega
      simp only [integerRootForward, hp, ite_false]
      rw [heq]
      exact (Nat.min_eq_left (by omega)).symm

theorem integerRootForward_tests_le
    (Y b r fuel : Nat) (hb : 1 <= b) (hr : r <= integerRootCutoff Y b) :
    (integerRootForward Y b r fuel).tests <= integerRootCutoff Y b - r + 1 := by
  induction fuel generalizing r with
  | zero => simp only [integerRootForward]; omega
  | succ fuel ih =>
    by_cases hp : (r + 1) ^ b <= Y
    case pos =>
      have hnext : r + 1 <= integerRootCutoff Y b :=
        (integerRootCutoff_predicate_iff Y b (r + 1) hb).mp hp
      have hchild := ih (r + 1) hnext
      simp only [integerRootForward, hp, ite_true]
      omega
    case neg =>
      simp only [integerRootForward, hp, ite_false]
      omega

theorem fastIntegerRootCutoff_eq (Y b : Nat) (hb : 1 <= b) :
    fastIntegerRootCutoff Y b = integerRootCutoff Y b := by
  have hbound : integerRootCutoff Y b <= Y := Nat.findGreatest_le Y
  unfold fastIntegerRootCutoff
  rw [integerRootForward_value Y b 0 (Y + 1) hb (Nat.zero_le _)]
  simp only [Nat.zero_add]
  exact Nat.min_eq_left (by omega)

theorem fastIntegerRootCutoff_tests_le (Y b : Nat) (hb : 1 <= b) :
    (integerRootForward Y b 0 (Y + 1)).tests <= fastIntegerRootCutoff Y b + 1 := by
  rw [fastIntegerRootCutoff_eq Y b hb]
  simpa only [Nat.sub_zero] using integerRootForward_tests_le Y b 0 (Y + 1) hb (Nat.zero_le _)

theorem fastRationalDecoderRadius_eq (a b N : Nat) (hb : 1 <= b) :
    fastRationalDecoderRadius a b N = decoderRadius ((a : Real) / (b : Real)) N := by
  unfold fastRationalDecoderRadius
  rw [fastIntegerRootCutoff_eq _ b hb]
  exact rationalDecoderRadius_eq a b N hb

end PrimeFactorOscillations.PrimeClassDecoder

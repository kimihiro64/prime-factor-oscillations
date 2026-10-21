/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.PrimeClassDecoderLogCutoffs

/-!
# An explicit division algorithm for both binary cutoffs

The fuel guarantees termination. The actual number of visited tests is
exactly Nat.log 2 n + 1, including n=0 and n=1.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.PrimeClassDecoder

structure DecoderBinaryLogState where
  value : Nat
  tests : Nat

def decoderBinaryLogState (n : Nat) : Nat -> DecoderBinaryLogState
  | 0 => { value := 0, tests := 0 }
  | fuel + 1 =>
    if n < 2 then
      { value := 0, tests := 1 }
    else
      let next := decoderBinaryLogState (n / 2) fuel
      { value := next.value + 1, tests := next.tests + 1 }

def executableBinaryCutoff (N : Nat) : Nat :=
  (decoderBinaryLogState N (N + 1)).value

theorem decoderBinaryLogState_correct
    (n fuel : Nat) (hfuel : n < fuel) :
    And ((decoderBinaryLogState n fuel).value = Nat.log 2 n)
      ((decoderBinaryLogState n fuel).tests = Nat.log 2 n + 1) := by
  induction fuel generalizing n with
  | zero => omega
  | succ fuel ih =>
    by_cases hn : n < 2
    case pos =>
      simp only [decoderBinaryLogState, hn, ite_true, Nat.log_of_lt hn]
      exact And.intro True.intro True.intro
    case neg =>
      have hn2 : 2 <= n := by omega
      have hdiv : n / 2 < n := Nat.div_lt_self (by omega) (by omega)
      have hchild := ih (n / 2) (by omega)
      have hlog : 1 <= Nat.log 2 n := by
        have hmono := Nat.log_mono_right (b := 2) hn2
        simpa only [show Nat.log 2 2 = 1 by decide] using hmono
      have hrec := Nat.log_div_base 2 n
      simp only [decoderBinaryLogState, hn, ite_false]
      exact And.intro (by omega) (by omega)

theorem executableBinaryCutoff_eq (N : Nat) :
    executableBinaryCutoff N = binaryCutoff N := by
  exact (decoderBinaryLogState_correct N (N + 1) (Nat.lt_succ_self N)).1

theorem decoderBinaryCutoff_tests (N : Nat) :
    (decoderBinaryLogState N (N + 1)).tests = binaryCutoff N + 1 :=
  (decoderBinaryLogState_correct N (N + 1) (Nat.lt_succ_self N)).2

end PrimeFactorOscillations.PrimeClassDecoder

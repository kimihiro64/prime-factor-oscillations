/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Assembly.DetectorPackets.MobiusCompensatedCovariance

/-!
# PrimeCompensationMarginal

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

/-!
Prime-supported compensation cannot change the nonunit divisor marginals
below the prime support. The signed low-divisor packet is retained exactly;
this is a constraint on a proposed cancellation mechanism, not a power bound.
-/


noncomputable section

namespace PrimeFactorOscillations.PrimeCompensationMarginal

open QuadraticCoprimeMean MobiusCompensatedCovariance

theorem prime_supported_multipleSum_zero
    (D d : Nat) (S : Finset Nat) (b : Nat -> Complex)
    (hd : 2 <= d) (hdD : d <= D)
    (hb : forall n, Membership.mem S n -> Not (b n = 0) ->
      Nat.Prime n /\ D < n) :
    multipleSum d S b = 0 := by
  classical
  unfold multipleSum
  apply Finset.sum_eq_zero
  intro n hn
  by_cases hz : b n = 0
  . simp only [hz, ite_self]
  . by_cases hdiv : Dvd.dvd d n
    . have hp : Nat.Prime n := (hb n hn hz).1
      have hlarge : D < n := (hb n hn hz).2
      have hor : Or (d = 1) (d = n) := (Nat.dvd_prime hp).mp hdiv
      have hf : False := by
        cases hor with
        | inl he => omega
        | inr he => omega
      exact False.elim hf
    . simp only [if_neg hdiv]

theorem compensated_multipleSum_eq
    (D d : Nat) (S : Finset Nat) (a b : Nat -> Complex) (c : Complex)
    (hd : 2 <= d) (hdD : d <= D)
    (hb : forall n, Membership.mem S n -> Not (b n = 0) ->
      Nat.Prime n /\ D < n) :
    multipleSum d S (fun n => a n - c * b n) = multipleSum d S a := by
  rw [multipleSum_sub_scale,
    prime_supported_multipleSum_zero D d S b hd hdD hb, mul_zero, sub_zero]

theorem signed_low_packet_unchanged
    (D : Nat) (R S : Finset Nat) (a b : Nat -> Complex)
    (c : Complex) (weight : Nat -> Complex)
    (hR : forall d, Membership.mem R d -> 2 <= d /\ d <= D)
    (hb : forall n, Membership.mem S n -> Not (b n = 0) ->
      Nat.Prime n /\ D < n) :
    R.sum (fun d => weight d *
      multipleSum d S (fun n => a n - c * b n) *
      star (multipleSum d S (fun n => a n - c * b n))) =
    R.sum (fun d => weight d * multipleSum d S a *
      star (multipleSum d S a)) := by
  apply Finset.sum_congr rfl
  intro d hd
  have he := compensated_multipleSum_eq D d S a b c
    (hR d hd).1 (hR d hd).2 hb
  rw [he]

end PrimeFactorOscillations.PrimeCompensationMarginal

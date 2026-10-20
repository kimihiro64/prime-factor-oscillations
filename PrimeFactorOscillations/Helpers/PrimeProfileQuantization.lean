/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Helpers.PrimeProfileTransportTail

/-!
# Probe-independent even levels of bounded prime-profile distortion

One eventually bounded positive probe forces one even limiting level.
The eventual upper bound is uniform over every new positive probe.
The arbitrarily late lower witnesses also work for all probes at once.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations.PrimeProfileRigidity

theorem bounded_probe_quantized_uniform_envelope
    (e : Equiv.Perm Nat) (t : Nat -> Real) (ht : forall n, 0 < t n)
    (C : Real) (hC0 : 0 <= C)
    (hupper : exists M : Nat, forall n : Nat, M <= n ->
      normalizedPrimePrefixDefect e t n <= C) :
    exists K : Nat,
      (forall eps : Real, 0 < eps -> exists M : Nat,
        forall n : Nat, M <= n -> forall v : Nat -> Real, 0 < v n ->
          normalizedPrimePrefixDefect e v n <= 2 * (K : Real) + eps) /\
      (forall eps : Real, 0 < eps -> forall N : Nat,
        exists n : Nat, N <= n /\
          forall v : Nat -> Real, 0 < v n ->
            2 * (K : Real) - eps <= normalizedPrimePrefixDefect e v n) := by
  classical
  let S : Nat -> Real := fun n => Finset.prefixDefect
    (fun j => (PrimeFactorUnimodality.primeAt j : Real)) e (n + 1)
  have hlattice := eventually_prime_transport_lattice e t ht C hC0 hupper
  let L := Classical.choose hlattice
  have hL : forall n : Nat, L <= n ->
      (exists k : Nat, S n = 2 * (k : Real)) /\ S n <= 4 * C :=
    Classical.choose_spec hlattice
  let f : Nat -> Nat := fun n =>
    if h : exists k : Nat, S n = 2 * (k : Real) then Classical.choose h else 0
  have hfn : forall n : Nat, L <= n -> S n = 2 * (f n : Real) := by
    intro n hn
    have hex : exists k : Nat, S n = 2 * (k : Real) := (hL n hn).1
    dsimp only [f]
    rw [dite_eq_left hex]
    exact Classical.choose_spec hex
  have hfReal : forall n : Nat, L <= n -> (f n : Real) <= 2 * C := by
    intro n hn
    have hb := (hL n hn).2
    rw [hfn n hn] at hb
    linarith only [hb]
  have hlargeB : exists B : Nat, 2 * C < (B : Real) := exists_nat_gt _
  let B := Classical.choose hlargeB
  have hB : 2 * C < (B : Real) := Classical.choose_spec hlargeB
  have hfbound : exists B : Nat, exists M : Nat,
      forall n : Nat, M <= n -> f n <= B := by
    refine Exists.intro B (Exists.intro L ?_)
    intro n hn
    have hb : (f n : Real) <= (B : Real) := (hfReal n hn).trans hB.le
    exact_mod_cast hb
  have hpeak := Nat.exists_eventual_maximum_recurrent f hfbound
  let K := Classical.choose hpeak
  have hK :
      (exists M : Nat, forall n : Nat, M <= n -> f n <= K) /\
      (forall N : Nat, exists n : Nat, N <= n /\ f n = K) :=
    Classical.choose_spec hpeak
  refine Exists.intro K (And.intro ?_ ?_)
  . intro eps heps
    let P := Classical.choose hK.1
    have hP : forall n : Nat, P <= n -> f n <= K := Classical.choose_spec hK.1
    have hevent := eventually_uniform_prime_transport_error e t ht C hC0 hupper eps heps
    let E := Classical.choose hevent
    have hE : forall n : Nat, E <= n -> forall v : Nat -> Real, 0 < v n ->
        abs (normalizedPrimePrefixDefect e v n - S n) < eps :=
      Classical.choose_spec hevent
    refine Exists.intro (max L (max P E)) ?_
    intro n hn v hv
    have hLn : L <= n := (le_max_left L (max P E)).trans hn
    have hPE : max P E <= n := (le_max_right L (max P E)).trans hn
    have hPn : P <= n := (le_max_left P E).trans hPE
    have hEn : E <= n := (le_max_right P E).trans hPE
    have hSn := hfn n hLn
    have hfK : (f n : Real) <= (K : Real) := by exact_mod_cast hP n hPn
    have hdiff := (abs_lt.mp (hE n hEn v hv)).2
    linarith only [hSn, hfK, hdiff]
  . intro eps heps N
    have hevent := eventually_uniform_prime_transport_error e t ht C hC0 hupper eps heps
    let E := Classical.choose hevent
    have hE : forall n : Nat, E <= n -> forall v : Nat -> Real, 0 < v n ->
        abs (normalizedPrimePrefixDefect e v n - S n) < eps :=
      Classical.choose_spec hevent
    let n := Classical.choose (hK.2 (max N (max L E)))
    have hn : max N (max L E) <= n /\ f n = K :=
      Classical.choose_spec (hK.2 (max N (max L E)))
    have hLE : max L E <= n := (le_max_right N (max L E)).trans hn.1
    have hLn : L <= n := (le_max_left L E).trans hLE
    have hEn : E <= n := (le_max_right L E).trans hLE
    have hSn := hfn n hLn
    rw [hn.2] at hSn
    refine Exists.intro n (And.intro ((le_max_left N (max L E)).trans hn.1) ?_)
    intro v hv
    have hdiff := (abs_lt.mp (hE n hEn v hv)).1
    linarith only [hSn, hdiff]

end PrimeFactorOscillations.PrimeProfileRigidity

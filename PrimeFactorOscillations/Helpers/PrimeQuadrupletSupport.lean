/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Helpers.PrimeProfileQuadrupletInverse
import PrimeFactorOscillations.Mathlib.Combinatorics.TwoStepSwapPrefix

/-!
# Sparse supports for four-prime probability-profile transport

Recurrent short quadruplets supply disjoint four-coordinate blocks.
The two distance-two edges in each block both have prime displacement six.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations.PrimeProfileRigidity

theorem exists_unbounded_quadruplet_twoStepSupport
    (hrec : forall N : Nat, exists k : Nat, N <= k /\ IsShortPrimeQuadruplet k) :
    exists B : Set Nat,
      (forall n, Membership.mem B n -> Not (Membership.mem B (n + 2))) /\
      (forall n, Membership.mem B n ->
        PrimeFactorUnimodality.primeAt (n + 2) =
          PrimeFactorUnimodality.primeAt n + 6) /\
      (forall N : Nat, exists k : Nat, N <= k /\
        Membership.mem B k /\ Membership.mem B (k + 1)) := by
  let S : Set Nat := {k | IsShortPrimeQuadruplet k}
  have hs := Set.exists_unbounded_separated_subset S hrec 4 (by decide)
  let A := Classical.choose hs
  have hA : (forall n, Membership.mem A n -> Membership.mem S n) /\
      (forall a, Membership.mem A a -> forall b, Membership.mem A b ->
        a < b -> a + 4 <= b) /\
      (forall N : Nat, exists n : Nat, N <= n /\ Membership.mem A n) :=
    Classical.choose_spec hs
  let B : Set Nat := {n | exists a : Nat,
    Membership.mem A a /\ (n = a \/ n = a + 1)}
  have hB : forall n, Membership.mem B n -> Not (Membership.mem B (n + 2)) := by
    intro n hn hn2
    let a := Classical.choose hn
    have ha : Membership.mem A a /\ (n = a \/ n = a + 1) := Classical.choose_spec hn
    let b := Classical.choose hn2
    have hb : Membership.mem A b /\ (n + 2 = b \/ n + 2 = b + 1) :=
      Classical.choose_spec hn2
    have hab : a < b := by omega
    have hsep := hA.2.1 a ha.1 b hb.1 hab
    omega
  have hgap : forall n, Membership.mem B n ->
      PrimeFactorUnimodality.primeAt (n + 2) =
        PrimeFactorUnimodality.primeAt n + 6 := by
    intro n hn
    let a := Classical.choose hn
    have ha : Membership.mem A a /\ (n = a \/ n = a + 1) := Classical.choose_spec hn
    have hquad : IsShortPrimeQuadruplet a := hA.1 a ha.1
    cases ha.2 with
    | inl he =>
      rw [he]
      cases hquad.2 with
      | inl h => exact h.2.1
      | inr h => exact h.2.1
    | inr he =>
      rw [he]
      have hidx : a + 1 + 2 = a + 3 := by omega
      rw [hidx]
      cases hquad.2 with
      | inl h => omega
      | inr h => omega
  refine Exists.intro B (And.intro hB (And.intro hgap ?_))
  intro N
  let k := Classical.choose (hA.2.2 N)
  have hk : N <= k /\ Membership.mem A k := Classical.choose_spec (hA.2.2 N)
  exact Exists.intro k (And.intro hk.1
    (And.intro (Exists.intro k (And.intro hk.2 (Or.inl rfl)))
      (Exists.intro k (And.intro hk.2 (Or.inr rfl)))))

end PrimeFactorOscillations.PrimeProfileRigidity

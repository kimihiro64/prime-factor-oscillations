/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import BombieriVinogradov.Assembly.PrimeCountingConversion.Main
import PrimeGapsTheory.Endgame.Main

/-!
# Closed bounded-gap input

This restates an existing unconditional analytic input with all quantifiers
explicit. It is not a new bounded-gap theorem or a new QRH exponent.
-/

set_option autoImplicit false
set_option Elab.async false

theorem closed_prime_pairs_within_600 (N : Nat) :
    exists p q : Nat, N <= p /\ p < q /\ Nat.Prime p /\
      Nat.Prime q /\ q <= p + 600 :=
  bombieriVinogradov_implies_prime_gap_le_600
    BombieriVinogradov.PrimeCountingConversion.weighted_to_prime_counting N

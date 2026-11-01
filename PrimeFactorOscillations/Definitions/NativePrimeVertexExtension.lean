/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Definitions.NativePrimeVertexGreedy

/-! # The complete finite prime-vertex rejection families -/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.FiniteFieldIntegerSignature

/-- Clear every old/new lower collision and both new/new rows.
All subtractions are in the integers, so these are genuine fixed polynomials. -/
def nativePrimeVertexExtensionClear (P : Finset Nat) (q : Nat) : Prop :=
  And
    (forall p : Nat, Membership.mem P p ->
      forall n : Nat, Membership.mem P n ->
      forall m : Nat, Membership.mem P m -> n < m ->
        Not (IsSquare (((p * n * (m - n) : Nat) : Int) * ((q : Int) - (p : Int)))))
    (And
      (forall p : Nat, Membership.mem P p ->
        forall r : Nat, Membership.mem P r -> Not (p = r) ->
          Not (IsSquare (((p * r : Nat) : Int) * ((q : Int) - (p : Int)) *
            ((q : Int) - (r : Int)))))
      (forall p : Nat, Membership.mem P p ->
        forall r : Nat, Membership.mem P r -> Not (p = r) ->
          Not (IsSquare (((q : Int) - (p : Int)) * ((q : Int) - (r : Int))))))

end PrimeFactorOscillations.FiniteFieldIntegerSignature

/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Helpers.PeakPrimePrefixBounds

/-!
# Complete-prime-prefix coefficient specialization

This is the original coefficient criterion, specialized from the maintained
mixed-prefix theorem with no exceptional or missing coordinates.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations

theorem primePrefix_tilted_adjacent_flatness
    (n P H r : Nat) (hn : 2 <= n) (hP : 1 <= P) (hH : 2 <= H)
    (hPH : P <= H) (hHn : H <= n) (hr : 1 <= r)
    (a : Nat -> Real) (nu K E z delta : Real)
    (hnu : 0 <= nu) (hK : 0 <= K) (hz : 0 < z)
    (hd0 : 0 <= delta) (hd1 : delta < 1)
    (hpos : forall p, Nat.Prime p -> P < p -> p <= n -> 0 < a p)
    (hupper : forall p, Nat.Prime p -> P < p -> p <= n ->
      a p <= 2 * nu / (p : Real))
    (herror : forall p, Nat.Prime p -> P < p -> p <= n ->
      abs (a p - nu / (p : Real)) <= K / (p : Real) ^ 2)
    (hE : 2 * K / (P : Real) + nu *
      (abs (PrimeFactorUnimodality.reciprocalPrimeSumBelow (P + 1)) +
        (abs Mertens.M + abs PrimeFactorUnimodality.mertensErrorConstant /
          Real.log 2)) <= E)
    (hcenter : z * (nu * Real.log (Real.log (n : Real))) = (r : Real))
    (hbudget : z * (2 * E + 2 * nu * ((r - 1 : Nat) : Real) / (H : Real) +
      nu * Real.log (Real.log (H : Real))) <= delta * (r : Real))
    (hupperbudget : z * E <= delta * (r : Real)) :
    let S := (n + 1).primesBelow \ (P + 1).primesBelow
    let s := S.toList.map (fun p => z * a p / (1 + z * a p))
    r <= S.card /\ 0 < List.bernoulliMass s r /\
      abs (List.bernoulliMass s (r - 1) / List.bernoulliMass s r - 1) <=
        delta / (1 - delta) := by
  have hc := mixedPrimePrefix_tilted_adjacent_flatness n P H r hn hP hH hPH hHn hr
    ((n + 1).primesBelow \ (P + 1).primesBelow) (fun _ hp => hp)
    a [] nu K E z delta 0 0 0 hnu hK hz hd0 hd1 hpos hupper herror hE
    (by intro b hb; cases hb) (by simp) (by simp) (by simp [hcenter])
    (by simpa using hbudget) (by simpa using hupperbudget)
  dsimp only at hc
  simpa using And.intro hc.1 (And.intro hc.2.1 hc.2.2.1)

end PrimeFactorOscillations

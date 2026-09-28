import PrimeFactorUnimodality.Definitions.KthPrimeFactor

set_option autoImplicit false

/-!
# Quantitative reversal vocabulary

Ranks are one-based; prime indices are zero-based, as in the dependency.
These definitions do not assert either an asymptotic theorem or finiteness.
The ordinary density is reused directly from the Erdos 690 library.
-/

namespace PrimeFactorOscillations

variable {R : Type*} [Preorder R]

/-- A strict decrease followed later by a strict increase. -/
def IsReversal (f : Nat -> R) (descent ascent : Nat) : Prop :=
  descent < ascent /\ f (descent + 1) < f descent /\ f ascent < f (ascent + 1)

/-- An ordered family of witnesses whose closed index intervals are disjoint. -/
def HasAtLeastReversals (f : Nat -> R) (m : Nat) : Prop :=
  exists descent ascent : Fin m -> Nat,
    (forall j, IsReversal f (descent j) (ascent j)) /\
    (forall i j, i < j -> ascent i + 1 < descent j)

/-- The distribution of the number of selected entries under finite independent laws. -/
def finiteLocalMass (eta : Nat -> Rat) : List Nat -> Nat -> Rat
  | [], 0 => 1
  | [], _ + 1 => 0
  | p :: ps, 0 => (1 - eta p) * finiteLocalMass eta ps 0
  | p :: ps, r + 1 =>
      (1 - eta p) * finiteLocalMass eta ps (r + 1) + eta p * finiteLocalMass eta ps r

noncomputable section

/-- The local-law rank formula; its arithmetic interpretation requires independence. -/
def localRankDensity (eta : Nat -> Rat) (k i : Nat) : Rat :=
  eta (PrimeFactorUnimodality.primeAt i) *
    finiteLocalMass eta (PrimeFactorUnimodality.primesBelow
      (PrimeFactorUnimodality.primeAt i)) (k - 1)

/-- Ordinary integer density, without redefining the dependency's formula. -/
def ordinaryDensity (k : Nat) : Nat -> Rat :=
  PrimeFactorUnimodality.primeFactorDensity k

/-- Generic odd affine local law, used only at prime arguments. -/
def genericOddEta (p : Nat) : Rat :=
  if p = 2 then 0 else ((p : Rat) - 2) / ((p : Rat) - 1) ^ 2

/-- Limiting density formula for the generic odd affine family. -/
def genericOddDensity (k : Nat) : Nat -> Rat :=
  localRankDensity genericOddEta k

end

end PrimeFactorOscillations

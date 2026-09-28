import Mathlib.Analysis.SpecialFunctions.Exp
import PrimeFactorOscillations.Definitions.Reversals

set_option autoImplicit false

/-!
# Headline research targets

These are fully specified propositions, not assumed facts or proof holes.
The maximum is characterized by witnesses and an upper bound on every family,
so this statement cannot silently assign a finite count to infinite oscillation.
Input-size limits defining the two densities precede the growing-rank limit.
-/

namespace PrimeFactorOscillations

variable {R : Type*} [Preorder R]

/-- A certified finite maximum of separated strict reversal families. -/
def HasReversalNumber (f : Nat -> R) (N : Nat) : Prop :=
  HasAtLeastReversals f N /\ forall m, HasAtLeastReversals f m -> m <= N

/-- The two quantitative inequalities at one rank, including finite maximality. -/
def ReversalBoundsAt (f : Nat -> R) (k : Nat) (a epsilon : Real) : Prop :=
  exists N : Nat, HasReversalNumber f N /\
    Real.exp (Real.exp (a * (k : Real))) <= (N : Real) /\
    (N : Real) <= Real.exp (Real.exp (((1 : Real) / 3 + epsilon) * (k : Real)))

/-- Main open target with a common positive constant for both named families. -/
def DoubleExponentialReversalBounds : Prop :=
  exists a : Real, 0 < a /\
    forall epsilon : Real, 0 < epsilon ->
      exists K : Nat, 1 <= K /\ forall k : Nat, K <= k ->
        ReversalBoundsAt (ordinaryDensity k) k a epsilon /\
        ReversalBoundsAt (genericOddDensity k) k a epsilon

/-- Separate open target: remove the intermediate-rank gap in the odd family. -/
def GenericOddCompleteClassification : Prop :=
  forall k : Nat, 1 <= k ->
    (PrimeFactorUnimodality.IsUnimodal (genericOddDensity k) <-> k <= 3)

end PrimeFactorOscillations

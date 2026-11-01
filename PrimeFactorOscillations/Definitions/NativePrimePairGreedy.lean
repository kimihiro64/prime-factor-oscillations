/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Data.Finset.Basic
import Mathlib.Data.List.Range
import Mathlib.Data.Nat.Prime.Basic

/-!
# Computable persistent native prime-pair selection

Visit upper endpoints in increasing order and lower endpoints in their
natural order. Keep a genuine positive prime pair exactly when its two
positive square rows are unused. No choice or noncomputable definition
is used in the construction or the global membership decision.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.FiniteFieldIntegerSignature

/-- Both square rows separate the two labels. -/
def nativePrimePairSquareCompatible (a b : Prod Nat Nat) : Prop :=
  Not (IsSquare ((a.2 * a.1) * (b.2 * b.1))) /\
  Not (IsSquare ((a.2 * (a.1 + a.2)) * (b.2 * (b.1 + b.2))))

instance nativePrimePairSquareCompatibleDecidable (a b : Prod Nat Nat) :
    Decidable (nativePrimePairSquareCompatible a b) := by
  unfold nativePrimePairSquareCompatible
  infer_instance

/-- A single computable insertion at the specified upper endpoint. -/
def nativePrimePairGreedyInsert (q : Nat) (M : Finset (Prod Nat Nat)) (p : Nat) :
    Finset (Prod Nat Nat) :=
  if Nat.Prime p /\ Nat.Prime q /\ p < q /\
      (forall a : Prod Nat Nat, Membership.mem M a ->
        nativePrimePairSquareCompatible (p, q - p) a) then
    insert (p, q - p) M
  else M

/-- Process the ordered lower-endpoint list without removing prior labels. -/
def nativePrimePairGreedyScan (q : Nat) :
    List Nat -> Finset (Prod Nat Nat) -> Finset (Prod Nat Nat)
  | [], M => M
  | p :: ps, M => nativePrimePairGreedyScan q ps (nativePrimePairGreedyInsert q M p)

/-- The persistent finite selection at every natural height. -/
def nativePrimePairGreedyPrefix : Nat -> Finset (Prod Nat Nat)
  | 0 => {}
  | Y + 1 => nativePrimePairGreedyScan (Y + 1) (List.range (Y + 1))
      (nativePrimePairGreedyPrefix Y)

/-- Membership is decided by the finite computation at the label's birth
height. The prefix theorem proves that this is the same single family
at every later height. -/
def nativePrimePairGreedyClass : Set (Prod Nat Nat) :=
  fun a => Membership.mem (nativePrimePairGreedyPrefix (a.1 + a.2)) a

instance nativePrimePairGreedyClassDecidable : DecidablePred nativePrimePairGreedyClass :=
  fun a => inferInstanceAs (Decidable
    (Membership.mem (nativePrimePairGreedyPrefix (a.1 + a.2)) a))

end PrimeFactorOscillations.FiniteFieldIntegerSignature

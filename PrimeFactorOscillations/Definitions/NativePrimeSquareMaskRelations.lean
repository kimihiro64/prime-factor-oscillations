/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Definitions.NativePrimeSignedRows

/-! # Complete supported even-square row relations -/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.FiniteFieldIntegerSignature

def nativeUnsignedRowProduct (A B : Finset (Prod Nat Nat)) : Nat :=
  A.prod (fun e => e.1 * (e.2 - e.1)) * B.prod (fun e => e.2 * (e.2 - e.1))

noncomputable def nativeEvenSquareRowPairs (G : Finset (Prod Nat Nat)) :
    Finset (Prod (Finset (Prod Nat Nat)) (Finset (Prod Nat Nat))) := by
  classical
  exact (G.powerset.product G.powerset).filter (fun r =>
    And ((r.1.card + r.2.card) % 2 = 0) (IsSquare (nativeUnsignedRowProduct r.1 r.2)))

noncomputable def nativeEvenSquareRowCount (G : Finset (Prod Nat Nat)) : Nat :=
  (nativeEvenSquareRowPairs G).card

end PrimeFactorOscillations.FiniteFieldIntegerSignature

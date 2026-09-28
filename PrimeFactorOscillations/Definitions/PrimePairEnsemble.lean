import Mathlib.Basic.Real.Basic
import Mathlib.Data.Finset.Prod
import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.PrimeCounting

/-! # The complete ordered prime-pair ensemble at a finite input cutoff -/

set_option autoImplicit false

namespace PrimeFactorOscillations

open scoped Classical

def primePairs (N : Nat) : Finset (Prod Nat Nat) :=
  SProd.sprod (Nat.primesLE N) (Nat.primesLE N)

noncomputable def primePairResidueCount (N q : Nat) (R : Finset (Prod (ZMod q) (ZMod q))) : Nat :=
  ((primePairs N).filter (fun ab => Membership.mem R ((ab.1 : ZMod q), (ab.2 : ZMod q)))).card

noncomputable def primePairResidueProbability (N q : Nat)
    (R : Finset (Prod (ZMod q) (ZMod q))) : Real :=
  (primePairResidueCount N q R : Real) / (Nat.primeCounting N : Real) ^ 2

theorem primePairs_card (N : Nat) : (primePairs N).card = (Nat.primeCounting N) ^ 2 := by
  simp only [primePairs, Finset.card_product, Nat.primesLE_card_eq_primeCounting, pow_two]

noncomputable def primePairProbability (N : Nat) (P : Prod Nat Nat -> Prop) : Real :=
  (((primePairs N).filter P).card : Real) / (Nat.primeCounting N : Real) ^ 2

noncomputable def primePairResidueEventProbability (N q : Nat)
    (P : Prod (ZMod q) (ZMod q) -> Prop) : Real :=
  primePairProbability N (fun ab => P ((ab.1 : ZMod q), (ab.2 : ZMod q)))

end PrimeFactorOscillations

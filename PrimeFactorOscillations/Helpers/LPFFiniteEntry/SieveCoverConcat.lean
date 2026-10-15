/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.LPFFiniteEntry.SieveCoverCore

/-! Compose checked finite intervals without reducing the complete table again. -/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.LPF

theorem orbitTreeSieveIntervalCheck_append (tree : OrbitWitnessTree) (j start : Nat)
    (ds es : List Nat) :
    orbitTreeSieveIntervalCheck tree j start (ds ++ es) =
      (orbitTreeSieveIntervalCheck tree j start ds &&
        orbitTreeSieveIntervalCheck tree j (start + ds.length) es) := by
  induction ds generalizing start with
  | nil => simp [orbitTreeSieveIntervalCheck]
  | cons d ds ih =>
    rw [List.cons_append, orbitTreeSieveIntervalCheck, orbitTreeSieveIntervalCheck,
      ih, List.length_cons]
    have hIndex : (start + 1) + ds.length = start + (ds.length + 1) := by omega
    rw [hIndex]
    cases orbitTreeIntegerCover tree j start d <;> rfl

structure TreeSievePacket (tree : OrbitWitnessTree) (j start count : Nat) where
  divisors : List Nat
  length_eq : divisors.length = count
  checked : orbitTreeSieveIntervalCheck tree j start divisors = true

def TreeSievePacket.append {tree : OrbitWitnessTree} {j start left right : Nat}
    (a : TreeSievePacket tree j start left)
    (b : TreeSievePacket tree j (start + left) right) :
    TreeSievePacket tree j start (left + right) where
  divisors := a.divisors ++ b.divisors
  length_eq := by rw [List.length_append, a.length_eq, b.length_eq]
  checked := by
    rw [orbitTreeSieveIntervalCheck_append, a.length_eq, Bool.and_eq_true]
    exact And.intro a.checked b.checked

end PrimeFactorOscillations.LPF

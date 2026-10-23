/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.PrimeOrderReturnLaw

/-!
# Gated prime-order return patterns on the entire finite group

A closed gate forces nonreturn without constraining the underlying
coordinate. Every binary pattern is retained, including impossible
successes at closed gates. The exact product law uses the actual
image groups and their complete homomorphism fibers.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations.PrimeOrderReturnKernel

open FiniteHomProbability PrimeOrderReturnLaw

variable {G : Type*} [CommGroup G] [Fintype G]

local instance imageFintype (L l : Nat) : Fintype (returnImage (G := G) L l) :=
  PrimeOrderReturnLaw.imageFintype L l

def gatedCoordinateSet (L l : Nat) (gate bit : Bool) :
    Finset (returnImage (G := G) L l) := by
  classical
  exact if gate then coordinateSet L l bit else if bit then Finset.empty else Finset.univ

theorem gatedCoordinateSet_mem (L l : Nat) (gate bit : Bool)
    (x : returnImage (G := G) L l) :
    Membership.mem (gatedCoordinateSet L l gate bit) x <->
      if bit then And (gate = true) (x = 1) else Not (And (gate = true) (x = 1)) := by
  classical
  cases gate <;> cases bit <;> simp [gatedCoordinateSet, Finset.empty, coordinateSet_mem]

theorem gatedCoordinateSet_card (L l : Nat) (gate bit : Bool) :
    (gatedCoordinateSet (G := G) L l gate bit).card =
      if gate then if bit then 1 else returnIndex (G := G) L l - 1
      else if bit then 0 else returnIndex (G := G) L l := by
  classical
  cases gate <;> cases bit <;> simp [gatedCoordinateSet, Finset.empty, coordinateSet_card, returnIndex]

def gatedImagePatternSet (L : Nat) (S : Finset Nat.Primes) (gates bits : S -> Bool) :
    Finset ((p : S) -> returnImage (G := G) L (p.val : Nat)) := by
  classical
  exact Fintype.piFinset (fun p : S => gatedCoordinateSet L (p.val : Nat) (gates p) (bits p))

theorem gatedImagePatternSet_mem (L : Nat) (S : Finset Nat.Primes)
    (gates bits : S -> Bool) (y : (p : S) -> returnImage (G := G) L (p.val : Nat)) :
    Membership.mem (gatedImagePatternSet L S gates bits) y <->
      forall p : S, if bits p then And (gates p = true) (y p = 1)
      else Not (And (gates p = true) (y p = 1)) := by
  classical
  unfold gatedImagePatternSet
  rw [Fintype.mem_piFinset]
  apply forall_congr'
  intro p
  exact gatedCoordinateSet_mem L (p.val : Nat) (gates p) (bits p) (y p)

theorem gatedImagePatternSet_card (L : Nat) (S : Finset Nat.Primes) (gates bits : S -> Bool) :
    (gatedImagePatternSet (G := G) L S gates bits).card =
      Finset.univ.prod (fun p : S =>
        if gates p then if bits p then 1 else returnIndex (G := G) L (p.val : Nat) - 1
        else if bits p then 0 else returnIndex (G := G) L (p.val : Nat)) := by
  classical
  unfold gatedImagePatternSet
  rw [Fintype.card_piFinset]
  apply Finset.prod_congr rfl
  intro p _
  exact gatedCoordinateSet_card L (p.val : Nat) (gates p) (bits p)

def gatedPatternProbability (L : Nat) (S : Finset Nat.Primes) (gates bits : S -> Bool) : Real :=
  uniformProbability (fun g : G => forall p : S,
    if bits p then And (gates p = true) (g ^ (L / (p.val : Nat)) = 1)
    else Not (And (gates p = true) (g ^ (L / (p.val : Nat)) = 1)))

theorem gatedPatternProbability_eq_product (L : Nat) (S : Finset Nat.Primes)
    (hDiv : forall p : S, Dvd.dvd (p.val : Nat) L)
    (hAnn : forall g : G, g ^ L = 1) (gates bits : S -> Bool) :
    gatedPatternProbability (G := G) L S gates bits =
      Finset.univ.prod (fun p : S =>
        if gates p then
          if bits p then 1 / (returnIndex (G := G) L (p.val : Nat) : Real)
          else 1 - 1 / (returnIndex (G := G) L (p.val : Nat) : Real)
        else if bits p then 0 else 1) := by
  classical
  let H := (p : S) -> returnImage (G := G) L (p.val : Nat)
  let T : Finset H := gatedImagePatternSet L S gates bits
  have hPred :
      (fun g : G => forall p : S,
        if bits p then And (gates p = true) (g ^ (L / (p.val : Nat)) = 1)
        else Not (And (gates p = true) (g ^ (L / (p.val : Nat)) = 1))) =
      (fun g : G => Membership.mem T (packetProjection L S g)) := by
    funext g
    apply propext
    rw [gatedImagePatternSet_mem]
    apply forall_congr'
    intro p
    have heq : (packetProjection L S g) p = 1 <->
        g ^ (L / (p.val : Nat)) = 1 := by
      constructor
      { intro h
        exact congrArg Subtype.val h }
      { intro h
        apply Subtype.ext
        exact h }
    cases bits p
    { exact not_congr (and_congr Iff.rfl heq.symm) }
    { exact and_congr Iff.rfl heq.symm }
  unfold gatedPatternProbability
  rw [hPred, uniformProbability_preimage _ (packetProjection_surjective L S hDiv hAnn)]
  unfold uniformProbability
  change (Nat.card T : Real) / (Nat.card H : Real) = _
  rw [Nat.card_eq_fintype_card, Fintype.card_coe]
  rw [Nat.card_eq_fintype_card, Fintype.card_pi]
  rw [gatedImagePatternSet_card]
  simp only [Nat.cast_prod]
  rw [<- Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro p _
  have hPos : 0 < returnIndex (G := G) L (p.val : Nat) :=
    Fintype.card_pos_iff.mpr (Nonempty.intro 1)
  have hNonzero : Not ((returnIndex (G := G) L (p.val : Nat) : Real) = 0) := by
    exact_mod_cast (Nat.ne_of_gt hPos)
  cases gates p
  { cases bits p
    { exact div_self hNonzero }
    { simp } }
  { cases bits p
    { change (((returnIndex (G := G) L (p.val : Nat) - 1 : Nat) : Real) /
        (returnIndex (G := G) L (p.val : Nat) : Real)) =
        1 - 1 / (returnIndex (G := G) L (p.val : Nat) : Real)
      rw [Nat.cast_sub (by omega), Nat.cast_one, sub_div, div_self hNonzero] }
    { change ((1 : Nat) : Real) / (returnIndex (G := G) L (p.val : Nat) : Real) =
        1 / (returnIndex (G := G) L (p.val : Nat) : Real)
      rw [Nat.cast_one] } }

end PrimeFactorOscillations.PrimeOrderReturnKernel

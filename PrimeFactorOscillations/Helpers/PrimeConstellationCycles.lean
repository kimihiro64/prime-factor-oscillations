/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.GroupTheory.Perm.ViaEmbedding
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import PrimeFactorOscillations.Mathlib.Combinatorics.AdjacentSwapPrefix

/-!
# Disjoint prime cycles of any fixed finite offset shape

Recurring translated prime patterns supply separated copies of their entire
shape. Rotating each copy gives a global prime permutation with displacement
bounded by the shape diameter. The cycle labels recover every prime offset.
No consecutive-prime or prime-tuple conjecture is assumed in the decoding.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations

/-- Recurrence of an explicitly indexed finite translated prime pattern. -/
def RecurrentPrimeShape {k : Nat} (h : Fin k -> Nat) : Prop :=
  forall N : Nat, exists q : Nat, N <= q /\ forall i : Fin k, Nat.Prime (q + h i)

/-- A prime permutation realizes the full labelled rotation of the shape at q. -/
def PrimeShapeCycleAt {k : Nat} (h : Fin k -> Nat)
    (sigma : Equiv.Perm Nat.Primes) (q : Nat) : Prop :=
  exists a : Fin k -> Nat.Primes,
    (forall i, (a i : Nat) = q + h i) /\
    (forall i, sigma (a i) = a (finRotate k i))

/-- The full cycle word, rather than only its diameter, recovers the prime pattern. -/
theorem PrimeShapeCycleAt.prime_offsets {k : Nat} {h : Fin k -> Nat}
    {sigma : Equiv.Perm Nat.Primes} {q : Nat} (hc : PrimeShapeCycleAt h sigma q) :
    forall i : Fin k, Nat.Prime (q + h i) := by
  let a := hc.choose
  have ha := hc.choose_spec
  intro i
  rw [<- ha.1 i]
  exact (a i).property

/-- Infinitely recurring shapes admit one global bounded permutation realizing disjoint cycles. -/
theorem RecurrentPrimeShape.exists_bounded_cycle_permutation
    {k : Nat} (h : Fin k -> Nat) (hinj : Function.Injective h)
    (W : Nat) (hW : forall i, h i <= W) (hrec : RecurrentPrimeShape h) :
    exists sigma : Equiv.Perm Nat.Primes,
      (forall p : Nat.Primes,
        abs (((sigma p : Nat) : Real) - ((p : Nat) : Real)) <= (W : Real)) /\
      (forall N : Nat, exists q : Nat, N <= q /\ PrimeShapeCycleAt h sigma q) := by
  classical
  let S : Set Nat := fun q => forall i : Fin k, Nat.Prime (q + h i)
  choose A hA hsep hUnbounded using
    Set.exists_unbounded_separated_subset S hrec (W + 1) (by omega)
  let point : A -> Fin k -> Nat.Primes := fun a i =>
    Subtype.mk ((a : Nat) + h i) (hA (a : Nat) a.property i)
  have hpoint : Function.Injective (fun ai : Prod A (Fin k) => point ai.1 ai.2) := by
    intro ai bj heq
    have hv : (ai.1 : Nat) + h ai.2 = (bj.1 : Nat) + h bj.2 :=
      congrArg (fun p : Nat.Primes => (p : Nat)) heq
    have hfirst : (ai.1 : Nat) = (bj.1 : Nat) := by
      have hi := hW ai.2
      have hj := hW bj.2
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlo | hhi
      . have hs := hsep (ai.1 : Nat) ai.1.property (bj.1 : Nat) bj.1.property hlo
        omega
      . have hs := hsep (bj.1 : Nat) bj.1.property (ai.1 : Nat) ai.1.property hhi
        omega
    have hsecond : h ai.2 = h bj.2 := by omega
    exact Prod.ext (Subtype.ext hfirst) (hinj hsecond)
  let embed : Function.Embedding (Prod A (Fin k)) Nat.Primes :=
    Function.Embedding.mk (fun ai => point ai.1 ai.2) hpoint
  let rotate : Equiv.Perm (Prod A (Fin k)) :=
    Equiv.prodCongr (Equiv.refl A) (finRotate k)
  let sigma := rotate.viaEmbedding embed
  have hAction (a : A) (i : Fin k) :
      sigma (point a i) = point a (finRotate k i) := by
    exact rotate.viaEmbedding_apply embed (a, i)
  have hdispl : forall p : Nat.Primes,
      abs (((sigma p : Nat) : Real) - ((p : Nat) : Real)) <= (W : Real) := by
    intro p
    by_cases hp : Membership.mem (Set.range embed) p
    . let ai := hp.choose
      have hai := hp.choose_spec
      rw [<- hai, rotate.viaEmbedding_apply]
      change abs (((((ai.1 : Nat) + h (finRotate k ai.2)) : Nat) : Real) -
        ((((ai.1 : Nat) + h ai.2) : Nat) : Real)) <= (W : Real)
      have hi : ((h ai.2 : Nat) : Real) <= (W : Real) := by exact_mod_cast hW ai.2
      have hj : ((h (finRotate k ai.2) : Nat) : Real) <= (W : Real) := by
        exact_mod_cast hW (finRotate k ai.2)
      have hi0 : (0 : Real) <= (h ai.2 : Nat) := by positivity
      have hj0 : (0 : Real) <= (h (finRotate k ai.2) : Nat) := by positivity
      push_cast
      exact abs_le.mpr (And.intro (by linarith) (by linarith))
    . rw [rotate.viaEmbedding_apply_of_notMem embed p hp, sub_self, abs_zero]
      positivity
  refine Exists.intro sigma (And.intro hdispl ?_)
  intro N
  choose q hq hqA using hUnbounded N
  let a : A := Subtype.mk q hqA
  refine Exists.intro q (And.intro hq (Exists.intro (point a) (And.intro ?_ ?_)))
  . intro i
    rfl
  . exact hAction a

/-- Recurrence is equivalent to existence of a bounded full-shape cycle transport. -/
theorem recurrentPrimeShape_iff_bounded_cycle_permutation
    {k : Nat} (h : Fin k -> Nat) (hinj : Function.Injective h)
    (W : Nat) (hW : forall i, h i <= W) :
    RecurrentPrimeShape h <->
      exists sigma : Equiv.Perm Nat.Primes,
        (forall p : Nat.Primes,
          abs (((sigma p : Nat) : Real) - ((p : Nat) : Real)) <= (W : Real)) /\
        (forall N : Nat, exists q : Nat, N <= q /\ PrimeShapeCycleAt h sigma q) := by
  constructor
  . exact RecurrentPrimeShape.exists_bounded_cycle_permutation h hinj W hW
  . intro hex N
    let sigma := hex.choose
    have hs := hex.choose_spec
    choose q hq hc using hs.2 N
    exact Exists.intro q (And.intro hq hc.prime_offsets)

end PrimeFactorOscillations

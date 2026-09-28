import Mathlib.Data.Fintype.Card
import PrimeFactorOscillations.Helpers.ReversalCount
import PrimeFactorUnimodality.Helpers.PrimeSequence.Basic

/-! # Finite prime-gap counts bound every separated reversal family -/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations

variable {R : Type*} [Preorder R]

open PrimeFactorUnimodality

/-- Charge each ascent to either an initial prime range or an actual short gap.
The right-hand side counts prime indices, so repeated witnesses are excluded
before any asymptotic estimate is applied. -/
theorem reversal_count_le_short_gap_count (f : Nat -> R) (H T X m : Nat)
    (hcover : forall i : Nat, f i < f (i + 1) ->
      primeAt i <= T \/ (primeAt i <= X /\ primeGap i <= H))
    (hm : HasAtLeastReversals f m) :
    m <= T + ((Finset.range X).filter
      (fun i => primeAt i <= X /\ primeGap i <= H)).card := by
  classical
  let G : Finset Nat := (Finset.range X).filter
    (fun i => primeAt i <= X /\ primeGap i <= H)
  choose descent ascent h using hm
  have hmono : StrictMono ascent := by
    intro i j hij
    exact lt_trans (Nat.lt_succ_self _) (lt_trans (h.2 i j hij) (h.1 j).1)
  have hmem : forall j,
      Membership.mem (Union.union (Finset.range T) G) (ascent j) := by
    intro j
    have hbase : ascent j + 2 <= primeAt (ascent j) :=
      Nat.add_two_le_nth_prime (ascent j)
    have hc := hcover (ascent j) (h.1 j).2.2
    rcases hc with hearly | hgap
    next =>
      exact Finset.mem_union_left G (Finset.mem_range.mpr (by omega))
    next =>
      apply Finset.mem_union_right
      exact Finset.mem_filter.mpr (And.intro (Finset.mem_range.mpr (by omega)) hgap)
  let into : Fin m -> {i : Nat // Membership.mem (Union.union (Finset.range T) G) i} :=
    fun j => Subtype.mk (ascent j) (hmem j)
  have hinj : Function.Injective into := by
    intro i j heq
    exact hmono.injective (congrArg Subtype.val heq)
  have hc : m <= (Union.union (Finset.range T) G).card := by
    simpa only [Fintype.card_fin, Fintype.card_coe] using
      Fintype.card_le_of_injective into hinj
  have hu := Finset.card_union_le (Finset.range T) G
  rw [Finset.card_range] at hu
  exact hc.trans hu

end PrimeFactorOscillations

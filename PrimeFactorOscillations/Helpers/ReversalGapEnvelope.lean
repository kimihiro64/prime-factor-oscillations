import Mathlib.Data.Fintype.Card
import PrimeFactorOscillations.Helpers.ReversalCount
import PrimeFactorUnimodality.Helpers.PrimeSequence.Basic

/-! # Count reversals separately at each actual gap scale -/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations

variable {R : Type*} [Preorder R]

open PrimeFactorUnimodality

/-- A finite gap-by-gap envelope preserves each gap's individual cutoff.
The sum may overcount prime gaps, but never undercounts distinct ascents. -/
theorem reversal_count_le_gap_envelope (f : Nat -> R) (T J m : Nat)
    (U : Nat -> Nat)
    (hcover : forall i : Nat, f i < f (i + 1) ->
      primeAt i <= T \/ exists g : Nat, g <= J /\
        primeAt i <= U g /\ primeGap i <= g)
    (hm : HasAtLeastReversals f m) :
    m <= T + Finset.sum (Finset.range (J + 1))
      (fun g => ((Finset.range (U g)).filter
        (fun i => primeAt i <= U g /\ primeGap i <= g)).card) := by
  classical
  let G : Nat -> Finset Nat := fun g => (Finset.range (U g)).filter
    (fun i => primeAt i <= U g /\ primeGap i <= g)
  let S : Finset Nat := (Finset.range (J + 1)).biUnion G
  choose descent ascent h using hm
  have hmono : StrictMono ascent := by
    intro i j hij
    exact lt_trans (Nat.lt_succ_self _) (lt_trans (h.2 i j hij) (h.1 j).1)
  have hmem : forall j,
      Membership.mem (Union.union (Finset.range T) S) (ascent j) := by
    intro j
    have hbase : ascent j + 2 <= primeAt (ascent j) :=
      Nat.add_two_le_nth_prime (ascent j)
    rcases hcover (ascent j) (h.1 j).2.2 with hearly | hlate
    next =>
      exact Finset.mem_union_left S (Finset.mem_range.mpr (by omega))
    next =>
      choose g hg using hlate
      apply Finset.mem_union_right
      apply Finset.mem_biUnion.mpr
      refine Exists.intro g (And.intro (Finset.mem_range.mpr (by omega)) ?_)
      exact Finset.mem_filter.mpr
        (And.intro (Finset.mem_range.mpr (by omega)) hg.2)
  let into : Fin m -> {i : Nat // Membership.mem (Union.union (Finset.range T) S) i} :=
    fun j => Subtype.mk (ascent j) (hmem j)
  have hinj : Function.Injective into := by
    intro i j heq
    exact hmono.injective (congrArg Subtype.val heq)
  have hc : m <= (Union.union (Finset.range T) S).card := by
    simpa only [Fintype.card_fin, Fintype.card_coe] using
      Fintype.card_le_of_injective into hinj
  have hu := Finset.card_union_le (Finset.range T) S
  rw [Finset.card_range] at hu
  have hb : S.card <= Finset.sum (Finset.range (J + 1)) (fun g => (G g).card) :=
    Finset.card_biUnion_le
  exact hc.trans (hu.trans (Nat.add_le_add_left hb T))

end PrimeFactorOscillations

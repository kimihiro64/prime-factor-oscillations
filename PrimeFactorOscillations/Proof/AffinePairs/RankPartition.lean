import Mathlib.Algebra.BigOperators.Ring.Finset
import PrimeFactorOscillations.Definitions.PrimePairEnsemble

/-! # Exact finite cardinality partitions of the ordered prime-pair sample -/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations

open scoped Classical

theorem prime_pair_probability_cardinality_partition
    {B : Type*} [DecidableEq B] (N : Nat) (S : Finset B)
    (g : Prod Nat Nat -> Finset B) (hg : forall ab : Prod Nat Nat, g ab <= S)
    (E : Prod Nat Nat -> Prop) (r : Nat) :
    (S.powersetCard r).sum (fun T =>
      primePairProbability N (fun ab => E ab /\ g ab = T)) =
    primePairProbability N (fun ab => E ab /\ (g ab).card = r) := by
  let A : Finset (Prod Nat Nat) := (primePairs N).filter E
  have hL (T : Finset B) : A.filter (fun ab => g ab = T) =
      (primePairs N).filter (fun ab => E ab /\ g ab = T) := by
    apply Finset.ext
    intro ab
    simp only [A, Finset.mem_filter, and_assoc]
  have hR : A.filter (fun ab => Membership.mem (S.powersetCard r) (g ab)) =
      (primePairs N).filter (fun ab => E ab /\ (g ab).card = r) := by
    apply Finset.ext
    intro ab
    simp only [A, Finset.mem_filter, Finset.mem_powersetCard]
    constructor
    case mp =>
      intro h
      exact And.intro h.1.1 (And.intro h.1.2 h.2.2)
    case mpr =>
      intro h
      exact And.intro (And.intro h.1 h.2.1) (And.intro (hg ab) h.2.2)
  have hcount : (S.powersetCard r).sum (fun T =>
      ((primePairs N).filter (fun ab => E ab /\ g ab = T)).card) =
      ((primePairs N).filter (fun ab => E ab /\ (g ab).card = r)).card := by
    calc
      _ = (S.powersetCard r).sum (fun T => (A.filter (fun ab => g ab = T)).card) := by
        apply Finset.sum_congr rfl
        intro T hT
        exact congrArg Finset.card (hL T).symm
      _ = (A.filter (fun ab => Membership.mem (S.powersetCard r) (g ab))).card :=
        Finset.sum_card_fiberwise_eq_card_filter A (S.powersetCard r) g
      _ = _ := congrArg Finset.card hR
  have normalize (s : Finset (Prod Nat Nat)) (P : Prod Nat Nat -> Prop) (d : DecidablePred P) :
      @Finset.filter (Prod Nat Nat) P d s =
        @Finset.filter (Prod Nat Nat) P (fun ab => Classical.propDecidable (P ab)) s :=
    @Finset.filter_congr_decidable (Prod Nat Nat) s P d
      (fun ab => Classical.propDecidable (P ab))
  have hreal := congrArg (fun n : Nat => (n : Real) / (Nat.primeCounting N : Real) ^ 2) hcount
  simpa only [primePairProbability, Nat.cast_sum, div_eq_mul_inv, Finset.sum_mul, normalize]
    using hreal

end PrimeFactorOscillations

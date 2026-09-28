import PrimeFactorOscillations.Helpers.AffineRankEvent
import PrimeFactorOscillations.Mathlib.Probability.Distributions.FiniteBernoulliPatterns
import PrimeFactorOscillations.Proof.AffinePairs.PrimePatterns
import PrimeFactorOscillations.Proof.AffinePairs.RankPartition

/-! # Fixed-rank distributions for actual affine prime-pair products -/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.AffineSumFamily
open scoped Classical

theorem tendsto_prime_designated_atom (F : AffineSumFamily) (S T : Finset Nat)
    (hS : forall l : Nat, Membership.mem S l -> Nat.Prime l)
    (hTS : T <= S) (p : Nat) (hp : Nat.Prime p)
    (hpS : Not (Membership.mem S p)) :
    Filter.Tendsto (fun N : Nat => primePairProbability N (fun ab =>
      Dvd.dvd (p : Int) (F.value ab.1 ab.2) /\
        S.filter (fun l : Nat => Dvd.dvd (l : Int) (F.value ab.1 ab.2)) = T)) Filter.atTop
      (nhds (F.localProbability p * S.prod (fun l =>
        if Membership.mem T l then F.localProbability l else 1 - F.localProbability l))) := by
  have hU : forall l : Nat, Membership.mem (insert p S) l -> Nat.Prime l := by
    intro l hl
    apply Or.elim (Finset.mem_insert.mp hl)
    intro heq
    subst l
    exact hp
    intro hmem
    exact hS l hmem
  have hfilter (ab : Prod Nat Nat) :
      S.filter (fun l : Nat => Dvd.dvd (l : Int) (F.value ab.1 ab.2)) = T <->
        forall l : Nat, Membership.mem S l ->
          (Dvd.dvd (l : Int) (F.value ab.1 ab.2) <-> Membership.mem T l) := by
    constructor
    intro heq l hl
    rw [<- heq, Finset.mem_filter]
    simp only [hl, true_and]
    intro h
    apply Finset.ext
    intro l
    constructor
    intro hl
    exact (h l (Finset.mem_filter.mp hl).1).mp (Finset.mem_filter.mp hl).2
    intro hl
    exact Finset.mem_filter.mpr (And.intro (hTS hl) ((h l (hTS hl)).mpr hl))
  have hne (l : Nat) (hl : Membership.mem S l) : Not (l = p) := by
    intro heq
    apply hpS
    simpa only [heq] using hl
  have hevent (ab : Prod Nat Nat) :
      (forall l : Nat, Membership.mem (insert p S) l ->
        (Dvd.dvd (l : Int) (F.value ab.1 ab.2) <-> Membership.mem (insert p T) l)) <->
      (Dvd.dvd (p : Int) (F.value ab.1 ab.2) /\
        S.filter (fun l : Nat => Dvd.dvd (l : Int) (F.value ab.1 ab.2)) = T) := by
    constructor
    intro h
    refine And.intro ((h p (Finset.mem_insert_self p S)).mpr (Finset.mem_insert_self p T)) ?_
    apply (hfilter ab).mpr
    intro l hl
    simpa only [Finset.mem_insert, hne l hl, false_or] using
      h l (Finset.mem_insert_of_mem hl)
    intro h l hl
    apply Or.elim (Finset.mem_insert.mp hl)
    intro heq
    subst l
    simp only [h.1, Finset.mem_insert_self, iff_self]
    intro hmem
    simpa only [Finset.mem_insert, hne l hmem, false_or] using (hfilter ab).mp h.2 l hmem
  have hprod :
      (insert p S).prod (fun l =>
        if Membership.mem (insert p T) l then F.localProbability l
        else 1 - F.localProbability l) =
      F.localProbability p * S.prod (fun l =>
        if Membership.mem T l then F.localProbability l else 1 - F.localProbability l) := by
    rw [Finset.prod_insert hpS]
    simp only [Finset.mem_insert_self, ite_true]
    congr 1
    apply Finset.prod_congr rfl
    intro l hl
    simp only [Finset.mem_insert, hne l hl, false_or]
  have h := F.tendsto_prime_set_pattern (insert p S) (insert p T) hU
  simpa only [hevent, hprod] using h

theorem tendsto_prime_rank_count (F : AffineSumFamily) (S : Finset Nat)
    (hS : forall l : Nat, Membership.mem S l -> Nat.Prime l)
    (p : Nat) (hp : Nat.Prime p) (hpS : Not (Membership.mem S p)) (r : Nat) :
    Filter.Tendsto (fun N : Nat => primePairProbability N (fun ab =>
      Dvd.dvd (p : Int) (F.value ab.1 ab.2) /\
        (S.filter (fun l : Nat => Dvd.dvd (l : Int) (F.value ab.1 ab.2))).card = r))
      Filter.atTop
      (nhds (F.localProbability p *
        List.bernoulliMass (S.toList.map F.localProbability) r)) := by
  have hlim := tendsto_finsetSum (S.powersetCard r) (fun T hT =>
    F.tendsto_prime_designated_atom S T hS (Finset.mem_powersetCard.mp hT).1 p hp hpS)
  have hprob (N : Nat) :
      (S.powersetCard r).sum (fun T =>
        primePairProbability N (fun ab => Dvd.dvd (p : Int) (F.value ab.1 ab.2) /\
          S.filter (fun l : Nat => Dvd.dvd (l : Int) (F.value ab.1 ab.2)) = T)) =
      primePairProbability N (fun ab => Dvd.dvd (p : Int) (F.value ab.1 ab.2) /\
        (S.filter (fun l : Nat => Dvd.dvd (l : Int) (F.value ab.1 ab.2))).card = r) :=
    prime_pair_probability_cardinality_partition N S
      (fun ab => S.filter (fun l : Nat => Dvd.dvd (l : Int) (F.value ab.1 ab.2)))
      (fun ab => Finset.filter_subset _ _) (fun ab => Dvd.dvd (p : Int) (F.value ab.1 ab.2)) r
  have hscalar :
      (S.powersetCard r).sum (fun T => F.localProbability p * S.prod (fun l =>
        if Membership.mem T l then F.localProbability l else 1 - F.localProbability l)) =
      F.localProbability p * List.bernoulliMass (S.toList.map F.localProbability) r := by
    rw [Finset.bernoulliMass_eq_pattern_sum, Finset.mul_sum]
  simpa only [hprob, hscalar] using hlim


end PrimeFactorOscillations.AffineSumFamily

import PrimeFactorOscillations.Helpers.AffineReciprocalSmooth
import PrimeFactorOscillations.Helpers.AffineZeroSupport
import PrimeFactorOscillations.Proof.AffinePairs.FiniteErrors
import PrimeFactorOscillations.Proof.AffinePairs.RankDistribution

/-! # Arithmetic densities of kth distinct prime factors in affine prime-pair products -/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.AffineSumFamily
open scoped Classical

/-- Input size tends to infinity with the family, rank and prime fixed.
For positive ranks this is the literal distinct-prime-factor density. -/
theorem tendsto_kth_distinct_prime_factor (F : AffineSumFamily) (k p : Nat)
    (hp : Nat.Prime p) :
    Filter.Tendsto (fun N : Nat => primePairProbability N (fun ab =>
      PrimeFactorUnimodality.IsKthDistinctPrimeFactor (F.value ab.1 ab.2).natAbs k p))
      Filter.atTop (nhds (F.reciprocalSmoothLaw.rankDensityAt k p)) := by
  let S : Finset Nat := (Finset.range p).filter Nat.Prime
  have hS : forall l : Nat, Membership.mem S l -> Nat.Prime l :=
    fun l hl => (Finset.mem_filter.mp hl).2
  have hpS : Not (Membership.mem S p) := by
    intro h
    exact Nat.lt_irrefl p (Finset.mem_range.mp (Finset.mem_filter.mp h).1)
  let E : Prod Nat Nat -> Prop := fun ab =>
    Dvd.dvd (p : Int) (F.value ab.1 ab.2) /\
      (S.filter (fun l : Nat => Dvd.dvd (l : Int) (F.value ab.1 ab.2))).card = k - 1
  have hlim := F.tendsto_prime_rank_count S hS p hp hpS (k - 1)
  have hscalar : F.localProbability p *
      List.bernoulliMass (S.toList.map F.localProbability) (k - 1) =
      F.reciprocalSmoothLaw.rankDensityAt k p := rfl
  rw [hscalar] at hlim
  let M : Nat := Finset.univ.sum (fun i : Fin F.arity => (F.shift i).natAbs)
  let S0 : Finset (Prod Nat Nat) :=
    SProd.sprod (Finset.range (M + 1)) (Finset.range (M + 1))
  have hzero : forall ab : Prod Nat Nat, F.value ab.1 ab.2 = 0 -> Membership.mem S0 ab := by
    intro ab hz
    have hbound := F.zero_value_sum_bound ab.1 ab.2 hz
    change ab.1 + ab.2 <= M at hbound
    apply Finset.mem_product.mpr
    exact And.intro (Finset.mem_range.mpr (by omega)) (Finset.mem_range.mpr (by omega))
  have hclean := tendsto_prime_pair_remove_finite E (fun ab => F.value ab.1 ab.2 = 0)
    S0 hzero (F.reciprocalSmoothLaw.rankDensityAt k p) hlim
  have hevent (ab : Prod Nat Nat) :
      (E ab /\ Not (F.value ab.1 ab.2 = 0)) <->
      PrimeFactorUnimodality.IsKthDistinctPrimeFactor (F.value ab.1 ab.2).natAbs k p := by
    constructor
    intro h
    exact (F.isKthDistinctPrimeFactor_iff ab.1 ab.2 k p hp h.2).mpr h.1
    intro h
    have hz : Not (F.value ab.1 ab.2 = 0) := by
      intro heq
      have hn := h.2.2.1
      apply hn
      simp only [heq, Int.natAbs_zero]
    exact And.intro ((F.isKthDistinctPrimeFactor_iff ab.1 ab.2 k p hp hz).mp h) hz
  simpa only [hevent] using hclean

end PrimeFactorOscillations.AffineSumFamily

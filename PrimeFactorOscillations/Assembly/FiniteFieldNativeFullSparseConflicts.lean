/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.FiniteFieldNativeCrossOutputs
import PrimeFactorOscillations.Assembly.FiniteFieldNativeSparseConflicts

/-!
# Sparse collision deletion for unrestricted actual prime pairs

The finite cross-output class handles distinct lower endpoints without a
short-gap assumption. Both original root-row output classes remain present.
Every deleted anchor is counted in the actual finite prime-pair sample.
-/

set_option autoImplicit false
set_option Elab.async false

open Filter
open scoped Classical Topology

namespace PrimeFactorOscillations.FiniteFieldIntegerSignature

def nativeCrossEndpointPrimeOutput (J p q : Nat) : Prop :=
  exists a b : Nat, 0 < a /\ a < J /\ 0 < b /\ b < J /\ 1 < a * b /\
    exists r : Nat, Nat.Prime r /\ (a * b - 1) * p + q = a * r

theorem tendsto_native_cross_endpoint_output_probability_zero (J : Nat) :
    Filter.Tendsto (fun N : Nat => primePairProbability N
      (fun pq => nativeCrossEndpointPrimeOutput J pq.1 pq.2))
      Filter.atTop (nhds (0 : Real)) := by
  classical
  let I := Prod (Fin J) (Fin J)
  let Valid : I -> Prop := fun i =>
    0 < i.1.val /\ 0 < i.2.val /\ 1 < i.1.val * i.2.val
  let P : I -> Prod Nat Nat -> Prop := fun i pq =>
    Valid i /\ exists r : Nat, Nat.Prime r /\
      (i.1.val * i.2.val - 1) * pq.1 + pq.2 = i.1.val * r
  have hlocal (i : I) : Filter.Tendsto
      (fun N : Nat => primePairProbability N (P i)) Filter.atTop (nhds (0 : Real)) := by
    by_cases hv : Valid i
    . have hcoef : 0 < i.1.val * i.2.val - 1 := Nat.sub_pos_of_lt hv.2.2
      have h := tendsto_weighted_prime_output_probability_zero
        (i.1.val * i.2.val - 1) 1 i.1.val hcoef (by decide) hv.1
      simpa only [P, hv, true_and, one_mul] using h
    . have he : (fun N : Nat => primePairProbability N (P i)) = (fun _ : Nat => (0 : Real)) := by
        funext N
        simp only [P, hv, false_and, primePairProbability, Finset.filter_false,
          Finset.card_empty, Nat.cast_zero, zero_div]
      rw [he]
      exact tendsto_const_nhds
  have hcover (pq : Prod Nat Nat) (hout : nativeCrossEndpointPrimeOutput J pq.1 pq.2) :
      exists i : I, P i pq := by
    choose a b ha0 haJ hb0 hbJ hab r hr he using hout
    let fa : Fin J := Fin.mk a haJ
    let fb : Fin J := Fin.mk b hbJ
    exact Exists.intro (Prod.mk fa fb)
      (And.intro (And.intro ha0 (And.intro hb0 hab)) (Exists.intro r (And.intro hr he)))
  have hbound (N : Nat) : primePairProbability N
      (fun pq => nativeCrossEndpointPrimeOutput J pq.1 pq.2) <=
        Finset.univ.sum (fun i : I => primePairProbability N (P i)) := by
    let C : I -> Finset (Prod Nat Nat) := fun i => (primePairs N).filter (P i)
    have hs : (primePairs N).filter (fun pq => nativeCrossEndpointPrimeOutput J pq.1 pq.2) <=
        Finset.univ.biUnion C := by
      intro pq hpq
      have hh := Finset.mem_filter.mp hpq
      choose i hi using hcover pq hh.2
      exact Finset.mem_biUnion.mpr (Exists.intro i
        (And.intro (Finset.mem_univ i) (Finset.mem_filter.mpr (And.intro hh.1 hi))))
    have hc := (Finset.card_le_card hs).trans Finset.card_biUnion_le
    have hcast :
        (((primePairs N).filter (fun pq => nativeCrossEndpointPrimeOutput J pq.1 pq.2)).card : Real) <=
          Finset.univ.sum (fun i : I => ((C i).card : Real)) := by
      exact_mod_cast hc
    have he (i : I) :
        ((C i).card : Real) / (Nat.primeCounting N : Real) ^ 2 =
          primePairProbability N (P i) := by
      unfold primePairProbability
      apply congrArg (fun s : Finset (Prod Nat Nat) =>
        (s.card : Real) / (Nat.primeCounting N : Real) ^ 2)
      ext pq
      simp only [C, Finset.mem_filter]
    have hh := div_le_div_of_nonneg_right hcast (sq_nonneg (Nat.primeCounting N : Real))
    simp only [Finset.sum_div] at hh
    simp_rw [he] at hh
    exact hh
  have hsum : Filter.Tendsto
      (fun N : Nat => Finset.univ.sum (fun i : I => primePairProbability N (P i)))
      Filter.atTop (nhds (0 : Real)) := by
    have h := tendsto_finsetSum Finset.univ (fun i _ => hlocal i)
    simpa only [Finset.sum_const_zero] using h
  apply squeeze_zero ?_ hbound hsum
  intro N
  unfold primePairProbability
  exact div_nonneg (Nat.cast_nonneg _) (sq_nonneg _)

theorem native_unrestricted_clean_sparse_collision_packing
    (S : Finset (Prod Nat Nat)) (T J Y : Nat)
    (hprime : forall a : Prod Nat Nat, Membership.mem S a ->
      Nat.Prime a.1 /\ Nat.Prime (a.1 + a.2) /\ 0 < a.2 /\
        2 < a.1 /\ a.1 + a.2 <= Y /\ Y < J * a.1)
    (hclean : forall a : Prod Nat Nat, Membership.mem S a ->
      forall u : Nat, T <= u -> Not (Dvd.dvd (u ^ 2) a.2)) :
    exists M : Finset (Prod Nat Nat), M <= S /\
      S.card <= M.card +
        ((primePairs Y).filter (fun pq => nativeWeightedEndpointPrimeOutput T pq.1 pq.2)).card +
        ((primePairs Y).filter (fun pq => nativeCrossEndpointPrimeOutput J pq.1 pq.2)).card /\
      forall a : Prod Nat Nat, Membership.mem M a ->
        forall b : Prod Nat Nat, Membership.mem M b -> Not (a = b) ->
          nativeAgreementRate a.1 a.2 b.1 b.2 = 3 / 8 := by
  classical
  let Root := (primePairs Y).filter (fun pq => nativeWeightedEndpointPrimeOutput T pq.1 pq.2)
  let Cross := (primePairs Y).filter (fun pq => nativeCrossEndpointPrimeOutput J pq.1 pq.2)
  let M := S.filter (fun a =>
    Not (nativeWeightedEndpointPrimeOutput T a.1 (a.1 + a.2)) /\
    Not (nativeCrossEndpointPrimeOutput J a.1 (a.1 + a.2)))
  let Bad := S.filter (fun a =>
    nativeWeightedEndpointPrimeOutput T a.1 (a.1 + a.2) \/
    nativeCrossEndpointPrimeOutput J a.1 (a.1 + a.2))
  have hM : M <= S := Finset.filter_subset _ _
  have hcover : S <= Union.union M Bad := by
    intro a ha
    by_cases hr : nativeWeightedEndpointPrimeOutput T a.1 (a.1 + a.2)
    . exact Finset.mem_union.mpr (Or.inr
        (Finset.mem_filter.mpr (And.intro ha (Or.inl hr))))
    . by_cases hc : nativeCrossEndpointPrimeOutput J a.1 (a.1 + a.2)
      . exact Finset.mem_union.mpr (Or.inr
          (Finset.mem_filter.mpr (And.intro ha (Or.inr hc))))
      . exact Finset.mem_union.mpr (Or.inl
          (Finset.mem_filter.mpr (And.intro ha (And.intro hr hc))))
  have hBad : Bad.card <= Root.card + Cross.card := by
    have hUnion : Bad.card <= (Union.union Root Cross).card := by
      apply Finset.card_le_card_of_injOn (fun a : Prod Nat Nat => Prod.mk a.1 (a.1 + a.2))
      . intro a ha
        have haS := (Finset.mem_filter.mp ha).1
        have hp := hprime a haS
        have hInput : Membership.mem (primePairs Y) (Prod.mk a.1 (a.1 + a.2)) := by
          change Membership.mem ((Nat.primesLE Y).product (Nat.primesLE Y))
            (Prod.mk a.1 (a.1 + a.2))
          exact Finset.mem_product.mpr (And.intro
            (Nat.mem_primesLE.mpr (And.intro (by omega) hp.1))
            (Nat.mem_primesLE.mpr (And.intro hp.2.2.2.2.1 hp.2.1)))
        apply Finset.mem_union.mpr
        rcases (Finset.mem_filter.mp ha).2 with hr | hc
        . exact Or.inl (Finset.mem_filter.mpr (And.intro hInput hr))
        . exact Or.inr (Finset.mem_filter.mpr (And.intro hInput hc))
      . intro a ha b hb he
        have hp1 := congrArg (fun z : Prod Nat Nat => z.1) he
        have hp2 := congrArg (fun z : Prod Nat Nat => z.2) he
        have hn : a.1 = b.1 := hp1
        have hq : a.1 + a.2 = b.1 + b.2 := hp2
        exact Prod.ext hn (by omega)
    exact hUnion.trans (Finset.card_union_le Root Cross)
  refine Exists.intro M (And.intro hM (And.intro ?_ ?_))
  . change S.card <= M.card + Root.card + Cross.card
    have hh := (Finset.card_le_card hcover).trans (Finset.card_union_le M Bad)
    omega
  . apply native_clean_avoiding_weighted_outputs_flat_of_lower_recovery M T
    . intro a ha
      have hp := hprime a (hM ha)
      exact And.intro hp.1 (And.intro hp.2.1 hp.2.2.1)
    . intro a ha
      exact hclean a (hM ha)
    . intro a ha
      exact (Finset.mem_filter.mp ha).2.1
    . intro a ha b hb hs
      by_contra hne
      have haP := hprime a (hM ha)
      have hbP := hprime b (hM hb)
      have cert := native_lower_square_cross_bounded_positive_output
        a.1 a.2 b.1 b.2 J Y haP.1 haP.2.1 hbP.1 hbP.2.1
          haP.2.2.1 hbP.2.2.1 haP.2.2.2.1 hbP.2.2.2.1 hne hs
          haP.2.2.2.2.1 hbP.2.2.2.2.1 haP.2.2.2.2.2 hbP.2.2.2.2.2
      choose u v hu0 huJ hv0 hvJ huv heq using cert
      apply (Finset.mem_filter.mp ha).2.2
      exact Exists.intro u (Exists.intro v (And.intro hu0 (And.intro huJ
        (And.intro hv0 (And.intro hvJ (And.intro huv
          (Exists.intro (b.1 + b.2) (And.intro hbP.2.1 heq))))))))

end PrimeFactorOscillations.FiniteFieldIntegerSignature

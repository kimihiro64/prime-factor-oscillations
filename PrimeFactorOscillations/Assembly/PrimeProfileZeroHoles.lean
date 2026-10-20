/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Assembly.PrimeProfileCutoffInverse

/-!
# Zero coordinates cannot evade the adaptive cutoff inverse

Profile multiplicity recovery identifies all positive entries. A zero hole
leaves fewer entries in every later prefix. Common coordinates cancel;
the unequal-cardinality boundary estimate gives a divergent signed cost.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

open Filter
open scoped Topology

namespace PrimeFactorOscillations.PrimeProfileRigidity

private theorem primeLogWeight_nonpos (t : Real) (ht : 0 < t) (n : Nat) :
    primeLogWeight t n <= 0 := by
  have hp : (0 : Real) < PrimeFactorUnimodality.primeAt n := by
    exact_mod_cast (PrimeFactorUnimodality.prime_primeAt n).pos
  have h := Real.log_le_sub_one_of_pos
    (by positivity : 0 < 1 + t / (PrimeFactorUnimodality.primeAt n : Real))
  unfold primeLogWeight Real.bernoulliLogProfile
  linarith only [h]

private theorem exists_positive_prime_equiv (a : Nat -> Real)
    (ha : forall n, 0 <= a n) (ha1 : forall n, a n <= 1)
    (hsa : Summable (fun n => (a n) ^ 2))
    (heq : Complex.canonicalBernoulliProfile a =
      Complex.canonicalBernoulliProfile reciprocalPrimeProbability) :
    exists e : Equiv {n : Nat // 0 < a n} Nat,
      forall n, a n.val = reciprocalPrimeProbability (e n) := by
  let eb : Equiv Nat {n : Nat // 0 < reciprocalPrimeProbability n} :=
    { toFun := fun n => Subtype.mk n (reciprocalPrimeProbability_pos n)
      invFun := Subtype.val
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hh := Complex.exists_positive_equiv_of_canonicalBernoulliProfile_eq
    a reciprocalPrimeProbability ha ha1
    (fun n => (reciprocalPrimeProbability_pos n).le) reciprocalPrimeProbability_le_one
    hsa summable_reciprocalPrimeProbability_sq heq
  let ep := Classical.choose hh
  have hep : forall n : {n : Nat // 0 < a n},
      a n.val = reciprocalPrimeProbability (ep n).val := Classical.choose_spec hh
  exact Exists.intro (ep.trans eb.symm) hep

/-- Once a zero has entered a prefix, its adaptive normalized cost grows at
least like the last prime, independently of the positive probe. -/
theorem quarter_prime_le_normalized_defect_of_zero (a : Nat -> Real)
    (ha : forall n, 0 <= a n) (ha1 : forall n, a n <= 1)
    (hsa : Summable (fun n => (a n) ^ 2))
    (heq : Complex.canonicalBernoulliProfile a =
      Complex.canonicalBernoulliProfile reciprocalPrimeProbability)
    (t : Nat -> Real) (i n : Nat) (hz : a i = 0) (hin : i <= n)
    (ht : 0 < t n) :
    (PrimeFactorUnimodality.primeAt n : Real) / 4 <=
      normalizedProbabilityPrefixDefect a t n := by
  classical
  have hh := exists_positive_prime_equiv a ha ha1 hsa heq
  let e := Classical.choose hh
  have he : forall j : {j : Nat // 0 < a j},
      a j.val = reciprocalPrimeProbability (e j) := Classical.choose_spec hh
  let f : Nat -> Nat := fun j => if hj : 0 < a j then e (Subtype.mk j hj) else 0
  let P := (Finset.range (n + 1)).filter (fun j => 0 < a j)
  let S := P.image f
  have hf : Set.InjOn f (P : Set Nat) := by
    intro j hj k hk hjk
    have hjpos : 0 < a j := (Finset.mem_filter.mp hj).2
    have hkpos : 0 < a k := (Finset.mem_filter.mp hk).2
    have heqf : e (Subtype.mk j hjpos) = e (Subtype.mk k hkpos) := by
      simpa only [f, dite_eq_left hjpos, dite_eq_left hkpos] using hjk
    exact congrArg Subtype.val (e.injective heqf)
  have hcardS : S.card = P.card := Finset.card_image_iff.mpr hf
  have hsub : forall j, Membership.mem P j ->
      Membership.mem ((Finset.range (n + 1)).erase i) j := by
    intro j hj
    have hd := Finset.mem_filter.mp hj
    apply Finset.mem_erase.mpr
    refine And.intro ?_ hd.1
    intro hji
    have hpos := hd.2
    rw [hji, hz] at hpos
    exact lt_irrefl 0 hpos
  have hcard : S.card < (Finset.range (n + 1)).card := by
    have hc := Finset.card_le_card hsub
    rw [Finset.card_erase_of_mem (Finset.mem_range.mpr (by omega : i < n + 1))] at hc
    rw [hcardS, Finset.card_range]
    rw [Finset.card_range] at hc
    omega
  have hsum : (Finset.range (n + 1)).sum
      (fun j => Real.log (1 + t n * a j) - t n * a j) =
      S.sum (primeLogWeight (t n)) := by
    rw [show S = P.image f from rfl, Finset.sum_image hf]
    change _ = ((Finset.range (n + 1)).filter (fun j => 0 < a j)).sum _
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro j hj
    by_cases hpos : 0 < a j
    . rw [ite_eq_left hpos]
      have hv := he (Subtype.mk j hpos)
      change a j = reciprocalPrimeProbability (e (Subtype.mk j hpos)) at hv
      simp only [f, dite_eq_left hpos]
      rw [hv]
      simp only [primeLogWeight, Real.bernoulliLogProfile, reciprocalPrimeProbability,
        mul_one_div]
    . have hzero : a j = 0 := le_antisymm (le_of_not_gt hpos) (ha j)
      rw [ite_eq_right hpos, hzero]
      simp only [mul_zero, add_zero, Real.log_one, sub_self]
  have hbound := Finset.neg_boundary_le_sum_sub_sum_of_card_lt
    S (Finset.range (n + 1)) (primeLogWeight (t n)) (primeLogWeight (t n) n)
    (primeLogWeight_nonpos _ ht _) hcard
    (fun j hj => (primeLogWeight_strictMono _ ht).monotone (by
      have hnot := (Finset.mem_sdiff.mp hj).2
      rw [Finset.mem_range] at hnot
      omega))
    (fun j hj => (primeLogWeight_strictMono _ ht).monotone (by
      have hmem := (Finset.mem_sdiff.mp hj).1
      rw [Finset.mem_range] at hmem
      omega))
  have hp : (0 : Real) < PrimeFactorUnimodality.primeAt n := by
    exact_mod_cast (PrimeFactorUnimodality.prime_primeAt n).pos
  have hnorm : 0 <= (PrimeFactorUnimodality.primeAt n : Real) ^ 2 *
      ((PrimeFactorUnimodality.primeAt n : Real) + t n) / (t n) ^ 2 := by positivity
  have hmul := mul_le_mul_of_nonneg_left hbound hnorm
  have hcost := Real.quarter_denominator_le_normalized_zero_cost (t n)
    (PrimeFactorUnimodality.primeAt n : Real) ht hp
  unfold normalizedProbabilityPrefixDefect
  rw [hsum]
  apply hcost.trans
  simpa only [primeLogWeight, Real.bernoulliLogProfile, neg_sub] using hmul

/-- The full adaptive inverse includes all zero-coordinate exceptions. -/
theorem profile_cutoff_inverse (a : Nat -> Real)
    (ha : forall n, 0 <= a n) (ha1 : forall n, a n <= 1)
    (hsa : Summable (fun n => (a n) ^ 2))
    (heq : Complex.canonicalBernoulliProfile a =
      Complex.canonicalBernoulliProfile reciprocalPrimeProbability)
    (t : Nat -> Real) (ht : forall n, 0 < t n) :
    Tendsto (normalizedProbabilityPrefixDefect a t) atTop (nhds 0) <->
      exists N : Nat, exists e : Equiv.Perm Nat,
        (forall n, N <= n -> e n = n) /\
          forall n, a n = reciprocalPrimeProbability (e n) := by
  constructor
  . intro h
    have hpos : forall i, 0 < a i := by
      intro i
      by_contra hn
      have hz : a i = 0 := le_antisymm (le_of_not_gt hn) (ha i)
      have hsmall := h.eventually (gt_mem_nhds (by norm_num : (0 : Real) < 1))
      have hfalse : Filter.Eventually (fun _ : Nat => False) atTop := by
        filter_upwards [hsmall, eventually_ge_atTop i, eventually_ge_atTop 8] with n hs hi hn
        have hb := quarter_prime_le_normalized_defect_of_zero
          a ha ha1 hsa heq t i n hz hi (ht n)
        have hNat : 8 <= PrimeFactorUnimodality.primeAt n :=
          hn.trans (PrimeFactorUnimodality.primeAt_strictMono.id_le n)
        have hp : (8 : Real) <= PrimeFactorUnimodality.primeAt n := by exact_mod_cast hNat
        linarith only [hb, hs, hp]
      exact hfalse.exists.elim (fun _ hf => hf)
    exact (positive_profile_cutoff_inverse a hpos ha1 hsa heq t ht).mp h
  . intro h
    let N := Classical.choose h
    let e := Classical.choose (Classical.choose_spec h)
    have hd : (forall n, N <= n -> e n = n) /\
        forall n, a n = reciprocalPrimeProbability (e n) :=
      Classical.choose_spec (Classical.choose_spec h)
    have hpos : forall n, 0 < a n := by
      intro n
      rw [hd.2 n]
      exact reciprocalPrimeProbability_pos _
    exact (positive_profile_cutoff_inverse a hpos ha1 hsa heq t ht).mpr h

end PrimeFactorOscillations.PrimeProfileRigidity

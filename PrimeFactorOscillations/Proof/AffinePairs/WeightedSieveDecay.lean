/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.GenericOddMertens
import PrimeFactorOscillations.Proof.AffinePairs.WeightedPrimePatterns

/-!
# Vanishing weighted sieve products beyond a fixed prime cutoff

The installed Mertens estimate supplies divergent ordinary prime odds.
Every sieve is finite; its cutoff tends to infinity only after the fixed
coefficient-exception cutoff has been chosen.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations

open Filter

noncomputable def weightedSievePrimes (B n : Nat) : Finset Nat := by
  classical
  exact ((Finset.range (n + 1)).filter Nat.Prime).filter (fun p => B < p)

noncomputable def weightedSieveProduct (B n : Nat) : Real :=
  (weightedSievePrimes B n).prod (fun p => 1 - 1 / ((p : Real) - 1))

noncomputable def weightedSieveWeightSum (B n : Nat) : Real :=
  (weightedSievePrimes B n).sum (fun p => 1 / ((p : Real) - 1))

private theorem ordinary_odds_sum_real (x : Nat) :
    (ordinaryPrimeWeightSum x : Real) =
      ((Finset.range x).filter Nat.Prime).sum (fun p => 1 / ((p : Real) - 1)) := by
  have hQ : ordinaryPrimeWeightSum x =
      ((Finset.range x).filter Nat.Prime).sum
        (fun p => (1 : Rat) / ((p : Rat) - 1)) := by
    unfold ordinaryPrimeWeightSum
    apply Finset.sum_congr rfl
    intro p hp
    exact ordinaryWeight_cast p (Finset.mem_filter.mp hp).2.one_lt.le
  exact_mod_cast hQ

private theorem tendsto_ordinary_odds_atTop :
    Tendsto (fun n : Nat => (ordinaryPrimeWeightSum (n + 1) : Real)) atTop atTop := by
  have hNat : Tendsto (fun n : Nat => (n : Real)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hLog : Tendsto (fun n : Nat => Real.log (n : Real)) atTop atTop := by
    simpa only [Function.comp_def] using Real.tendsto_log_atTop.comp hNat
  have hLogLog : Tendsto (fun n : Nat => Real.log (Real.log (n : Real)))
      atTop atTop := by
    simpa only [Function.comp_def] using Real.tendsto_log_atTop.comp hLog
  have hSmall : Tendsto (fun n : Nat =>
      PrimeFactorUnimodality.mertensErrorConstant / Real.log (n : Real))
      atTop (nhds (0 : Real)) := by
    simpa only [Function.comp_def, div_eq_mul_inv, mul_zero] using
      (tendsto_inv_atTop_zero.comp hLog).const_mul
        PrimeFactorUnimodality.mertensErrorConstant
  apply tendsto_atTop.mpr
  intro b
  filter_upwards [eventually_ge_atTop (2 : Nat),
    (tendsto_atTop.mp hLogLog) (b - Mertens.M + 3),
    hSmall.eventually (gt_mem_nhds (show (0 : Real) < 1 by norm_num))]
      with n hn hl hs
  have hm := (genericOdd_mertens_bounds n hn).1
  have hd : (genericOddPrimeWeightSum (n + 1) : Real) <=
      (ordinaryPrimeWeightSum (n + 1) : Real) := by
    have hQ := sub_nonneg.mp (genericOdd_weightSum_transfer (n + 1)).1
    exact_mod_cast hQ
  linarith only [hm, hd, hl, hs]

private theorem weighted_sieve_weight_sum_eq (B n : Nat) (hBn : B <= n) :
    weightedSieveWeightSum B n =
      (ordinaryPrimeWeightSum (n + 1) : Real) -
        (ordinaryPrimeWeightSum (B + 1) : Real) := by
  classical
  let S : Nat -> Finset Nat := fun x => (Finset.range (x + 1)).filter Nat.Prime
  have hsub : S B <= S n := by
    intro p hp
    have h := Finset.mem_filter.mp hp
    apply Finset.mem_filter.mpr
    refine And.intro ?_ h.2
    exact Finset.mem_range.mpr
      (Nat.lt_of_lt_of_le (Finset.mem_range.mp h.1) (Nat.add_le_add_right hBn 1))
  have hSet : weightedSievePrimes B n = SDiff.sdiff (S n) (S B) := by
    apply Finset.ext
    intro p
    simp only [weightedSievePrimes, S, Finset.mem_filter, Finset.mem_range,
      Finset.mem_sdiff]
    constructor
    . intro h
      refine And.intro h.1 ?_
      intro hp
      omega
    . intro h
      refine And.intro h.1 ?_
      by_contra hn
      exact h.2 (And.intro (by omega) h.1.2)
  have hsum :
      (SDiff.sdiff (S n) (S B)).sum (fun p => 1 / ((p : Real) - 1)) =
        (S n).sum (fun p => 1 / ((p : Real) - 1)) -
          (S B).sum (fun p => 1 / ((p : Real) - 1)) := by
    apply eq_sub_iff_add_eq.mpr
    exact Finset.sum_sdiff hsub
  unfold weightedSieveWeightSum
  rw [hSet, hsum]
  dsimp only [S]
  rw [ordinary_odds_sum_real (n + 1), ordinary_odds_sum_real (B + 1)]

private theorem tendsto_weighted_sieve_weight_sum (B : Nat) :
    Tendsto (weightedSieveWeightSum B) atTop atTop := by
  apply tendsto_atTop.mpr
  intro b
  filter_upwards [eventually_ge_atTop B,
    (tendsto_atTop.mp tendsto_ordinary_odds_atTop)
      (b + (ordinaryPrimeWeightSum (B + 1) : Real))] with n hn hs
  rw [weighted_sieve_weight_sum_eq B n hn]
  linarith only [hs]

private theorem weighted_sieve_factor_nonneg (B : Nat) (hB : 2 <= B)
    (n p : Nat) (hp : Membership.mem (weightedSievePrimes B n) p) :
    0 <= 1 - 1 / ((p : Real) - 1) := by
  have hpB := (Finset.mem_filter.mp hp).2
  have hpR : (2 : Real) < p := by exact_mod_cast (lt_of_le_of_lt hB hpB)
  apply sub_nonneg.mpr
  simpa only [div_one] using
    (div_le_div_of_nonneg_left (show (0 : Real) <= 1 by norm_num)
      (show (0 : Real) < 1 by norm_num) (show (1 : Real) <= (p : Real) - 1 by linarith))

private theorem weighted_sieve_product_exp_bound (B : Nat) (hB : 2 <= B) (n : Nat) :
    weightedSieveProduct B n <= Real.exp (-weightedSieveWeightSum B n) := by
  classical
  have hBound (s : Finset Nat) : s <= weightedSievePrimes B n ->
      s.prod (fun p => 1 - 1 / ((p : Real) - 1)) <=
        Real.exp (-s.sum (fun p => 1 / ((p : Real) - 1))) := by
    induction s using Finset.induction_on with
    | empty =>
      intro hs
      simp
    | @insert p s hp ih =>
      intro hs
      have hpS : Membership.mem (weightedSievePrimes B n) p :=
        hs (Finset.mem_insert_self p s)
      have hsS : s <= weightedSievePrimes B n :=
        fun q hq => hs (Finset.mem_insert_of_mem hq)
      have hf : 1 - 1 / ((p : Real) - 1) <=
          Real.exp (-(1 / ((p : Real) - 1))) := by
        have he := Real.add_one_le_exp (-(1 / ((p : Real) - 1)))
        linarith only [he]
      have hn : 0 <= s.prod (fun q => 1 - 1 / ((q : Real) - 1)) :=
        Finset.prod_nonneg (fun q hq =>
          weighted_sieve_factor_nonneg B hB n q (hsS hq))
      rw [Finset.prod_insert hp, Finset.sum_insert hp]
      calc
        (1 - 1 / ((p : Real) - 1)) *
            s.prod (fun q => 1 - 1 / ((q : Real) - 1)) <=
          Real.exp (-(1 / ((p : Real) - 1))) *
            Real.exp (-s.sum (fun q => 1 / ((q : Real) - 1))) :=
          mul_le_mul hf (ih hsS) hn (Real.exp_nonneg _)
        _ = Real.exp (-(1 / ((p : Real) - 1) +
            s.sum (fun q => 1 / ((q : Real) - 1)))) := by
          rw [neg_add, Real.exp_add]
  exact hBound (weightedSievePrimes B n) (fun p hp => hp)

/-- The exact finite weighted-sieve product tends to zero after any fixed
cutoff at least two. No selected prime varies inside the sampling limit. -/
theorem tendsto_weighted_sieve_product_zero (B : Nat) (hB : 2 <= B) :
    Tendsto (weightedSieveProduct B) atTop (nhds (0 : Real)) := by
  have hExp : Tendsto (fun n : Nat => Real.exp (-weightedSieveWeightSum B n))
      atTop (nhds (0 : Real)) :=
    Real.tendsto_exp_atBot.comp
      (tendsto_neg_atTop_atBot.comp (tendsto_weighted_sieve_weight_sum B))
  apply squeeze_zero ?_ ?_ hExp
  . intro n
    exact Finset.prod_nonneg (fun p hp => weighted_sieve_factor_nonneg B hB n p hp)
  . intro n
    exact weighted_sieve_product_exp_bound B hB n

private theorem prime_pair_probability_nonneg (N : Nat)
    (P : Prod Nat Nat -> Prop) : 0 <= primePairProbability N P := by
  unfold primePairProbability
  exact div_nonneg (Nat.cast_nonneg _) (sq_nonneg _)

private theorem prime_pair_probability_mono (N : Nat)
    (P Q : Prod Nat Nat -> Prop)
    (hPQ : forall pq : Prod Nat Nat, Membership.mem (primePairs N) pq -> P pq -> Q pq) :
    primePairProbability N P <= primePairProbability N Q := by
  classical
  unfold primePairProbability
  apply div_le_div_of_nonneg_right ?_ (sq_nonneg _)
  have hsub : (primePairs N).filter P <= (primePairs N).filter Q := by
    intro pq hpq
    have h := Finset.mem_filter.mp hpq
    exact Finset.mem_filter.mpr (And.intro h.1 (hPQ pq h.1 h.2))
  exact_mod_cast Finset.card_le_card hsub

private theorem prime_pair_probability_or_bound (N : Nat)
    (P Q R : Prod Nat Nat -> Prop)
    (hP : forall pq : Prod Nat Nat, Membership.mem (primePairs N) pq ->
      P pq -> Q pq \/ R pq) :
    primePairProbability N P <= primePairProbability N Q + primePairProbability N R := by
  classical
  have hsub : (primePairs N).filter P <=
      Union.union ((primePairs N).filter Q) ((primePairs N).filter R) := by
    intro pq hpq
    have h := Finset.mem_filter.mp hpq
    apply Finset.mem_union.mpr
    rcases hP pq h.1 h.2 with hQ | hR
    . exact Or.inl (Finset.mem_filter.mpr (And.intro h.1 hQ))
    . exact Or.inr (Finset.mem_filter.mpr (And.intro h.1 hR))
  have hc : ((primePairs N).filter P).card <=
      ((primePairs N).filter Q).card + ((primePairs N).filter R).card :=
    (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  unfold primePairProbability
  rw [<- add_div]
  apply div_le_div_of_nonneg_right ?_ (sq_nonneg _)
  exact_mod_cast hc

private theorem tendsto_prime_pair_small_first_probability_zero (B : Nat) :
    Tendsto (fun N : Nat => primePairProbability N (fun pq => pq.1 <= B))
      atTop (nhds (0 : Real)) := by
  classical
  let M : Nat := (Nat.primesLE B).prod (fun p => p)
  have hM : Not (M = 0) := by
    dsimp only [M]
    exact Finset.prod_ne_zero_iff.mpr (fun p hp =>
      (Nat.mem_primesLE.mp hp).2.ne_zero)
  let : NeZero M := NeZero.mk hM
  have hCard : Nat.card {xy : Prod (Units (ZMod M)) (Units (ZMod M)) //
      Not (IsUnit (xy.1 : ZMod M))} = 0 := by
    let : IsEmpty {xy : Prod (Units (ZMod M)) (Units (ZMod M)) //
        Not (IsUnit (xy.1 : ZMod M))} :=
      IsEmpty.mk (fun xy => xy.property xy.val.1.isUnit)
    simp
  have hLaw : Tendsto (fun N : Nat => primePairResidueEventProbability N M
      (fun xy => Not (IsUnit xy.1))) atTop (nhds (0 : Real)) := by
    have ht := tendsto_prime_pair_predicate_probability M (fun xy => Not (IsUnit xy.1))
    simpa only [hCard, Nat.cast_zero, zero_div] using ht
  have hDom (N : Nat) :
      primePairProbability N (fun pq => pq.1 <= B) <=
        primePairResidueEventProbability N M (fun xy => Not (IsUnit xy.1)) := by
    change primePairProbability N (fun pq => pq.1 <= B) <=
      primePairProbability N (fun pq => Not (IsUnit (pq.1 : ZMod M)))
    apply prime_pair_probability_mono N
    intro pq hpq hB
    have hpq' : Membership.mem
        ((Nat.primesLE N).product (Nat.primesLE N)) pq := hpq
    have hPrime : Nat.Prime pq.1 :=
      (Nat.mem_primesLE.mp (Finset.mem_product.mp hpq').1).2
    have hMem : Membership.mem (Nat.primesLE B) pq.1 :=
      Nat.mem_primesLE.mpr (And.intro hB hPrime)
    have hDiv : Dvd.dvd pq.1 M := Finset.dvd_prod_of_mem (fun p : Nat => p) hMem
    intro hUnit
    have hCoprime : pq.1.Coprime M := (ZMod.isUnit_iff_coprime pq.1 M).mp hUnit
    exact (hPrime.coprime_iff_not_dvd.mp hCoprime) hDiv
  exact squeeze_zero (fun N => prime_pair_probability_nonneg N _) hDom hLaw

/-- For fixed positive a,b,k, the relation a*p+b*q=k*r with r prime holds
on a zero-density subset of the actual ordered prime-pair ensemble. -/
theorem tendsto_weighted_prime_output_probability_zero
    (a b k : Nat) (ha : 0 < a) (hb : 0 < b) (hk : 0 < k) :
    Tendsto (fun N : Nat => primePairProbability N (fun pq =>
      exists r : Nat, Nat.Prime r /\ a * pq.1 + b * pq.2 = k * r))
      atTop (nhds (0 : Real)) := by
  classical
  let Out : Prod Nat Nat -> Prop := fun pq =>
    exists r : Nat, Nat.Prime r /\ a * pq.1 + b * pq.2 = k * r
  let B : Nat := a + b + k + 2
  have hB : 2 <= B := by dsimp only [B]; omega
  change Tendsto (fun N : Nat => primePairProbability N Out) atTop (nhds (0 : Real))
  apply tendsto_order.mpr
  constructor
  . intro c hc
    exact Filter.Eventually.of_forall (fun N =>
      lt_of_lt_of_le hc (prime_pair_probability_nonneg N Out))
  . intro epsilon hepsilon
    have hProductSmall := (tendsto_weighted_sieve_product_zero B hB).eventually
      (gt_mem_nhds (show (0 : Real) < epsilon / 3 by linarith))
    choose z hz using hProductSmall.exists
    let S : Finset Nat := weightedSievePrimes B z
    let m : S -> Nat := fun i => i.val
    have hp (i : S) : Nat.Prime (m i) :=
      (Finset.mem_filter.mp (Finset.mem_filter.mp i.property).1).2
    have hLarge (i : S) : B < m i := (Finset.mem_filter.mp i.property).2
    have hCeiling (i : S) : m i <= z := by
      change i.val <= z
      have h : i.val < z + 1 := Finset.mem_range.mp
        (Finset.mem_filter.mp (Finset.mem_filter.mp i.property).1).1
      omega
    have hCoprime : Pairwise (fun i j : S => (m i).Coprime (m j)) := by
      intro i j hij
      apply (hp i).coprime_iff_not_dvd.mpr
      intro hDiv
      rcases (Nat.dvd_prime (hp j)).mp hDiv with hone | heq
      . have hi2 := (hp i).two_le
        omega
      . exact hij (Subtype.ext heq)
    have hCoeff (c : Nat) (hpos : 0 < c) (i : S) (hci : c < m i) :
        Not ((c : ZMod (m i)) = 0) := by
      let : NeZero (m i) := NeZero.mk (hp i).ne_zero
      let : Fact (Nat.Prime (m i)) := Fact.mk (hp i)
      have hn : Not (Dvd.dvd (m i) c) := Nat.not_dvd_of_pos_of_lt hpos hci
      have hc : c.Coprime (m i) := ((hp i).coprime_iff_not_dvd.mpr hn).symm
      exact ((ZMod.isUnit_iff_coprime c (m i)).mpr hc).ne_zero
    have haMod (i : S) : Not ((a : ZMod (m i)) = 0) := by
      apply hCoeff a ha i
      have hi := hLarge i
      dsimp only [B] at hi
      omega
    have hbMod (i : S) : Not ((b : ZMod (m i)) = 0) := by
      apply hCoeff b hb i
      have hi := hLarge i
      dsimp only [B] at hi
      omega
    have hkNot (i : S) : Not (Dvd.dvd (m i) k) := by
      apply Nat.not_dvd_of_pos_of_lt hk
      have hi := hLarge i
      dsimp only [B] at hi
      omega
    let Avoid : Prod Nat Nat -> Prop := fun pq => forall i : S,
      Not (Dvd.dvd (m i : Int) ((a : Int) * (pq.1 : Int) + (b : Int) * (pq.2 : Int)))
    have hProduct : Finset.univ.prod (fun i : S =>
        1 - 1 / ((m i : Real) - 1)) = weightedSieveProduct B z := by
      change S.attach.prod (fun i => 1 - 1 / ((i.val : Real) - 1)) =
        S.prod (fun p => 1 - 1 / ((p : Real) - 1))
      exact Finset.prod_attach S (fun p : Nat => 1 - 1 / ((p : Real) - 1))
    have hAvoid : Tendsto (fun N : Nat => primePairProbability N Avoid) atTop
        (nhds (weightedSieveProduct B z)) := by
      have ht := tendsto_prime_pair_weighted_nondivisibility_pattern
        m hp hCoprime a b haMod hbMod
      rw [hProduct] at ht
      exact ht
    have hDom (N : Nat) :
        primePairProbability N Out <= primePairProbability N Avoid +
          primePairProbability N (fun pq => pq.1 <= k * z) := by
      apply prime_pair_probability_or_bound N Out Avoid
      intro pq hpq hOut
      choose r hr heq using hOut
      by_cases hSmall : pq.1 <= k * z
      . exact Or.inr hSmall
      . apply Or.inl
        intro i hDiv
        have hDivNat : Dvd.dvd (m i) (a * pq.1 + b * pq.2) := by
          exact_mod_cast hDiv
        have hDivKr : Dvd.dvd (m i) (k * r) := by
          rw [heq] at hDivNat
          exact hDivNat
        have hDivR : Dvd.dvd (m i) r :=
          ((hp i).dvd_mul.mp hDivKr).resolve_left (hkNot i)
        have hEq : m i = r := by
          rcases (Nat.dvd_prime hr).mp hDivR with hone | hprimeEq
          . have hi2 := (hp i).two_le
            omega
          . exact hprimeEq
        have hrz : r <= z := by
          rw [<- hEq]
          exact hCeiling i
        have hpA : pq.1 <= a * pq.1 := by
          simpa only [one_mul] using
            Nat.mul_le_mul_right pq.1 (show 1 <= a by omega)
        have hpBound : pq.1 <= k * z := calc
          pq.1 <= a * pq.1 := hpA
          _ <= a * pq.1 + b * pq.2 := by omega
          _ = k * r := heq
          _ <= k * z := Nat.mul_le_mul_left k hrz
        exact hSmall hpBound
    have hAvoidEventually := hAvoid.eventually
      (gt_mem_nhds (show weightedSieveProduct B z < epsilon / 2 by
        linarith only [hz, hepsilon]))
    have hSmallEventually := (tendsto_prime_pair_small_first_probability_zero (k * z)).eventually
      (gt_mem_nhds (show (0 : Real) < epsilon / 2 by linarith))
    filter_upwards [hAvoidEventually, hSmallEventually] with N hAvoidN hSmallN
    have hd := hDom N
    linarith only [hd, hAvoidN, hSmallN]

end PrimeFactorOscillations

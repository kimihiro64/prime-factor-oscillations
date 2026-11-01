/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Data.Nat.Squarefree
import PrimeFactorOscillations.Assembly.FiniteFieldNativeRowFibres
import PrimeFactorOscillations.Proof.AffinePairs.WeightedSieveDecay

/-!
# Sparse native collisions from positive weighted prime outputs

The two arguments are actual prime endpoints. Both native row types are
retained. A distinct collision forces the larger square-root multiplier
to witness one of finitely many positive weighted prime-output events.
-/

set_option autoImplicit false
set_option Elab.async false

open Filter
open scoped Classical Topology

namespace PrimeFactorOscillations.FiniteFieldIntegerSignature

def nativeWeightedEndpointPrimeOutput (T p q : Nat) : Prop :=
  exists u v : Nat, 0 < v /\ v < u /\ u < T /\
    ((exists r : Nat, Nat.Prime r /\
      (u ^ 2 - v ^ 2) * p + v ^ 2 * q = u ^ 2 * r) \/
     (exists r : Nat, Nat.Prime r /\
      v ^ 2 * p + (u ^ 2 - v ^ 2) * q = u ^ 2 * r))

private theorem native_clean_avoiding_weighted_outputs_flat
    (S : Finset (Prod Nat Nat)) (T : Nat)
    (hprime : forall a : Prod Nat Nat, Membership.mem S a ->
      Nat.Prime a.1 /\ Nat.Prime (a.1 + a.2) /\ 0 < a.2 /\ a.2 < a.1)
    (hclean : forall a : Prod Nat Nat, Membership.mem S a ->
      forall u : Nat, T <= u -> Not (Dvd.dvd (u ^ 2) a.2))
    (havoid : forall a : Prod Nat Nat, Membership.mem S a ->
      Not (nativeWeightedEndpointPrimeOutput T a.1 (a.1 + a.2))) :
    forall a : Prod Nat Nat, Membership.mem S a ->
      forall b : Prod Nat Nat, Membership.mem S b -> Not (a = b) ->
        nativeAgreementRate a.1 a.2 b.1 b.2 = 3 / 8 := by
  classical
  have hfactor : forall a : Prod Nat Nat, exists d u : Nat,
      Membership.mem S a ->
        0 < d /\ 0 < u /\ u ^ 2 * d = a.2 /\ Squarefree d := by
    intro a
    by_cases ha : Membership.mem S a
    . choose d u hd hu he hs using Nat.sq_mul_squarefree_of_pos (hprime a ha).2.2.1
      exact Exists.intro d (Exists.intro u (fun _ => And.intro hd
        (And.intro hu (And.intro he hs))))
    . exact Exists.intro 1 (Exists.intro 1 (fun h => False.elim (ha h)))
  choose d u hdu using hfactor
  have hroot (a : Prod Nat Nat) (ha : Membership.mem S a) : u a < T := by
    by_contra hnot
    exact hclean a ha (u a) (le_of_not_gt hnot)
      (Exists.intro (d a) (hdu a ha).2.2.1.symm)
  have hcore (a b : Prod Nat Nat) (ha : Membership.mem S a)
      (hb : Membership.mem S b) (v : Nat) (hv : 0 < v)
      (hs : IsSquare (a.2 * b.2 * v * v)) : d a = d b := by
    let z := Classical.choose hs
    have hz : a.2 * b.2 * v * v = z * z := Classical.choose_spec hs
    let w := u a * u b * v
    have hw : 0 < w := Nat.mul_pos
      (Nat.mul_pos (hdu a ha).2.1 (hdu b hb).2.1) hv
    have he : w * w * (d a * d b) = z * z := by
      calc
        w * w * (d a * d b) = a.2 * b.2 * v * v := by
          rw [<- (hdu a ha).2.2.1, <- (hdu b hb).2.2.1]
          dsimp [w]
          ring
        _ = z * z := hz
    have hdiv : Dvd.dvd (w ^ 2) (z ^ 2) :=
      Exists.intro (d a * d b) (by simpa only [pow_two] using he.symm)
    have hdz : Dvd.dvd w z :=
      (Nat.pow_dvd_pow_iff (by decide : Not ((2 : Nat) = 0))).mp hdiv
    let t := Classical.choose hdz
    have hzt : z = w * t := Classical.choose_spec hdz
    have he' : (w * w) * (d a * d b) = (w * w) * (t * t) := by
      calc
        (w * w) * (d a * d b) = z * z := he
        _ = (w * w) * (t * t) := by rw [hzt]; ring
    have hsq : IsSquare (d a * d b) :=
      Exists.intro t (Nat.eq_of_mul_eq_mul_left (Nat.mul_pos hw hw) he')
    have hsq' : IsSquare (d b * d a) := by simpa only [mul_comm] using hsq
    exact Nat.dvd_antisymm
      (Squarefree.dvd_of_isSquare_mul (hdu a ha).2.2.2 hsq)
      (Squarefree.dvd_of_isSquare_mul (hdu b hb).2.2.2 hsq')
  have hbadLower (a b : Prod Nat Nat) (ha : Membership.mem S a)
      (hb : Membership.mem S b) (hn : a.1 = b.1)
      (hd : d a = d b) (hu : u b < u a) : False := by
    apply havoid a ha
    refine Exists.intro (u a) (Exists.intro (u b)
      (And.intro (hdu b hb).2.1 (And.intro hu (And.intro (hroot a ha) ?_))))
    apply Or.inl
    refine Exists.intro (b.1 + b.2) (And.intro (hprime b hb).2.1 ?_)
    have hcoef : (u a ^ 2 - u b ^ 2) + u b ^ 2 = u a ^ 2 :=
      Nat.sub_add_cancel (Nat.pow_le_pow_left (Nat.le_of_lt hu) 2)
    calc
      (u a ^ 2 - u b ^ 2) * a.1 + u b ^ 2 * (a.1 + a.2) =
          ((u a ^ 2 - u b ^ 2) + u b ^ 2) * a.1 + u b ^ 2 * a.2 := by ring
      _ = u a ^ 2 * a.1 + u b ^ 2 * (u a ^ 2 * d a) := by
        rw [hcoef, <- (hdu a ha).2.2.1]
      _ = u a ^ 2 * (a.1 + u b ^ 2 * d a) := by ring
      _ = u a ^ 2 * (b.1 + b.2) := by rw [hn, hd, (hdu b hb).2.2.1]
  have hbadUpper (a b : Prod Nat Nat) (ha : Membership.mem S a)
      (hb : Membership.mem S b) (hq : a.1 + a.2 = b.1 + b.2)
      (hd : d a = d b) (hu : u b < u a) : False := by
    apply havoid a ha
    refine Exists.intro (u a) (Exists.intro (u b)
      (And.intro (hdu b hb).2.1 (And.intro hu (And.intro (hroot a ha) ?_))))
    apply Or.inr
    refine Exists.intro b.1 (And.intro (hprime b hb).1 ?_)
    have hcoef : (u a ^ 2 - u b ^ 2) + u b ^ 2 = u a ^ 2 :=
      Nat.sub_add_cancel (Nat.pow_le_pow_left (Nat.le_of_lt hu) 2)
    have hcross : u a ^ 2 * b.2 = u b ^ 2 * a.2 := by
      rw [<- (hdu a ha).2.2.1, <- (hdu b hb).2.2.1, <- hd]
      ring
    suffices he : (u b ^ 2 * a.1 + (u a ^ 2 - u b ^ 2) * (a.1 + a.2)) +
        u a ^ 2 * b.2 = (u a ^ 2 * b.1) + u a ^ 2 * b.2 by omega
    calc
      (u b ^ 2 * a.1 + (u a ^ 2 - u b ^ 2) * (a.1 + a.2)) + u a ^ 2 * b.2 =
          ((u a ^ 2 - u b ^ 2) + u b ^ 2) * (a.1 + a.2) := by rw [hcross]; ring
      _ = u a ^ 2 * (a.1 + a.2) := by rw [hcoef]
      _ = u a ^ 2 * (b.1 + b.2) := by rw [hq]
      _ = (u a ^ 2 * b.1) + u a ^ 2 * b.2 := by ring
  intro a ha b hb hneq
  have haP := hprime a ha
  have hbP := hprime b hb
  have hneq' : Not (And (a.1 = b.1) (a.2 = b.2)) := by
    intro h
    exact hneq (Prod.ext h.1 h.2)
  apply (native_agreement_arithmetic_classification a.1 a.2 b.1 b.2
    haP.1 haP.2.1 hbP.1 hbP.2.1 haP.2.2.1 hbP.2.2.1 hneq').2.mpr
  constructor
  . intro hs
    have hn : a.1 = b.1 :=
      (native_square_rows_recover_endpoints a.1 a.2 b.1 b.2
        haP.1 haP.2.1 hbP.1 hbP.2.1 haP.2.2.1 hbP.2.2.1).1
          haP.2.2.2 hbP.2.2.2 hs
    have hs' : IsSquare (a.2 * b.2 * a.1 * a.1) := by
      simpa only [<- hn] using hs
    have hd := hcore a b ha hb a.1 haP.1.pos hs'
    rcases lt_trichotomy (u a) (u b) with hlt | he | hgt
    . exact hbadLower b a hb ha hn.symm hd.symm hlt
    . have hh : a.2 = b.2 := by
        rw [<- (hdu a ha).2.2.1, <- (hdu b hb).2.2.1, he, hd]
      exact hneq (Prod.ext hn hh)
    . exact hbadLower a b ha hb hn hd hgt
  . intro hs
    have hq : a.1 + a.2 = b.1 + b.2 :=
      (native_square_rows_recover_endpoints a.1 a.2 b.1 b.2
        haP.1 haP.2.1 hbP.1 hbP.2.1 haP.2.2.1 hbP.2.2.1).2 hs
    have hs' : IsSquare (a.2 * b.2 * (a.1 + a.2) * (a.1 + a.2)) := by
      simpa only [<- hq] using hs
    have hd := hcore a b ha hb (a.1 + a.2) haP.2.1.pos hs'
    rcases lt_trichotomy (u a) (u b) with hlt | he | hgt
    . exact hbadUpper b a hb ha hq.symm hd.symm hlt
    . have hh : a.2 = b.2 := by
        rw [<- (hdu a ha).2.2.1, <- (hdu b hb).2.2.1, he, hd]
      exact hneq (Prod.ext (by omega) hh)
    . exact hbadUpper a b ha hb hq hd hgt


/-- Exact finite deletion consumer: remove the actual prime-output anchors,
with both native row types included and no matching-factor loss. -/
theorem native_clean_sparse_collision_packing
    (S : Finset (Prod Nat Nat)) (T Y : Nat)
    (hprime : forall a : Prod Nat Nat, Membership.mem S a ->
      Nat.Prime a.1 /\ Nat.Prime (a.1 + a.2) /\ 0 < a.2 /\
        a.2 < a.1 /\ a.1 + a.2 <= Y)
    (hclean : forall a : Prod Nat Nat, Membership.mem S a ->
      forall u : Nat, T <= u -> Not (Dvd.dvd (u ^ 2) a.2)) :
    exists M : Finset (Prod Nat Nat), M <= S /\
      S.card <= M.card +
        ((primePairs Y).filter (fun pq => nativeWeightedEndpointPrimeOutput T pq.1 pq.2)).card /\
      forall a : Prod Nat Nat, Membership.mem M a ->
        forall b : Prod Nat Nat, Membership.mem M b -> Not (a = b) ->
          nativeAgreementRate a.1 a.2 b.1 b.2 = 3 / 8 := by
  classical
  let M := S.filter (fun a => Not (nativeWeightedEndpointPrimeOutput T a.1 (a.1 + a.2)))
  let B := S.filter (fun a => nativeWeightedEndpointPrimeOutput T a.1 (a.1 + a.2))
  have hM : M <= S := Finset.filter_subset _ _
  have hcover : S <= Union.union M B := by
    intro a ha
    by_cases hout : nativeWeightedEndpointPrimeOutput T a.1 (a.1 + a.2)
    . exact Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr (And.intro ha hout)))
    . exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr (And.intro ha hout)))
  have hB : B.card <=
      ((primePairs Y).filter (fun pq => nativeWeightedEndpointPrimeOutput T pq.1 pq.2)).card := by
    apply Finset.card_le_card_of_injOn (fun a : Prod Nat Nat => Prod.mk a.1 (a.1 + a.2))
    . intro a ha
      have haS := (Finset.mem_filter.mp ha).1
      have hp := hprime a haS
      apply Finset.mem_filter.mpr
      refine And.intro ?_ (Finset.mem_filter.mp ha).2
      change Membership.mem ((Nat.primesLE Y).product (Nat.primesLE Y))
        (Prod.mk a.1 (a.1 + a.2))
      exact Finset.mem_product.mpr (And.intro
        (Nat.mem_primesLE.mpr (And.intro (by omega) hp.1))
        (Nat.mem_primesLE.mpr (And.intro hp.2.2.2.2 hp.2.1)))
    . intro a ha b hb he
      have hp1 := congrArg (fun z : Prod Nat Nat => z.1) he
      have hp2 := congrArg (fun z : Prod Nat Nat => z.2) he
      have hn : a.1 = b.1 := hp1
      have hq : a.1 + a.2 = b.1 + b.2 := hp2
      exact Prod.ext hn (by omega)
  refine Exists.intro M (And.intro hM (And.intro ?_ ?_))
  . exact (Finset.card_le_card hcover).trans
      ((Finset.card_union_le M B).trans (Nat.add_le_add_left hB M.card))
  . apply native_clean_avoiding_weighted_outputs_flat M T
    . intro a ha
      have hp := hprime a (hM ha)
      exact And.intro hp.1 (And.intro hp.2.1 (And.intro hp.2.2.1 hp.2.2.2.1))
    . intro a ha
      exact hclean a (hM ha)
    . intro a ha
      exact (Finset.mem_filter.mp ha).2

/-- The complete fixed-root collision event has zero actual prime-pair density.
The root cutoff is fixed before the independent sampling height tends to infinity. -/
theorem tendsto_native_weighted_endpoint_output_probability_zero (T : Nat) :
    Filter.Tendsto (fun N : Nat => primePairProbability N
      (fun pq => nativeWeightedEndpointPrimeOutput T pq.1 pq.2))
      Filter.atTop (nhds (0 : Real)) := by
  classical
  let I := Prod (Prod (Fin T) (Fin T)) Bool
  let Valid : I -> Prop := fun i => 0 < i.1.2.val /\ i.1.2.val < i.1.1.val
  let ca : I -> Nat := fun i =>
    if i.2 = true then i.1.2.val ^ 2 else i.1.1.val ^ 2 - i.1.2.val ^ 2
  let cb : I -> Nat := fun i =>
    if i.2 = true then i.1.1.val ^ 2 - i.1.2.val ^ 2 else i.1.2.val ^ 2
  let P : I -> Prod Nat Nat -> Prop := fun i pq =>
    Valid i /\ exists r : Nat, Nat.Prime r /\
      ca i * pq.1 + cb i * pq.2 = i.1.1.val ^ 2 * r
  have hlocal (i : I) : Filter.Tendsto
      (fun N : Nat => primePairProbability N (P i)) Filter.atTop (nhds (0 : Real)) := by
    by_cases hv : Valid i
    . have hvp : 0 < i.1.2.val /\ i.1.2.val < i.1.1.val := hv
      have hu : 0 < i.1.1.val := by omega
      have hv2 : 0 < i.1.2.val ^ 2 := pow_pos hvp.1 2
      have hd : 0 < i.1.1.val ^ 2 - i.1.2.val ^ 2 := by
        have hh : i.1.2.val ^ 2 < i.1.1.val ^ 2 := by nlinarith [hvp.1, hvp.2]
        exact Nat.sub_pos_of_lt hh
      have ha : 0 < ca i := by dsimp only [ca]; split_ifs <;> assumption
      have hb : 0 < cb i := by dsimp only [cb]; split_ifs <;> assumption
      have h := tendsto_weighted_prime_output_probability_zero
        (ca i) (cb i) (i.1.1.val ^ 2) ha hb (pow_pos hu 2)
      simpa only [P, hv, true_and] using h
    . have he : (fun N : Nat => primePairProbability N (P i)) = (fun _ : Nat => (0 : Real)) := by
        funext N
        simp only [P, hv, false_and, primePairProbability, Finset.filter_false,
          Finset.card_empty, Nat.cast_zero, zero_div]
      rw [he]
      exact tendsto_const_nhds
  have hcover (pq : Prod Nat Nat) (hout : nativeWeightedEndpointPrimeOutput T pq.1 pq.2) :
      exists i : I, P i pq := by
    choose u v hv hlt huT hrow using hout
    let fu : Fin T := Fin.mk u huT
    let fv : Fin T := Fin.mk v (hlt.trans huT)
    rcases hrow with hl | hr
    . exact Exists.intro (Prod.mk (Prod.mk fu fv) false)
        (And.intro (And.intro hv hlt) hl)
    . exact Exists.intro (Prod.mk (Prod.mk fu fv) true)
        (And.intro (And.intro hv hlt) hr)
  have hbound (N : Nat) : primePairProbability N
      (fun pq => nativeWeightedEndpointPrimeOutput T pq.1 pq.2) <=
        Finset.univ.sum (fun i : I => primePairProbability N (P i)) := by
    let C : I -> Finset (Prod Nat Nat) := fun i => (primePairs N).filter (P i)
    have hs : (primePairs N).filter (fun pq => nativeWeightedEndpointPrimeOutput T pq.1 pq.2) <=
        Finset.univ.biUnion C := by
      intro pq hpq
      have hh := Finset.mem_filter.mp hpq
      choose i hi using hcover pq hh.2
      exact Finset.mem_biUnion.mpr (Exists.intro i
        (And.intro (Finset.mem_univ i) (Finset.mem_filter.mpr (And.intro hh.1 hi))))
    have hc := (Finset.card_le_card hs).trans Finset.card_biUnion_le
    have hcast :
        (((primePairs N).filter (fun pq => nativeWeightedEndpointPrimeOutput T pq.1 pq.2)).card : Real) <=
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

end PrimeFactorOscillations.FiniteFieldIntegerSignature

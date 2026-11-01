/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Mathlib.Algebra.Field.FiniteAffineRoots
import PrimeFactorOscillations.Proof.AffinePairs.CRTLimits

/-!
# Exact fixed-prime sieve for weighted prime-pair outputs

The two coefficients can differ. This supplies the finite collision sieve
for the density-one native codebook programme, without replacing a weighted
linear form by a family that depends only on the sum of its inputs.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations

open scoped Classical

private theorem weighted_unit_zero_count (p : Nat) [NeZero p]
    (hp : Nat.Prime p) (a b : ZMod p)
    (ha : Not (a = 0)) (hb : Not (b = 0)) :
    Nat.card {xy : Prod (Units (ZMod p)) (Units (ZMod p)) //
      a * (xy.1 : ZMod p) + b * (xy.2 : ZMod p) = 0} = p - 1 := by
  let : Fact (Nat.Prime p) := Fact.mk hp
  let P : Prod (ZMod p) (ZMod p) -> Prop :=
    fun xy => a * xy.1 + b * xy.2 = 0
  let N : Nat := (((Finset.univ.erase (0 : ZMod p)).product
    (Finset.univ.erase (0 : ZMod p))).filter P).card
  have hunit (x : ZMod p) : IsUnit x <-> Not (x = 0) := isUnit_iff_ne_zero
  have hcount : Nat.card {xy : Prod (Units (ZMod p)) (Units (ZMod p)) //
      a * (xy.1 : ZMod p) + b * (xy.2 : ZMod p) = 0} = N := by
    rw [<- ZMod.natCard_unit_pair_event_eq_filter p P]
    dsimp only [N]
    apply congrArg Finset.card
    apply Finset.ext
    intro xy
    have hprod : Membership.mem ((Finset.univ.erase (0 : ZMod p)).product
        (Finset.univ.erase (0 : ZMod p))) xy <->
        Membership.mem (Finset.univ.erase (0 : ZMod p)) xy.1 /\
        Membership.mem (Finset.univ.erase (0 : ZMod p)) xy.2 := Finset.mem_product
    simp only [Finset.mem_filter, Finset.mem_univ, hprod, Finset.mem_erase,
      hunit, true_and, and_comm, P]
  rw [hcount]
  dsimp only [N, P]
  simpa only [ZMod.card] using Finset.card_nonzero_linear_sum_zero a b ha hb

private theorem weighted_unit_nonzero_probability (p : Nat) [NeZero p]
    (hp : Nat.Prime p) (a b : ZMod p)
    (ha : Not (a = 0)) (hb : Not (b = 0)) :
    (Nat.card {xy : Prod (Units (ZMod p)) (Units (ZMod p)) //
      Not (a * (xy.1 : ZMod p) + b * (xy.2 : ZMod p) = 0)} : Real) /
      (p.totient : Real) ^ 2 = 1 - 1 / ((p : Real) - 1) := by
  let P : Prod (Units (ZMod p)) (Units (ZMod p)) -> Prop :=
    fun xy => a * (xy.1 : ZMod p) + b * (xy.2 : ZMod p) = 0
  have hamb : Fintype.card (Prod (Units (ZMod p)) (Units (ZMod p))) =
      p.totient ^ 2 := by
    simp only [Fintype.card_prod, ZMod.card_units_eq_totient, pow_two]
  have hle : Nat.card {xy // P xy} <= p.totient ^ 2 := by
    rw [Nat.card_eq_fintype_card, <- hamb]
    exact Fintype.card_subtype_le P
  have hcompl : Nat.card {xy // Not (P xy)} =
      p.totient ^ 2 - Nat.card {xy // P xy} := by
    simp only [Nat.card_eq_fintype_card]
    rw [Fintype.card_subtype_compl P, hamb]
  have hphi : 0 < (p.totient : Real) := by exact_mod_cast Nat.totient_pos.mpr hp.pos
  have hz : Nat.card {xy // P xy} = p - 1 := weighted_unit_zero_count p hp a b ha hb
  change (Nat.card {xy // Not (P xy)} : Real) / (p.totient : Real) ^ 2 = _
  rw [hcompl, Nat.cast_sub hle, Nat.cast_pow, sub_div,
    div_self (pow_ne_zero 2 (ne_of_gt hphi)), hz]
  rw [Nat.totient_prime hp, Nat.cast_sub hp.one_lt.le, Nat.cast_one] at hphi
  rw [Nat.totient_prime hp, Nat.cast_sub hp.one_lt.le, Nat.cast_one]
  rw [pow_two, <- div_div, div_self (ne_of_gt hphi)]

/-- Independent reduced prime residues give the exact finite sieve product
for arbitrary fixed weighted sums with nonzero local coefficients. -/
theorem tendsto_prime_pair_weighted_sieve_pattern {I : Type*} [Fintype I]
    (m : I -> Nat) (hp : forall i : I, Nat.Prime (m i))
    (hc : Pairwise (fun i j : I => (m i).Coprime (m j)))
    (a b : Nat)
    (ha : forall i : I, Not ((a : ZMod (m i)) = 0))
    (hb : forall i : I, Not ((b : ZMod (m i)) = 0)) :
    Filter.Tendsto (fun N : Nat =>
      primePairResidueEventProbability N (Finset.univ.prod m)
        (fun xy => forall i : I,
          Not ((a : ZMod (m i)) *
            ((ZMod.prodEquivPi m hc xy.1) i) +
            (b : ZMod (m i)) *
            ((ZMod.prodEquivPi m hc xy.2) i) = 0)))
      Filter.atTop
      (nhds (Finset.univ.prod (fun i : I =>
        1 - 1 / ((m i : Real) - 1)))) := by
  let : forall i : I, NeZero (m i) := fun i => NeZero.mk (hp i).ne_zero
  let : NeZero (Finset.univ.prod m) := NeZero.mk
    (Finset.prod_ne_zero_iff.mpr (fun i _ => (hp i).ne_zero))
  let P : forall i : I, Prod (ZMod (m i)) (ZMod (m i)) -> Prop :=
    fun i xy => Not ((a : ZMod (m i)) * xy.1 + (b : ZMod (m i)) * xy.2 = 0)
  have hterm (i : I) :
      (Nat.card {xy : Prod (Units (ZMod (m i))) (Units (ZMod (m i))) //
        P i ((xy.1 : ZMod (m i)), (xy.2 : ZMod (m i)))} : Real) /
        ((m i).totient : Real) ^ 2 = 1 - 1 / ((m i : Real) - 1) :=
    weighted_unit_nonzero_probability (m i) (hp i) a b (ha i) (hb i)
  have ht := tendsto_prime_pair_crt_pattern_probability m hc P
  simpa only [hterm] using ht

/-- The finite sieve product applies directly to the actual integer weighted
outputs of both sampled prime inputs. All moduli are fixed before the cutoff. -/
theorem tendsto_prime_pair_weighted_nondivisibility_pattern {I : Type*} [Fintype I]
    (m : I -> Nat) (hp : forall i : I, Nat.Prime (m i))
    (hc : Pairwise (fun i j : I => (m i).Coprime (m j)))
    (a b : Nat)
    (ha : forall i : I, Not ((a : ZMod (m i)) = 0))
    (hb : forall i : I, Not ((b : ZMod (m i)) = 0)) :
    Filter.Tendsto (fun N : Nat => primePairProbability N (fun pq =>
      forall i : I, Not (Dvd.dvd (m i : Int)
        ((a : Int) * (pq.1 : Int) + (b : Int) * (pq.2 : Int)))))
      Filter.atTop
      (nhds (Finset.univ.prod (fun i : I =>
        1 - 1 / ((m i : Real) - 1)))) := by
  let value (p q : Nat) : Int := (a : Int) * (p : Int) + (b : Int) * (q : Int)
  have hcast (x : Nat) (i : I) :
      (ZMod.prodEquivPi m hc (x : ZMod (Finset.univ.prod m))) i =
        (x : ZMod (m i)) :=
    congrFun (map_natCast (ZMod.prodEquivPi m hc) x) i
  have hEval (p q : Nat) (i : I) :
      (a : ZMod (m i)) *
          ((ZMod.prodEquivPi m hc (p : ZMod (Finset.univ.prod m))) i) +
        (b : ZMod (m i)) *
          ((ZMod.prodEquivPi m hc (q : ZMod (Finset.univ.prod m))) i) =
      (value p q : ZMod (m i)) := by
    rw [hcast p i, hcast q i]
    simp only [value, Int.cast_add, Int.cast_mul, Int.cast_natCast]
  have hProb (N : Nat) :
      primePairProbability N (fun pq =>
        forall i : I, Not (Dvd.dvd (m i : Int)
          ((a : Int) * (pq.1 : Int) + (b : Int) * (pq.2 : Int)))) =
      primePairResidueEventProbability N (Finset.univ.prod m)
        (fun xy => forall i : I,
          Not ((a : ZMod (m i)) *
            ((ZMod.prodEquivPi m hc xy.1) i) +
            (b : ZMod (m i)) *
            ((ZMod.prodEquivPi m hc xy.2) i) = 0)) := by
    unfold primePairResidueEventProbability
    apply congrArg (primePairProbability N)
    funext pq
    apply propext
    apply forall_congr'
    intro i
    rw [hEval]
    exact not_congr (ZMod.intCast_zmod_eq_zero_iff_dvd
      ((a : Int) * (pq.1 : Int) + (b : Int) * (pq.2 : Int)) (m i)).symm
  have ht := tendsto_prime_pair_weighted_sieve_pattern m hp hc a b ha hb
  simpa only [hProb] using ht

end PrimeFactorOscillations

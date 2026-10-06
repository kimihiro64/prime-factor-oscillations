/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.ConditionalLocation.EsymmPrefixOrder
import PrimeFactorOscillations.Helpers.GenericOddPrefix
import PrimeFactorOscillations.Helpers.LocalMassGenerating
import PrimeFactorOscillations.Helpers.LocalMassPermutation
import PrimeFactorUnimodality.Helpers.FirstDifference.PrimeSequence

/-!
# Local Ratio Prefix Order

Maintained implementation of the conditional last-ascent location argument.
The arithmetic coverage assumptions remain explicit; no conjecture is an axiom.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations

theorem local_ratio_cons_le (eta : Nat -> Rat) (xs : List Nat)
    (hprob : forall p, List.Mem p xs -> 0 <= eta p /\ eta p < 1)
    (p r : Nat) (hp : 0 <= eta p /\ eta p < 1) (hr : 1 <= r)
    (hden : 0 < finiteLocalMass eta xs r) :
    finiteLocalMass eta (p :: xs) (r - 1) / finiteLocalMass eta (p :: xs) r <=
      finiteLocalMass eta xs (r - 1) / finiteLocalMass eta xs r := by
  let w := xs.map (fun q => eta q / (1 - eta q))
  have hw : forall a, Membership.mem (w : Multiset Rat) a -> 0 <= a := by
    intro a ha
    choose q hq using List.mem_map.mp ha
    rw [<- hq.2]
    exact div_nonneg (hprob q hq.1).1 (le_of_lt (sub_pos.mpr (hprob q hq.1).2))
  have he : 0 < (w : Multiset Rat).esymm r := by
    rw [finiteLocalMass_eq_base_mul_esymm eta xs
      (fun q hq => ne_of_lt (hprob q hq).2) r] at hden
    exact (mul_pos_iff_of_pos_left
      (local_complement_prod_pos eta xs (fun q hq => (hprob q hq).2))).mp hden
  have hbelow : forall q, List.Mem q (p :: xs) -> eta q < 1 := by
    intro q hq
    rcases List.mem_cons.mp hq with hq | hq
    next => subst q; exact hp.2
    next => exact (hprob q hq).2
  rw [local_densityRatio_eq_esymm_ratio eta (p :: xs) hbelow r,
    local_densityRatio_eq_esymm_ratio eta xs (fun q hq => (hprob q hq).2) r]
  exact Multiset.esymm_ratio_cons_le_rat (w : Multiset Rat) hw
    (eta p / (1 - eta p)) (div_nonneg hp.1 (le_of_lt (sub_pos.mpr hp.2))) r hr he

theorem local_mass_cons_pos_of_pos (eta : Nat -> Rat) (xs : List Nat)
    (hprob : forall p, List.Mem p xs -> 0 <= eta p /\ eta p < 1)
    (p r : Nat) (hp : 0 <= eta p /\ eta p < 1)
    (hden : 0 < finiteLocalMass eta xs r) :
    0 < finiteLocalMass eta (p :: xs) r := by
  cases r with
  | zero => exact mul_pos (sub_pos.mpr hp.2) hden
  | succ r =>
      exact add_pos_of_pos_of_nonneg (mul_pos (sub_pos.mpr hp.2) hden)
        (mul_nonneg hp.1 (finiteLocalMass_nonneg eta xs
          (fun q hq => And.intro (hprob q hq).1 (le_of_lt (hprob q hq).2)) r))

noncomputable section

def localPrimeRatio (eta : Nat -> Rat) (r i : Nat) : Rat :=
  finiteLocalMass eta (PrimeFactorUnimodality.primesBelow
    (PrimeFactorUnimodality.primeAt i)) (r - 1) /
  finiteLocalMass eta (PrimeFactorUnimodality.primesBelow
    (PrimeFactorUnimodality.primeAt i)) r

theorem localPrimeRatio_step (eta : Nat -> Rat)
    (hprob : forall p, Nat.Prime p -> 0 <= eta p /\ eta p < 1)
    (r i : Nat) (hr : 1 <= r)
    (hden : 0 < finiteLocalMass eta
      (PrimeFactorUnimodality.primesBelow (PrimeFactorUnimodality.primeAt i)) r) :
    0 < finiteLocalMass eta
        (PrimeFactorUnimodality.primesBelow (PrimeFactorUnimodality.primeAt (i + 1))) r /\
      localPrimeRatio eta r (i + 1) <= localPrimeRatio eta r i := by
  have hp := hprob _ (PrimeFactorUnimodality.prime_primeAt i)
  have hx : forall p, List.Mem p
      (PrimeFactorUnimodality.primesBelow (PrimeFactorUnimodality.primeAt i)) ->
        0 <= eta p /\ eta p < 1 := by
    intro p hmem
    exact hprob p (PrimeFactorUnimodality.primesBelow_entries _ _ hmem).1
  have heq := fun d => finiteLocalMass_perm eta _ _
    (PrimeFactorUnimodality.primesBelow_primeAt_succ_perm i) d
  constructor
  next =>
    rw [heq r]
    exact local_mass_cons_pos_of_pos eta _ hx _ r hp hden
  next =>
    unfold localPrimeRatio
    rw [heq (r - 1), heq r]
    exact local_ratio_cons_le eta _ hx _ r hp hr hden

theorem localPrimeRatio_antitone_from (eta : Nat -> Rat)
    (hprob : forall p, Nat.Prime p -> 0 <= eta p /\ eta p < 1)
    (r i j : Nat) (hr : 1 <= r) (hij : i <= j)
    (hden : 0 < finiteLocalMass eta
      (PrimeFactorUnimodality.primesBelow (PrimeFactorUnimodality.primeAt i)) r) :
    0 < finiteLocalMass eta
        (PrimeFactorUnimodality.primesBelow (PrimeFactorUnimodality.primeAt j)) r /\
      localPrimeRatio eta r j <= localPrimeRatio eta r i := by
  induction j, hij using Nat.le_induction with
  | base => exact And.intro hden (le_refl _)
  | succ j hij ih =>
      have h := localPrimeRatio_step eta hprob r j hr ih.1
      exact And.intro h.1 (h.2.trans ih.2)

theorem ordinaryEta_prime_probabilities (p : Nat) (hp : Nat.Prime p) :
    0 <= (1 : Rat) / p /\ (1 : Rat) / p < 1 := by
  have hpR : (1 : Rat) < p := by exact_mod_cast hp.one_lt
  constructor
  next => exact div_nonneg (by norm_num) (by linarith)
  next => exact (div_lt_one (by linarith)).mpr hpR

theorem genericOddEta_prime_probabilities (p : Nat) (hp : Nat.Prime p) :
    0 <= genericOddEta p /\ genericOddEta p < 1 := by
  by_cases heq : p = 2
  next => subst p; norm_num [genericOddEta]
  next =>
    have hgt : 2 < p := lt_of_le_of_ne hp.two_le (Ne.symm heq)
    exact And.intro (le_of_lt (genericOddEta_pos p hgt)) (genericOddEta_lt_one p hgt)

def genericTwinThreshold (p : Nat) : Rat :=
  3 - 2 / ((p : Rat) * ((p : Rat) - 2))

theorem genericTwinThreshold_mono (p q : Nat) (hp : 2 < p) (hpq : p <= q) :
    genericTwinThreshold p <= genericTwinThreshold q := by
  have hpR : (2 : Rat) < p := by exact_mod_cast hp
  have hpqR : (p : Rat) <= q := by exact_mod_cast hpq
  have hd : (0 : Rat) < (p : Rat) * ((p : Rat) - 2) :=
    mul_pos (by linarith) (by linarith)
  have hprod : (p : Rat) * ((p : Rat) - 2) <= (q : Rat) * ((q : Rat) - 2) := by
    nlinarith
  have hdiv := div_le_div_of_nonneg_left (show (0 : Rat) <= 2 by norm_num) hd hprod
  unfold genericTwinThreshold
  linarith

/-- The actual generic canonical twin criterion has no holes on its supported range. -/
theorem generic_twin_potential_initial_segment (r i j : Nat) (hr : 1 <= r)
    (hij : i <= j) (hp : 2 < PrimeFactorUnimodality.primeAt i)
    (hden : 0 < finiteLocalMass genericOddEta
      (PrimeFactorUnimodality.primesBelow (PrimeFactorUnimodality.primeAt i)) r)
    (hj : genericTwinThreshold (PrimeFactorUnimodality.primeAt j) <
      localPrimeRatio genericOddEta r j) :
    genericTwinThreshold (PrimeFactorUnimodality.primeAt i) <
      localPrimeRatio genericOddEta r i := by
  have hratio := localPrimeRatio_antitone_from genericOddEta
    genericOddEta_prime_probabilities r i j hr hij hden
  exact (genericTwinThreshold_mono _ _ hp
    (PrimeFactorUnimodality.primeAt_strictMono.monotone hij)).trans_lt (hj.trans_le hratio.2)

/-- The ordinary canonical twin criterion has the same initial-segment property. -/
theorem ordinary_twin_potential_initial_segment (r i j : Nat) (hr : 1 <= r)
    (hij : i <= j)
    (hden : 0 < finiteLocalMass (fun p => 1 / (p : Rat))
      (PrimeFactorUnimodality.primesBelow (PrimeFactorUnimodality.primeAt i)) r)
    (hj : 3 < localPrimeRatio (fun p => 1 / (p : Rat)) r j) :
    3 < localPrimeRatio (fun p => 1 / (p : Rat)) r i := by
  exact hj.trans_le (localPrimeRatio_antitone_from _
    ordinaryEta_prime_probabilities r i j hr hij hden).2

end
end PrimeFactorOscillations

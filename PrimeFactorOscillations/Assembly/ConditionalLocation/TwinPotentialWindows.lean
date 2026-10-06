/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.ConditionalLocation.LastTwinTransfer

/-!
# Twin Potential Windows

Maintained implementation of the conditional last-ascent location argument.
The arithmetic coverage assumptions remain explicit; no conjecture is an axiom.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations

/-- Every prime in the indicated window satisfies both exact twin criteria. -/
theorem both_twin_potential_on_window (b : Real) (hb : 0 < b)
    (hb3 : b < (1 : Real) / 3) :
    exists K : Nat, 4 <= K /\ forall k : Nat, K <= k ->
      8 <= b * (k : Real) /\
      forall i : Nat,
        Nat.ceil (Real.exp (Real.exp (b * k))) <= PrimeFactorUnimodality.primeAt i ->
        PrimeFactorUnimodality.primeAt i <= 4 * Nat.ceil (Real.exp (Real.exp (b * k))) ->
        ordinaryTwinPotential k i /\ genericTwinPotential k i := by
  choose K hK using both_ratios_eventually_in_additive_band 3 b
    (by norm_num) hb (by linarith)
  choose K8 hK8 using exists_nat_gt ((8 : Real) / b)
  refine Exists.intro (max K K8) (And.intro (hK.1.trans (le_max_left _ _)) ?_)
  intro k hk
  have hk4 : 4 <= k := hK.1.trans ((le_max_left _ _).trans hk)
  have hkk : (K8 : Real) <= k := by exact_mod_cast (le_max_right K K8).trans hk
  have ht : 8 <= b * (k : Real) := by
    have h := mul_lt_mul_of_pos_right (hK8.trans_le hkk) hb
    have hc : ((8 : Real) / b) * b = 8 := by field_simp [ne_of_gt hb]
    rw [hc] at h
    linarith only [h]
  refine And.intro ht ?_
  intro i hlo hhi
  have hpLower : Real.exp (Real.exp (b * k)) <=
      (PrimeFactorUnimodality.primeAt i : Real) :=
    (Nat.le_ceil _).trans (by exact_mod_cast hlo)
  have hE : (3 : Real) < Real.exp (Real.exp (b * k)) := by
    linarith [Real.add_one_le_exp (b * (k : Real)),
      Real.add_one_le_exp (Real.exp (b * (k : Real)))]
  have hpgt : 2 < PrimeFactorUnimodality.primeAt i := by
    exact_mod_cast (show (2 : Real) < PrimeFactorUnimodality.primeAt i by linarith)
  have hband := Real.ceil_double_exp_prime_prefix_additive_band ht hlo hhi
  have hr := hK.2 k ((le_max_left _ _).trans hk)
    (PrimeFactorUnimodality.primeAt i - 1) (by omega) hband.1 hband.2
  rw [Nat.sub_add_cancel (show 1 <= PrimeFactorUnimodality.primeAt i by omega)] at hr
  have hsub : k - 1 - 1 = k - 2 := by omega
  have hG : 0 < finiteLocalMass genericOddEta
      (PrimeFactorUnimodality.primesBelow (PrimeFactorUnimodality.primeAt i)) (k - 1) :=
    genericOdd_prefix_mass_pos _ (k - 1) hr.2.2.2.2.1
  have hO : 0 < finiteLocalMass (fun q => 1 / (q : Rat))
      (PrimeFactorUnimodality.primesBelow (PrimeFactorUnimodality.primeAt i)) (k - 1) := by
    apply local_mass_pos _ _ ?_ _ hr.2.2.2.2.2
    intro q hq
    have hprime := (PrimeFactorUnimodality.primesBelow_entries _ q hq).1
    refine And.intro (div_pos (by norm_num) ?_) (ordinaryEta_prime_probabilities q hprime).2
    exact_mod_cast hprime.pos
  have hRG : (3 : Rat) < localPrimeRatio genericOddEta (k - 1) i := by
    unfold localPrimeRatio
    rw [hsub]
    exact_mod_cast hr.1
  have hRO : (3 : Rat) < localPrimeRatio (fun q => 1 / (q : Rat)) (k - 1) i := by
    rw [ordinary_localPrimeRatio_eq]
    exact_mod_cast hr.2.2.1
  exact And.intro (And.intro hpgt (And.intro hO hRO))
    (And.intro hpgt (And.intro hG
      ((genericTwinThreshold_le_three _ hpgt).trans_lt hRG)))

/-- Concrete cutoff growth, independent of any hypothesis about twin primes. -/
theorem both_twin_cutoffs_eventually_large (b : Real) (hb : 0 < b)
    (hb3 : b < (1 : Real) / 3) :
    exists K : Nat, 4 <= K /\ forall k : Nat, K <= k ->
      Real.exp (Real.exp (b * k)) <=
        (PrimeFactorUnimodality.primeAt (ordinaryTwinCutoffIndex k) : Real) /\
      Real.exp (Real.exp (b * k)) <=
        (PrimeFactorUnimodality.primeAt (genericTwinCutoffIndex k) : Real) := by
  choose Ks hs using both_twin_potential_seed b hb hb3
  choose Kc hc using both_twin_cutoff_eventually_spec
  refine Exists.intro (max Ks Kc) (And.intro (hs.1.trans (le_max_left _ _)) ?_)
  intro k hk
  choose i hi using hs.2 k ((le_max_left _ _).trans hk)
  have hcut := hc.2 k ((le_max_right _ _).trans hk)
  have hbase : Real.exp (Real.exp (b * k)) <= (PrimeFactorUnimodality.primeAt i : Real) :=
    (Nat.le_ceil _).trans (by exact_mod_cast hi.1)
  constructor
  next =>
    exact hbase.trans (by exact_mod_cast
      PrimeFactorUnimodality.primeAt_strictMono.monotone (hcut.1.2 i hi.2.2.1))
  next =>
    exact hbase.trans (by exact_mod_cast
      PrimeFactorUnimodality.primeAt_strictMono.monotone (hcut.2.2 i hi.2.2.2))

theorem isTwinStep_of_prime_add_two (i : Nat)
    (hp : 2 < PrimeFactorUnimodality.primeAt i)
    (hp2 : Nat.Prime (PrimeFactorUnimodality.primeAt i + 2)) : IsTwinStep i := by
  have hlo := primeAt_gap_ge_two i hp
  have hhi : PrimeFactorUnimodality.primeAt (i + 1) <= PrimeFactorUnimodality.primeAt i + 2 := by
    by_contra hn
    have h := Nat.le_nth_of_lt_nth_succ (Nat.lt_of_not_ge hn) hp2
    change PrimeFactorUnimodality.primeAt i + 2 <= PrimeFactorUnimodality.primeAt i at h
    omega
  exact le_antisymm hhi hlo

end PrimeFactorOscillations

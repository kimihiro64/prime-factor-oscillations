/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.NumberTheory.Bertrand
import Mathlib.Order.Lattice.Nat
import PrimeFactorOscillations.Assembly.ConditionalLocation.TwinCutoffSteps
import PrimeFactorOscillations.Mathlib.Analysis.SpecialFunctions.Exp.CeilDoubleExpAdditive
import PrimeFactorOscillations.Proof.Lower.AdditiveRatios
import PrimeFactorOscillations.Proof.Upper.GeneralScaleRatios

/-!
# Twin Cutoff Existence

Maintained implementation of the conditional last-ascent location argument.
The arithmetic coverage assumptions remain explicit; no conjecture is an axiom.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations

noncomputable section

def ordinaryTwinPotential (k i : Nat) : Prop :=
  2 < PrimeFactorUnimodality.primeAt i /\
  0 < finiteLocalMass (fun p => 1 / (p : Rat))
    (PrimeFactorUnimodality.primesBelow (PrimeFactorUnimodality.primeAt i)) (k - 1) /\
  3 < localPrimeRatio (fun p => 1 / (p : Rat)) (k - 1) i

def genericTwinPotential (k i : Nat) : Prop :=
  2 < PrimeFactorUnimodality.primeAt i /\
  0 < finiteLocalMass genericOddEta
    (PrimeFactorUnimodality.primesBelow (PrimeFactorUnimodality.primeAt i)) (k - 1) /\
  genericTwinThreshold (PrimeFactorUnimodality.primeAt i) <
    localPrimeRatio genericOddEta (k - 1) i

def ordinaryTwinCutoffIndex (k : Nat) : Nat := sSup {i | ordinaryTwinPotential k i}
def genericTwinCutoffIndex (k : Nat) : Nat := sSup {i | genericTwinPotential k i}

theorem ordinary_localPrimeRatio_eq (r i : Nat) :
    localPrimeRatio (fun p => 1 / (p : Rat)) r i =
      PrimeFactorUnimodality.densityRatio
        (PrimeFactorUnimodality.primesBelow (PrimeFactorUnimodality.primeAt i)) r := by
  have hp : forall p, List.Mem p (PrimeFactorUnimodality.primesBelow
      (PrimeFactorUnimodality.primeAt i)) -> 1 <= p := by
    intro p h
    exact (PrimeFactorUnimodality.primesBelow_entries _ _ h).1.one_lt.le
  unfold localPrimeRatio PrimeFactorUnimodality.densityRatio
  rw [reciprocal_localMass_eq_finiteDensity _ hp, reciprocal_localMass_eq_finiteDensity _ hp]

theorem genericTwinThreshold_le_three (p : Nat) (hp : 2 < p) :
    genericTwinThreshold p <= 3 := by
  have hpR : (2 : Rat) < p := by exact_mod_cast hp
  have h := div_nonneg (show (0 : Rat) <= 2 by norm_num)
    (mul_nonneg (show (0 : Rat) <= p by positivity) (show (0 : Rat) <= p - 2 by linarith))
  unfold genericTwinThreshold
  linarith only [h]

/-- Ordinary prime existence, not a twin-prime hypothesis, puts both potential
cutoffs beyond every fixed scale below one third. -/
theorem both_twin_potential_seed (b : Real) (hb : 0 < b) (hb3 : b < (1 : Real) / 3) :
    exists K : Nat, 4 <= K /\ forall k : Nat, K <= k ->
      exists i : Nat,
        Nat.ceil (Real.exp (Real.exp (b * k))) <= PrimeFactorUnimodality.primeAt i /\
        PrimeFactorUnimodality.primeAt i <= 2 * Nat.ceil (Real.exp (Real.exp (b * k))) /\
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
  let N := Nat.ceil (Real.exp (Real.exp (b * k)))
  have hNpos : 0 < N := Nat.ceil_pos.mpr (Real.exp_pos _)
  choose p hp using Nat.exists_prime_lt_and_le_two_mul N (Nat.ne_of_gt hNpos)
  let i := Nat.count Nat.Prime p
  have hi : PrimeFactorUnimodality.primeAt i = p := Nat.nth_count hp.1
  have hpLower : Real.exp (Real.exp (b * k)) <= (p : Real) :=
    (Nat.le_ceil _).trans (by exact_mod_cast hp.2.1.le)
  have hE : (3 : Real) < Real.exp (Real.exp (b * k)) := by
    linarith [Real.add_one_le_exp (b * (k : Real)),
      Real.add_one_le_exp (Real.exp (b * (k : Real)))]
  have hpgt : 2 < p := by exact_mod_cast (show (2 : Real) < p by linarith)
  have hband := Real.ceil_double_exp_prime_prefix_additive_band ht hp.2.1.le
    (show p <= 4 * N by omega)
  have hr := hK.2 k ((le_max_left _ _).trans hk) (p - 1) (by omega) hband.1 hband.2
  rw [Nat.sub_add_cancel (show 1 <= p by omega)] at hr
  have hsub : k - 1 - 1 = k - 2 := by omega
  have hOG : 0 < finiteLocalMass genericOddEta (PrimeFactorUnimodality.primesBelow p)
      (k - 1) := genericOdd_prefix_mass_pos p (k - 1) hr.2.2.2.2.1
  have hOO : 0 < finiteLocalMass (fun q => 1 / (q : Rat))
      (PrimeFactorUnimodality.primesBelow p) (k - 1) := by
    apply local_mass_pos _ _ ?_ _ hr.2.2.2.2.2
    intro q hq
    have hprime := (PrimeFactorUnimodality.primesBelow_entries p q hq).1
    refine And.intro (div_pos (by norm_num) ?_) (ordinaryEta_prime_probabilities q hprime).2
    exact_mod_cast hprime.pos
  have hRG : (3 : Rat) < localPrimeRatio genericOddEta (k - 1) i := by
    unfold localPrimeRatio
    rw [hi, hsub]
    exact_mod_cast hr.1
  have hRO : (3 : Rat) < localPrimeRatio (fun q => 1 / (q : Rat)) (k - 1) i := by
    rw [ordinary_localPrimeRatio_eq, hi]
    exact_mod_cast hr.2.2.1
  refine Exists.intro i (And.intro (by simpa only [hi] using hp.2.1.le)
    (And.intro (by simpa only [hi] using hp.2.2) (And.intro ?_ ?_)))
  next =>
    exact And.intro (by simpa only [hi] using hpgt)
      (And.intro (by simpa only [hi] using hOO) hRO)
  next =>
    exact And.intro (by simpa only [hi] using hpgt)
      (And.intro (by simpa only [hi] using hOG)
        ((genericTwinThreshold_le_three _ (by simpa only [hi] using hpgt)).trans_lt hRG))

end
end PrimeFactorOscillations

/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.ConditionalLocation.TwinCountAsymptoticBridge

/-!
# Hypothetical ascent cutoffs for an arbitrary fixed gap

Supported hypothetical gap-H steps have attained finite cutoffs at all
sufficiently large ranks. Their lower locations use ordinary prime existence,
not occurrence of the specified gap.
-/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace PrimeFactorOscillations
open Filter

def ordinaryGapPotential (H k i : Nat) : Prop :=
  2 < PrimeFactorUnimodality.primeAt i /\
  0 < finiteLocalMass (fun p => 1 / (p : Rat))
    (PrimeFactorUnimodality.primesBelow (PrimeFactorUnimodality.primeAt i)) (k - 1) /\
  (H : Rat) + 1 < localPrimeRatio (fun p => 1 / (p : Rat)) (k - 1) i

def ordinaryGapCutoffIndex (H k : Nat) : Nat :=
  sSup {i | ordinaryGapPotential H k i}

theorem ordinary_gap_potential_seed (H : Nat) (b : Real)
    (hb : 0 < b) (hmargin : ((H : Real) + 1) * b < 1) :
    exists K : Nat, 4 <= K /\ forall k : Nat, K <= k ->
      exists i : Nat,
        Nat.ceil (Real.exp (Real.exp (b * k))) <= PrimeFactorUnimodality.primeAt i /\
        PrimeFactorUnimodality.primeAt i <= 2 * Nat.ceil (Real.exp (Real.exp (b * k))) /\
        ordinaryGapPotential H k i := by
  choose K hK using both_ratios_eventually_in_additive_band ((H : Real) + 1) b
    (by positivity) hb hmargin
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
  have hOO : 0 < finiteLocalMass (fun q => 1 / (q : Rat))
      (PrimeFactorUnimodality.primesBelow p) (k - 1) := by
    apply local_mass_pos _ _ ?_ _ hr.2.2.2.2.2
    intro q hq
    have hprime := (PrimeFactorUnimodality.primesBelow_entries p q hq).1
    refine And.intro (div_pos (by norm_num) ?_) (ordinaryEta_prime_probabilities q hprime).2
    exact_mod_cast hprime.pos
  have hRO : (H : Rat) + 1 < localPrimeRatio (fun q => 1 / (q : Rat)) (k - 1) i := by
    rw [ordinary_localPrimeRatio_eq, hi]
    exact_mod_cast hr.2.2.1
  refine Exists.intro i (And.intro (by simpa only [hi] using hp.2.1.le)
    (And.intro (by simpa only [hi] using hp.2.2) ?_))
  exact And.intro (by simpa only [hi] using hpgt)
    (And.intro (by simpa only [hi] using hOO) hRO)

theorem ordinary_gap_potential_eventually_bddAbove (H : Nat) (hH : 2 <= H) :
    Filter.Eventually (fun k : Nat => BddAbove {i | ordinaryGapPotential H k i}) atTop := by
  choose K hK using both_twin_potential_eventually_bddAbove
  filter_upwards [eventually_ge_atTop K] with k hk
  apply (hK.2 k hk).1.mono
  intro i hi
  refine And.intro hi.1 (And.intro hi.2.1 ?_)
  have hs : (3 : Rat) <= (H : Rat) + 1 := by exact_mod_cast (show 3 <= H + 1 by omega)
  exact hs.trans_lt hi.2.2

theorem ordinary_gap_cutoff_eventually_spec (H : Nat) (hH : 2 <= H) :
    Filter.Eventually (fun k : Nat =>
      ordinaryGapPotential H k (ordinaryGapCutoffIndex H k) /\
      forall i : Nat, ordinaryGapPotential H k i -> i <= ordinaryGapCutoffIndex H k) atTop := by
  let b : Real := 1 / (2 * ((H : Real) + 1))
  have hb : 0 < b := by dsimp [b]; positivity
  have hmargin : ((H : Real) + 1) * b < 1 := by
    dsimp [b]
    have hs : Not ((H : Real) + 1 = 0) := by positivity
    field_simp
    <;> linarith
  choose K hK using ordinary_gap_potential_seed H b hb hmargin
  filter_upwards [eventually_ge_atTop K, ordinary_gap_potential_eventually_bddAbove H hH]
    with k hk hbound
  choose i hi using hK.2 k hk
  have hne : Set.Nonempty {i | ordinaryGapPotential H k i} := Exists.intro i hi.2.2
  exact And.intro (Nat.sSup_mem hne hbound) (fun j hj => le_csSup hbound hj)

theorem ordinary_gap_cutoff_eventually_large (H : Nat) (hH : 2 <= H)
    (b : Real) (hb : 0 < b) (hmargin : ((H : Real) + 1) * b < 1) :
    Filter.Eventually (fun k : Nat =>
      Real.exp (Real.exp (b * k)) <=
        (PrimeFactorUnimodality.primeAt (ordinaryGapCutoffIndex H k) : Real)) atTop := by
  choose K hK using ordinary_gap_potential_seed H b hb hmargin
  filter_upwards [eventually_ge_atTop K, ordinary_gap_cutoff_eventually_spec H hH]
    with k hk hspec
  choose i hi using hK.2 k hk
  have hindex := hspec.2 i hi.2.2
  have hprime := PrimeFactorUnimodality.primeAt_strictMono.monotone hindex
  exact (Nat.le_ceil _).trans (by exact_mod_cast hi.1.trans hprime)

theorem tendsto_ordinaryGapCutoffPrime (H : Nat) (hH : 2 <= H) :
    Tendsto (fun k : Nat =>
      (PrimeFactorUnimodality.primeAt (ordinaryGapCutoffIndex H k) : Real)) atTop atTop := by
  let b : Real := 1 / (2 * ((H : Real) + 1))
  have hb : 0 < b := by dsimp [b]; positivity
  have hm : ((H : Real) + 1) * b < 1 := by
    dsimp [b]
    have hs : Not ((H : Real) + 1 = 0) := by positivity
    field_simp
    <;> linarith
  have hGrowth : Tendsto (fun k : Nat => Real.exp (Real.exp (b * k))) atTop atTop :=
    Real.tendsto_exp_atTop.comp (Real.tendsto_exp_atTop.comp
      ((tendsto_natCast_atTop_atTop : Tendsto (fun k : Nat => (k : Real)) atTop atTop).const_mul_atTop hb))
  exact tendsto_atTop_mono' atTop (ordinary_gap_cutoff_eventually_large H hH b hb hm) hGrowth

end PrimeFactorOscillations

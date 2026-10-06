/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.ConditionalLocation.GeneralGapCutoff
import PrimeFactorOscillations.Helpers.GapCoverageBefore

/-!
# Actual ascents below hypothetical gap cutoffs

The exact gap criterion and attained cutoff bound the last actual ascent.
A supported seed is constructed below half of the cutoff.
-/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace PrimeFactorOscillations
open Filter
open PrimeFactorUnimodality

theorem ordinary_ascent_iff_gap (k i : Nat) (hk : 2 <= k)
    (hden : 0 < finiteLocalMass (fun p => 1 / (p : Rat))
      (primesBelow (primeAt i)) (k - 1)) :
    ordinaryDensity k i < ordinaryDensity k (i + 1) <->
      (primeGap i : Rat) + 1 < localPrimeRatio (fun p => 1 / (p : Rat)) (k - 1) i := by
  have hp : (0 : Rat) < primeAt i := by exact_mod_cast (prime_primeAt i).pos
  have hq : (0 : Rat) < primeAt (i + 1) := by exact_mod_cast (prime_primeAt (i + 1)).pos
  rw [ordinaryDensity_eq_localRankDensity, ordinaryDensity_eq_localRankDensity,
    localRankDensity_step_gt_iff _ k i hk (div_pos (by norm_num) hp)
      (div_pos (by norm_num) hq) hden]
  simp only [one_div_one_div, primeGap,
    Nat.cast_sub (primeAt_strictMono.monotone (Nat.le_succ i))]

/-- An actual gap-H step below the attained hypothetical cutoff supplies
a genuine ascent; all actual ascents are below that same cutoff. -/
theorem last_ascent_bracket_of_gap_cutoff (H k C t j : Nat)
    (hk : 2 <= k)
    (hcut : ordinaryGapPotential H k C /\
      forall i : Nat, ordinaryGapPotential H k i -> i <= C)
    (htj : t <= j) (hjC : j <= C)
    (hsupport : 0 < finiteLocalMass (fun p => 1 / (p : Rat))
      (primesBelow (primeAt t)) (k - 1))
    (hgap : primeGap j = H)
    (hmin : forall i : Nat, C < i -> H <= primeGap i) :
    ordinaryDensity k j < ordinaryDensity k (j + 1) /\
    IsGreatest {i | ordinaryDensity k i < ordinaryDensity k (i + 1)}
      (sSup {i | ordinaryDensity k i < ordinaryDensity k (i + 1)}) /\
    primeAt j <= lastAscentPrime (ordinaryDensity k) /\
    lastAscentPrime (ordinaryDensity k) <= primeAt C := by
  have hjden := (localPrimeRatio_antitone_from _ ordinaryEta_prime_probabilities
    (k - 1) t j (by omega) htj hsupport).1
  have hjratio := (localPrimeRatio_antitone_from _ ordinaryEta_prime_probabilities
    (k - 1) j C (by omega) hjC hjden).2
  have hjascent : ordinaryDensity k j < ordinaryDensity k (j + 1) := by
    apply (ordinary_ascent_iff_gap k j hk hjden).mpr
    rw [hgap]
    exact hcut.1.2.2.trans_le hjratio
  have hbound : forall i : Nat, ordinaryDensity k i < ordinaryDensity k (i + 1) -> i <= C := by
    intro i hi
    by_contra h
    have hCi : C < i := Nat.lt_of_not_ge h
    have hiden := (localPrimeRatio_antitone_from _ ordinaryEta_prime_probabilities
      (k - 1) C i (by omega) hCi.le hcut.1.2.1).1
    have hri := (ordinary_ascent_iff_gap k i hk hiden).mp hi
    have hHri : (H : Rat) + 1 < localPrimeRatio (fun p => 1 / (p : Rat)) (k - 1) i :=
      (show (H : Rat) + 1 <= (primeGap i : Rat) + 1 by exact_mod_cast Nat.add_le_add_right (hmin i hCi) 1).trans_lt hri
    have hpi : 2 < primeAt i := hcut.1.1.trans_le (primeAt_strictMono.monotone hCi.le)
    exact not_le_of_gt hCi (hcut.2 i (And.intro hpi (And.intro hiden hHri)))
  have hb : BddAbove {i | ordinaryDensity k i < ordinaryDensity k (i + 1)} :=
    Exists.intro C hbound
  have hne : Set.Nonempty {i | ordinaryDensity k i < ordinaryDensity k (i + 1)} :=
    Exists.intro j hjascent
  have hs := Nat.sSup_mem hne hb
  refine And.intro hjascent (And.intro (And.intro hs (fun i hi => le_csSup hb hi))
    (And.intro ?_ ?_))
  . exact primeAt_strictMono.monotone (le_csSup hb hjascent)
  . exact primeAt_strictMono.monotone (hbound _ hs)

theorem four_ceil_double_exp_le_double_exp_double (t : Real) (ht : 3 <= t) :
    4 * (Nat.ceil (Real.exp (Real.exp t)) : Real) <= Real.exp (Real.exp (2 * t)) := by
  have hw : 4 <= Real.exp t := by linarith [Real.add_one_le_exp t]
  have hsq : Real.exp t + 8 <= (Real.exp t) ^ (2 : Nat) := by nlinarith
  have hE : 1 <= Real.exp (Real.exp t) := by linarith [Real.add_one_le_exp (Real.exp t)]
  have hceil : (Nat.ceil (Real.exp (Real.exp t)) : Real) <=
      2 * Real.exp (Real.exp t) := by
    have h := Nat.ceil_lt_add_one (Real.exp_nonneg (Real.exp t))
    linarith
  have h8 : 9 <= Real.exp (8 : Real) := by linarith [Real.add_one_le_exp (8 : Real)]
  have hmul := mul_le_mul_of_nonneg_left h8 (Real.exp_nonneg (Real.exp t))
  have hstep := Real.exp_le_exp.mpr hsq
  rw [Real.exp_add] at hstep
  have hdouble : Real.exp (2 * t) = (Real.exp t) ^ (2 : Nat) := by
    rw [show 2 * t = t + t by ring, Real.exp_add]
    ring
  rw [hdouble]
  nlinarith

theorem eventually_gap_cutoff_seed_below_half (H : Nat) (hH : 2 <= H) :
    Filter.Eventually (fun k : Nat => exists t : Nat,
      2 * primeAt t <= primeAt (ordinaryGapCutoffIndex H k) /\
      ordinaryGapPotential H k t) atTop := by
  let b : Real := 1 / (4 * ((H : Real) + 1))
  have hb : 0 < b := by dsimp [b]; positivity
  have hm : ((H : Real) + 1) * (2 * b) < 1 := by
    dsimp [b]
    have hs : Not ((H : Real) + 1 = 0) := by positivity
    field_simp
    <;> linarith
  have hm1 : ((H : Real) + 1) * b < 1 := by nlinarith
  choose K hK using ordinary_gap_potential_seed H b hb hm1
  have hlarge := ordinary_gap_cutoff_eventually_large H hH (2 * b) (by positivity) hm
  have ht : Filter.Eventually (fun k : Nat => 3 <= b * (k : Real)) atTop :=
    ((tendsto_natCast_atTop_atTop : Tendsto (fun k : Nat => (k : Real)) atTop atTop).const_mul_atTop hb).eventually (eventually_ge_atTop 3)
  filter_upwards [eventually_ge_atTop K, hlarge, ht] with k hk hV ht
  choose t htt using hK.2 k hk
  have hE := four_ceil_double_exp_le_double_exp_double (b * k) ht
  have heq : 2 * (b * (k : Real)) = (2 * b) * k := by ring
  rw [heq] at hE
  have htBound : (primeAt t : Real) <=
      2 * (Nat.ceil (Real.exp (Real.exp (b * k))) : Real) := by exact_mod_cast htt.2.1
  have hReal : 2 * (primeAt t : Real) <= primeAt (ordinaryGapCutoffIndex H k) := by linarith
  exact Exists.intro t (And.intro (by exact_mod_cast hReal) htt.2.2)

end PrimeFactorOscillations

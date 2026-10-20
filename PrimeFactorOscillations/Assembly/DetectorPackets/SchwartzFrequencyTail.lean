/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Assembly.DetectorPackets.CoprimeSchwartzHigh

/-!
# SchwartzFrequencyTail

Maintained extraction of completed detector/packet proof components.
All original theorem hypotheses and retained proof bodies are preserved.
This module alone asserts no improved zero-free boundary.
-/

set_option autoImplicit false
set_option Elab.async false

/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described by LICENSE.
Authors: Prime Factor Oscillations contributors
-/


noncomputable section
open scoped BigOperators Classical

namespace PrimeFactorOscillations.SchwartzFrequencyTail

open CoprimeSchwartzPoisson CoprimeSchwartzCenter CoprimeSchwartzSplit
open CoprimeSchwartzDecay SchwartzIntegerPowerTail

theorem finite_int_power_tail (k : Nat) (hk : 2 <= k) :
    exists A : Real, 0 < A /\
      forall (y : Real) (E : Finset Int), 0 < y ->
      (forall n : Int, Membership.mem E n -> y < (n.natAbs : Real)) ->
      E.sum (fun n => 1 / (n.natAbs : Real) ^ k) <= A / y ^ (k - 1) := by
  choose A hA ha using finite_power_tail k hk
  refine Exists.intro (2 * A) (And.intro (by positivity) ?_)
  intro y E hy hE
  let w : Nat -> Real := fun n => 1 / (n : Real) ^ k
  have hpart (p : Int -> Prop) [DecidablePred p]
      (hi : Set.InjOn Int.natAbs (E.filter p)) :
      (E.filter p).sum (fun n => w n.natAbs) <= A / y ^ (k - 1) := by
    let G : Finset Nat := (E.filter p).image Int.natAbs
    have heq : G.sum w = (E.filter p).sum (fun n => w n.natAbs) :=
      Finset.sum_image hi
    rw [heq.symm]
    apply ha y G hy
    intro m hm
    choose n hn hnm using Finset.mem_image.mp hm
    rw [hnm.symm]
    exact hE n (Finset.mem_filter.mp hn).1
  have hp := hpart (fun n => 0 <= n) (by
    intro a ha b hb hab
    have ha0 := (Finset.mem_filter.mp ha).2
    have hb0 := (Finset.mem_filter.mp hb).2
    apply Or.elim (Int.natAbs_eq_natAbs_iff.mp hab)
    next => exact fun h => h
    next => intro h; omega)
  have hn := hpart (fun n => Not (0 <= n)) (by
    intro a ha b hb hab
    have ha0 := (Finset.mem_filter.mp ha).2
    have hb0 := (Finset.mem_filter.mp hb).2
    apply Or.elim (Int.natAbs_eq_natAbs_iff.mp hab)
    next => exact fun h => h
    next => intro h; omega)
  calc
    _ = (E.filter (fun n => 0 <= n)).sum (fun n => w n.natAbs) +
        (E.filter (fun n => Not (0 <= n))).sum (fun n => w n.natAbs) :=
      (Finset.sum_filter_add_sum_filter_not E (fun n => 0 <= n)
        (fun n => w n.natAbs)).symm
    _ <= A / y ^ (k - 1) + A / y ^ (k - 1) := add_le_add hp hn
    _ = _ := by ring

theorem natAbs_real (n : Int) : (n.natAbs : Real) = abs (n : Real) := by
  have h := congrArg (fun z : Int => (z : Real)) (Int.natCast_natAbs n)
  simpa only [Int.cast_natCast, Int.cast_abs] using h

theorem outside_frequencyRange (L : Nat) (n : Int)
    (hn : Not (Membership.mem (frequencyRange L) n)) :
    (L : Real) < (n.natAbs : Real) := by
  have hc : Not (-(L : Int) <= n /\ n <= (L : Int)) := by
    simpa only [frequencyRange, Finset.mem_Icc] using hn
  have hab : (L : Int) < abs n := by
    by_cases hn0 : 0 <= n
    next => rw [abs_of_nonneg hn0]; omega
    next => rw [abs_of_neg (lt_of_not_ge hn0)]; omega
  rw [<- (Int.natCast_natAbs n)] at hab
  exact_mod_cast hab

theorem frequencyTail_norm_bound (f : SchwartzMap Real Complex)
    (k : Nat) (hk : 2 <= k) :
    exists C : Real, 0 < C /\
      forall (L : Nat) (a : Real), 1 <= L -> 0 < a ->
      norm (frequencyTail L f a) <= C / (a ^ k * (L : Real) ^ (k - 1)) := by
  choose S hS hs using global_decay f k
  choose A hA ha using finite_int_power_tail k hk
  refine Exists.intro (S * A) (And.intro (mul_pos hS hA) ?_)
  intro L a hL hapos
  have hLR : (0 : Real) < (L : Real) := by exact_mod_cast (show 0 < L by omega)
  let g : Int -> Complex := fun n =>
    if Membership.mem (frequencyRange L) n then 0 else f ((n : Real) * a)
  have hgdom (n : Int) : norm (g n) <= norm (f ((n : Real) * a)) := by
    dsimp only [g]
    split_ifs
    next => simpa only [norm_zero] using norm_nonneg (f ((n : Real) * a))
    next => exact le_refl _
  have hgs : Summable (fun n : Int => norm (g n)) :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) hgdom
      (by simpa only [mul_comm a] using
        (scaled_samples_summable a (ne_of_gt hapos) f).norm)
  have hrow (n : Int) (hn : Not (Membership.mem (frequencyRange L) n)) :
      norm (f ((n : Real) * a)) <=
      (S / a ^ k) * (1 / (n.natAbs : Real) ^ k) := by
    have hnL := outside_frequencyRange L n hn
    have hnpos : (0 : Real) < (n.natAbs : Real) := lt_trans hLR hnL
    apply le_of_mul_le_mul_left (a := (n.natAbs : Real) ^ k * a ^ k) ?_
      (mul_pos (pow_pos hnpos _) (pow_pos hapos _))
    calc
      _ = abs ((n : Real) * a) ^ k * norm (f ((n : Real) * a)) := by
        rw [abs_mul, abs_of_pos hapos, mul_pow, natAbs_real]
      _ <= S := hs _
      _ = _ := by field_simp
  have hfinite (E : Finset Int) :
      E.sum (fun n => norm (g n)) <=
        (S * A) / (a ^ k * (L : Real) ^ (k - 1)) := by
    let H : Finset Int := E.filter (fun n =>
      Not (Membership.mem (frequencyRange L) n))
    have heq : E.sum (fun n => norm (g n)) =
        H.sum (fun n => norm (f ((n : Real) * a))) := by
      dsimp only [H]
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro n hn
      dsimp only [g]
      by_cases hc : Membership.mem (frequencyRange L) n
      next => simp only [hc, if_pos, not_true_eq_false, if_false, norm_zero]
      next => simp only [hc, if_false, not_false_eq_true, if_true]
    have hcut := ha (L : Real) H hLR (fun n hn =>
      outside_frequencyRange L n (Finset.mem_filter.mp hn).2)
    calc
      _ = H.sum (fun n => norm (f ((n : Real) * a))) := heq
      _ <= H.sum (fun n => (S / a ^ k) *
          (1 / (n.natAbs : Real) ^ k)) := by
        apply Finset.sum_le_sum
        intro n hn
        exact hrow n (Finset.mem_filter.mp hn).2
      _ = (S / a ^ k) * H.sum (fun n => 1 / (n.natAbs : Real) ^ k) :=
        (Finset.mul_sum _ _ _).symm
      _ <= (S / a ^ k) * (A / (L : Real) ^ (k - 1)) :=
        mul_le_mul_of_nonneg_left hcut (by positivity)
      _ = _ := by ring
  exact (norm_tsum_le_tsum_norm hgs).trans
    (Real.tsum_le_of_sum_le (fun n => norm_nonneg _) hfinite)

end PrimeFactorOscillations.SchwartzFrequencyTail


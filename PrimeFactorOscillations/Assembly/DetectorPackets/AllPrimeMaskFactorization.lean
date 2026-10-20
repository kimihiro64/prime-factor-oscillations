/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import Mathlib.Tactic.FieldSimp
import PrimeFactorOscillations.Assembly.DetectorPackets.QuadraticRetainedBeta

/-!
# AllPrimeMaskFactorization

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

namespace PrimeFactorOscillations.AllPrimeMask

open QuadraticCoprimeMean QuadraticCarrierPacket QuadraticDivisorMean
open QuadraticMainTermCancellation QuadraticPrincipalBoundary
open QuadraticBoundaryMean IntegerQuadraticPrefix

def density (G : Finset Nat) : Real :=
  G.prod (fun p => 1 - 1 / (p : Real))

def amplifier (G : Finset Nat) (n : Nat) : Real :=
  G.prod (fun p => if Dvd.dvd p n then (p : Real) / ((p : Real) - 1) else 1)

def weight (G : Finset Nat) (n m : Nat) : Real :=
  G.prod (fun p => if Or (Dvd.dvd p n) (Dvd.dvd p m) then 1
    else 1 - 1 / (p : Real))

theorem density_pos (G : Finset Nat)
    (hG : forall p, Membership.mem G p -> 2 <= p) : 0 < density G := by
  apply Finset.prod_pos
  intro p hp
  have hpr : (1 : Real) < (p : Real) := by exact_mod_cast hG p hp
  have hp0 : (0 : Real) < (p : Real) := by linarith
  exact sub_pos.mpr ((div_lt_one hp0).mpr hpr)

theorem local_factorization (p n m : Nat) (hp : 2 <= p)
    (hc : Nat.Coprime n m) :
    (if Or (Dvd.dvd p n) (Dvd.dvd p m) then (1 : Real)
      else 1 - 1 / (p : Real)) =
    (1 - 1 / (p : Real)) *
      (if Dvd.dvd p n then (p : Real) / ((p : Real) - 1) else 1) *
      (if Dvd.dvd p m then (p : Real) / ((p : Real) - 1) else 1) := by
  have hp0 : Not ((p : Real) = 0) := by exact_mod_cast (by omega : Not (p = 0))
  have hp1 : Not ((p : Real) - 1 = 0) := by
    have hpr : (1 : Real) < (p : Real) := by exact_mod_cast hp
    linarith
  by_cases hn : Dvd.dvd p n
  next =>
    have hm : Not (Dvd.dvd p m) := by
      intro hm
      have hd : Dvd.dvd p 1 := by
        have h := Nat.dvd_gcd hn hm
        rwa [hc.gcd_eq_one] at h
      have hle := Nat.le_of_dvd Nat.zero_lt_one hd
      omega
    simp only [hn, hm, true_or, if_true, if_false]
    field_simp
  next =>
    by_cases hm : Dvd.dvd p m
    next =>
      simp only [hn, hm, false_or, if_true, if_false]
      field_simp
    next =>
      simp only [hn, hm, or_self, if_false, mul_one]

theorem weight_factorization (G : Finset Nat) (n m : Nat)
    (hG : forall p, Membership.mem G p -> 2 <= p)
    (hc : Nat.Coprime n m) :
    weight G n m = density G * amplifier G n * amplifier G m := by
  unfold weight density amplifier
  calc
    _ = G.prod (fun p => (1 - 1 / (p : Real)) *
        (if Dvd.dvd p n then (p : Real) / ((p : Real) - 1) else 1) *
        (if Dvd.dvd p m then (p : Real) / ((p : Real) - 1) else 1)) := by
      apply Finset.prod_congr rfl
      intro p hp
      exact local_factorization p n m (hG p hp) hc
    _ = _ := by simp only [Finset.prod_mul_distrib]

def weightedForm (G S T : Finset Nat) (a b : Nat -> Complex) : Complex :=
  S.sum (fun n => T.sum (fun m => if Nat.Coprime n m then
    (weight G n m : Complex) * a n * b m else 0))

theorem weightedForm_factorization (G S T : Finset Nat)
    (a b : Nat -> Complex)
    (hG : forall p, Membership.mem G p -> 2 <= p) :
    weightedForm G S T a b =
      (density G : Complex) * coprimeForm S T
        (fun n => (amplifier G n : Complex) * a n)
        (fun m => (amplifier G m : Complex) * b m) := by
  unfold weightedForm coprimeForm
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  apply Finset.sum_congr rfl
  intro m hm
  by_cases hc : Nat.Coprime n m
  next =>
    rw [if_pos hc, if_pos hc, weight_factorization G n m hG hc]
    push_cast
    ring
  next => simp only [if_neg hc, mul_zero]

theorem normalized_weightedForm (G S T : Finset Nat)
    (a b : Nat -> Complex)
    (hG : forall p, Membership.mem G p -> 2 <= p) :
    weightedForm G S T a b / (density G : Complex) =
      coprimeForm S T
        (fun n => (amplifier G n : Complex) * a n)
        (fun m => (amplifier G m : Complex) * b m) := by
  have hd : Not ((density G : Complex) = 0) := by
    exact_mod_cast (ne_of_gt (density_pos G hG))
  rw [weightedForm_factorization G S T a b hG]
  field_simp

theorem amplifier_truncate (G : Finset Nat) (n N : Nat)
    (hn : 0 < n) (hN : n <= N) :
    amplifier G n = amplifier (G.filter (fun p => p <= N)) n := by
  unfold amplifier
  symm
  apply Finset.prod_subset (Finset.filter_subset _ _)
  intro p hp hnot
  have hlarge : Not (p <= N) := by
    intro h
    exact hnot (Finset.mem_filter.mpr (And.intro hp h))
  have hdiv : Not (Dvd.dvd p n) := by
    intro hd
    exact hlarge ((Nat.le_of_dvd hn hd).trans hN)
  rw [if_neg hdiv]

theorem amplifier_nonneg (G : Finset Nat) (n : Nat)
    (hG : forall p, Membership.mem G p -> 2 <= p) :
    0 <= amplifier G n := by
  apply Finset.prod_nonneg
  intro p hp
  split_ifs
  . apply div_nonneg (Nat.cast_nonneg _)
    have hpr : (2 : Real) <= (p : Real) := by exact_mod_cast hG p hp
    linarith
  . norm_num

theorem amplifier_le_divisor_card (G : Finset Nat) (n : Nat)
    (hn : 0 < n) (hG : forall p, Membership.mem G p -> Nat.Prime p) :
    amplifier G n <= (n.divisors.card : Real) := by
  let S := G.filter (fun p => Dvd.dvd p n)
  have hS : S <= n.primeFactors := by
    intro p hp
    have h := Finset.mem_filter.mp hp
    exact Nat.mem_primeFactors.mpr
      (And.intro (hG p h.1) (And.intro h.2 (Nat.ne_of_gt hn)))
  have hprime : forall p, Membership.mem S p -> Nat.Prime p :=
    fun p hp => hG p (Finset.mem_filter.mp hp).1
  have hprod : Dvd.dvd (subsetProduct S) n := by
    exact (Finset.prod_dvd_prod_of_subset S n.primeFactors id hS).trans
      (Nat.prod_primeFactors_dvd n)
  have hdiv : (subsetProduct S).divisors <= n.divisors := by
    intro d hd
    exact Nat.mem_divisors.mpr (And.intro
      ((Nat.mem_divisors.mp hd).1.trans hprod) (Nat.ne_of_gt hn))
  have hcard : S.powerset.card <= n.divisors.card :=
    (QuadraticCompensatedSubpower.powerset_card_le_divisors S hprime).trans
      (Finset.card_le_card hdiv)
  have heq : amplifier G n =
      S.prod (fun p => (p : Real) / ((p : Real) - 1)) := by
    simp only [amplifier, S, Finset.prod_filter]
  calc
    _ = S.prod (fun p => (p : Real) / ((p : Real) - 1)) := heq
    _ <= S.prod (fun _ => (2 : Real)) := by
      have hbound : forall T : Finset Nat,
          (forall p, Membership.mem T p -> Nat.Prime p) ->
          T.prod (fun p => (p : Real) / ((p : Real) - 1)) <=
            T.prod (fun _ => (2 : Real)) := by
        intro T
        induction T using Finset.induction_on with
        | empty => intro hT; simp
        | @insert p T hp ih =>
          intro hT
          have hpr : (2 : Real) <= (p : Real) := by
            exact_mod_cast (hT p (Finset.mem_insert_self _ _)).two_le
          have hq0 : 0 <= (p : Real) / ((p : Real) - 1) :=
            div_nonneg (Nat.cast_nonneg _) (by linarith)
          have hq2 : (p : Real) / ((p : Real) - 1) <= 2 := by
            have hd : Not ((p : Real) - 1 = 0) := by linarith
            have he : (p : Real) / ((p : Real) - 1) =
                1 + 1 / ((p : Real) - 1) := by
              field_simp
              ring
            have hr := one_div_le_one_div_of_le (by norm_num : (0 : Real) < 1)
              (by linarith : (1 : Real) <= (p : Real) - 1)
            rw [he]
            have hr2 : 1 / ((p : Real) - 1) <= 1 := by
              simpa only [one_div, inv_one] using hr
            linarith
          rw [Finset.prod_insert hp, Finset.prod_insert hp]
          exact mul_le_mul hq2
            (ih (fun q hq => hT q (Finset.mem_insert_of_mem hq)))
            (Finset.prod_nonneg (fun q hq => by
              apply div_nonneg (Nat.cast_nonneg _)
              have hqr : (2 : Real) <= (q : Real) := by
                exact_mod_cast (hT q (Finset.mem_insert_of_mem hq)).two_le
              linarith))
            (by norm_num)
      exact hbound S hprime
    _ = (S.powerset.card : Real) := by simp
    _ <= _ := Nat.cast_le.mpr hcard

theorem amplifier_mass_subpower (eps : Real) (heps : 0 < eps) :
    exists C : Real, 0 < C /\
      forall (G S : Finset Nat) (N e : Nat) (a : Nat -> Complex),
      (forall p, Membership.mem G p -> Nat.Prime p) ->
      (forall n, Membership.mem S n -> Membership.mem (columns N) n) ->
      maskedMass e S (fun n => (amplifier G n : Complex) * a n) <=
        C * (N : Real) ^ eps * maskedMass e S a := by
  choose A hA ha using divisor_card_subpower (eps / 2) (by linarith)
  refine Exists.intro (A ^ 2) (And.intro (sq_pos_of_pos hA) ?_)
  intro G S N e a hG hS
  unfold maskedMass
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro n hn
  have hb := columns_bounds N n (hS n hn)
  have hN : 0 < (N : Real) := by exact_mod_cast hb.1.trans_le hb.2
  have hAmp : amplifier G n <= A * (N : Real) ^ (eps / 2) := by
    calc
      _ <= (n.divisors.card : Real) := amplifier_le_divisor_card G n hb.1 hG
      _ <= A * (n : Real) ^ (eps / 2) := ha n hb.1
      _ <= _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (Nat.cast_nonneg n) (Nat.cast_le.mpr hb.2)
          (by linarith)) hA.le
  have hAmp0 := amplifier_nonneg G n (fun p hp => (hG p hp).two_le)
  have hpower : ((N : Real) ^ (eps / 2)) ^ 2 = (N : Real) ^ eps := by
    rw [sq, <- Real.rpow_add hN]
    congr 1
    ring
  have hSquare : (amplifier G n) ^ 2 <= A ^ 2 * (N : Real) ^ eps := by
    calc
      _ <= (A * (N : Real) ^ (eps / 2)) ^ 2 := by
        nlinarith [mul_self_le_mul_self hAmp0 hAmp]
      _ = _ := by rw [mul_pow, hpower]
  split_ifs
  . simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hAmp0, mul_pow]
    exact mul_le_mul_of_nonneg_right hSquare (sq_nonneg _)
  . simp only [mul_zero, le_refl]


end PrimeFactorOscillations.AllPrimeMask


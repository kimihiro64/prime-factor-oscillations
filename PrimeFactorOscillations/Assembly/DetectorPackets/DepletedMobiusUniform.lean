/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import Mathlib.Tactic.Linarith
import PrimeFactorOscillations.Assembly.DetectorPackets.DepletedMobiusBound

/-!
# DepletedMobiusUniform

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

namespace PrimeFactorOscillations.DepletedMobius

theorem euler_factor_pos {alpha : Real} (halpha : 0 < alpha)
    {p : Nat} (hp : Nat.Prime p) :
    0 < Inv.inv (1 - 1 / (p : Real) ^ alpha) := by
  have hlt := decayHom_prime_norm_lt halpha hp
  rw [Real.norm_eq_abs, abs_of_nonneg (decayHom_nonneg alpha p)] at hlt
  exact inv_pos.mpr (sub_pos.mpr hlt)

theorem euler_factor_uniform {alpha : Real} (halpha : 0 < alpha)
    {p : Nat} (hp : Nat.Prime p) :
    Inv.inv (1 - 1 / (p : Real) ^ alpha) <=
      Inv.inv (1 - (2 : Real) ^ (-alpha)) := by
  have h2 : 0 < 1 - (2 : Real) ^ (-alpha) :=
    sub_pos.mpr (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (neg_lt_zero.mpr halpha))
  have hpow : (p : Real) ^ (-alpha) <= (2 : Real) ^ (-alpha) :=
    Real.rpow_le_rpow_of_nonpos (by norm_num) (by exact_mod_cast hp.two_le) (by linarith)
  have hden : 1 - (2 : Real) ^ (-alpha) <= 1 - 1 / (p : Real) ^ alpha := by
    rw [one_div, <- Real.rpow_neg (Nat.cast_nonneg p) alpha]
    linarith
  simpa only [one_div] using one_div_le_one_div_of_le h2 hden

theorem finite_nat_product_rpow (S : Finset Nat) (eps : Real) :
    S.prod (fun p => (p : Real) ^ eps) = ((S.prod id : Nat) : Real) ^ eps := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert p S hp ih =>
    rw [Finset.prod_insert hp, Finset.prod_insert hp, Nat.cast_mul]
    change (p : Real) ^ eps * S.prod (fun q => (q : Real) ^ eps) =
      ((p : Real) * ((S.prod id : Nat) : Real)) ^ eps
    rw [Real.mul_rpow (Nat.cast_nonneg p) (Nat.cast_nonneg (S.prod id)), <- ih]

theorem finite_real_prod_mono {I : Type*} (S : Finset I) (f g : I -> Real) :
    (forall i, Membership.mem S i -> 0 <= f i) ->
    (forall i, Membership.mem S i -> f i <= g i) -> S.prod f <= S.prod g := by
  induction S using Finset.induction_on with
  | empty => intro _ _; simp
  | @insert i S hi ih =>
    intro hzero hle
    have hzS : forall j, Membership.mem S j -> 0 <= f j :=
      fun j hj => hzero j (Finset.mem_insert_of_mem hj)
    have hlS : forall j, Membership.mem S j -> f j <= g j :=
      fun j hj => hle j (Finset.mem_insert_of_mem hj)
    rw [Finset.prod_insert hi, Finset.prod_insert hi]
    exact mul_le_mul (hle i (Finset.mem_insert_self i S)) (ih hzS hlS)
      (Finset.prod_nonneg hzS)
      ((hzero i (Finset.mem_insert_self i S)).trans (hle i (Finset.mem_insert_self i S)))

theorem eulerMask_subpower (alpha eps : Real) (halpha : 0 < alpha) (heps : 0 < eps) :
    exists B : Real, 0 < B /\ forall h : Nat, Not (h = 0) ->
      eulerMask h alpha <= B * (h : Real) ^ eps := by
  let L := Inv.inv (1 - (2 : Real) ^ (-alpha))
  have hL : 0 < L := by
    apply inv_pos.mpr
    exact sub_pos.mpr
      (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (neg_lt_zero.mpr halpha))
  let K := L + 1
  have hK : 1 <= K := by dsimp only [K]; linarith
  have hKpos : 0 < K := by linarith
  choose A hA using exists_nat_gt (K ^ (1 / eps))
  have hthreshold (p : Nat) (hp : A <= p) : K <= (p : Real) ^ eps := by
    have hpa : (A : Real) <= (p : Real) := by exact_mod_cast hp
    have hh := Real.rpow_le_rpow (Real.rpow_nonneg hKpos.le (1 / eps))
      (hA.le.trans hpa) heps.le
    have he : (K ^ (1 / eps)) ^ eps = K := by
      rw [<- Real.rpow_mul hKpos.le]
      have hexp : (1 / eps) * eps = 1 := by field_simp
      rw [hexp, Real.rpow_one]
    rwa [he] at hh
  refine Exists.intro (K ^ A) (And.intro (pow_pos hKpos A) ?_)
  intro h hh
  let S := h.primeFactors
  let small := S.filter (fun p => p < A)
  have hsmall : small.card <= A := by
    have hs : forall p, Membership.mem small p -> Membership.mem (Finset.range A) p := by
      intro p hp
      exact Finset.mem_range.mpr (Finset.mem_filter.mp hp).2
    have hc := Finset.card_le_card hs
    simpa only [Finset.card_range] using hc
  have hpmono : Monotone (fun n : Nat => K ^ n) := by
    apply monotone_nat_of_le_succ
    intro n
    rw [pow_succ]
    calc
      _ = K ^ n * 1 := by ring
      _ <= _ := mul_le_mul_of_nonneg_left hK (pow_nonneg hKpos.le n)
  have hg : S.prod (fun p => if p < A then K else 1) = K ^ small.card := by
    rw [Finset.prod_ite]
    simp only [Finset.prod_const, one_pow, mul_one, small]
  have hprod : ((S.prod id : Nat) : Real) <= (h : Real) := by
    have hd := Nat.prod_primeFactors_dvd h
    have hb := Nat.le_of_dvd (Nat.pos_iff_ne_zero.mpr hh) hd
    exact_mod_cast hb
  calc
    eulerMask h alpha <= S.prod (fun p =>
        (if p < A then K else 1) * (p : Real) ^ eps) := by
      apply finite_real_prod_mono
      . intro p hp
        exact (euler_factor_pos halpha (Nat.mem_primeFactors.mp hp).1).le
      . intro p hp
        have hprime := (Nat.mem_primeFactors.mp hp).1
        have hf : Inv.inv (1 - 1 / (p : Real) ^ alpha) <= K :=
          (euler_factor_uniform halpha hprime).trans (by dsimp only [K]; linarith)
        by_cases hpa : p < A
        . rw [ite_eq_left hpa]
          exact hf.trans (by
            have hone : 1 <= (p : Real) ^ eps :=
              Real.one_le_rpow (by exact_mod_cast hprime.one_le) heps.le
            simpa only [mul_one] using mul_le_mul_of_nonneg_left hone hKpos.le)
        . rw [ite_eq_right hpa, one_mul]
          exact hf.trans (hthreshold p (Nat.le_of_not_gt hpa))
    _ = (K ^ small.card) * ((S.prod id : Nat) : Real) ^ eps := by
      rw [Finset.prod_mul_distrib, hg, finite_nat_product_rpow]
    _ <= (K ^ A) * (h : Real) ^ eps :=
      mul_le_mul (hpmono hsmall)
        (Real.rpow_le_rpow (Nat.cast_nonneg _) hprod heps.le)
        (Real.rpow_nonneg (Nat.cast_nonneg _) _) (pow_nonneg hKpos.le A)

theorem depleted_prefix_uniform {R : Type*} [NormedField R]
    (eta : Nat -> R) (heta : forall m n : Nat, eta (m * n) = eta m * eta n)
    (hnorm : forall n : Nat, norm (eta n) <= 1)
    (alpha eps C : Real) (halpha : 0 < alpha) (heps : 0 < eps) (hC : 0 <= C)
    (hbase : forall n : Nat, norm (mertensPrefix eta n) <= C * (n : Real) ^ alpha) :
    exists B : Real, 0 < B /\ forall h N : Nat, Not (h = 0) ->
      norm (depletedPrefix h eta N) <= C * B * (N : Real) ^ alpha * (h : Real) ^ eps := by
  choose B hB hb using eulerMask_subpower alpha eps halpha heps
  refine Exists.intro B (And.intro hB ?_)
  intro h N hh
  calc
    _ <= C * (N : Real) ^ alpha * eulerMask h alpha :=
      depleted_prefix_euler_bound h N hh eta heta hnorm alpha C halpha hC hbase
    _ <= C * (N : Real) ^ alpha * (B * (h : Real) ^ eps) :=
      mul_le_mul_of_nonneg_left (hb h hh) (by positivity)
    _ = _ := by ring

end PrimeFactorOscillations.DepletedMobius

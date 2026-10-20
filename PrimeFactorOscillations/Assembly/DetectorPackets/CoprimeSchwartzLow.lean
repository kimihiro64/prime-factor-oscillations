/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Assembly.DetectorPackets.CoprimeSchwartzDecay
import PrimeFactorOscillations.Assembly.DetectorPackets.CoprimeSchwartzMixed

/-!
# CoprimeSchwartzLow

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

namespace PrimeFactorOscillations.CoprimeSchwartzLow

open CoprimeSchwartzPoisson CoprimeSchwartzCenter CoprimeSchwartzSplit
open CoprimeSchwartzMixed CoprimeSchwartzDecay

theorem smallDivisors_card (q : Nat) (hq : 0 < q) (Y : Real) (hY : 0 <= Y) :
    ((smallDivisors q Y).card : Real) <= Y := by
  have hsub : smallDivisors q Y <= Finset.Ioc 0 (Nat.floor Y) := by
    intro d hd
    have h := Finset.mem_filter.mp hd
    have hdpos := Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp h.1).1 hq
    exact Finset.mem_Ioc.mpr (And.intro hdpos (Nat.le_floor h.2))
  have hcard : (smallDivisors q Y).card <= Nat.floor Y := by
    have h := Finset.card_le_card hsub
    simpa only [Nat.card_Ioc, Nat.sub_zero] using h
  exact (Nat.cast_le.mpr hcard).trans (Nat.floor_le hY)

theorem dualRow_norm_bound (f : SchwartzMap Real Complex) (k : Nat) (hk : 2 <= k) :
    exists C : Real, 0 < C /\
      forall (d : Nat) (X : Real), 0 < d -> 0 < X ->
      norm (dualRow f X d) <= C * ((d : Real) / X) ^ (k - 1) := by
  choose C hC hc using offZero_norm_bound (FourierTransform.fourier f) k hk
  refine Exists.intro C (And.intro hC ?_)
  intro d X hd hX
  have hdR : (0 : Real) < (d : Real) := by exact_mod_cast hd
  let t := X / (d : Real)
  have ht : 0 < t := div_pos hX hdR
  have hmu : norm (ArithmeticFunction.moebius d : Complex) <= 1 := by
    rw [Complex.norm_intCast]
    exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := d))
  have hkEq : k = (k - 1) + 1 := by omega
  have hpow : t ^ k = t ^ (k - 1) * t := by
    calc
      _ = t ^ ((k - 1) + 1) := congrArg (fun j : Nat => t ^ j) hkEq
      _ = _ := pow_succ _ _
  have hinv : (d : Real) / X = 1 / t := by
    dsimp only [t]
    field_simp
  have hInvPow : (1 / t) ^ (k - 1) = 1 / t ^ (k - 1) := by
    rw [div_pow, one_pow]
  calc
    _ = norm (ArithmeticFunction.moebius d : Complex) * t *
        norm (offZeroSum (FourierTransform.fourier f) t) := by
      simp only [t, dualRow, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (div_pos hX hdR)]
    _ <= 1 * t * (C / t ^ k) :=
      mul_le_mul (mul_le_mul_of_nonneg_right hmu ht.le) (hc t ht)
        (norm_nonneg _) (by positivity)
    _ = _ := by
      rw [one_mul, hinv, hpow, hInvPow]
      field_simp [ne_of_gt ht] <;> ring

theorem lowDual_norm_bound (f : SchwartzMap Real Complex) (k : Nat) (hk : 2 <= k) :
    exists C : Real, 0 < C /\
      forall (q : Nat) (X Y : Real), 0 < q -> 0 < X -> 0 < Y ->
      norm (lowDual q X Y f) <= C * X * (Y / X) ^ k := by
  choose C hC hc using dualRow_norm_bound f k hk
  refine Exists.intro C (And.intro hC ?_)
  intro q X Y hq hX hY
  have hterm (d : Nat) (hd : Membership.mem (smallDivisors q Y) d) :
      norm (dualRow f X d) <= C * (Y / X) ^ (k - 1) := by
    have h := Finset.mem_filter.mp hd
    have hdpos := Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp h.1).1 hq
    have hquot : (d : Real) / X <= Y / X :=
      div_le_div_of_nonneg_right h.2 hX.le
    have hp : forall j : Nat, ((d : Real) / X) ^ j <= (Y / X) ^ j := by
      intro j
      induction j with
      | zero => simp only [pow_zero, le_refl]
      | succ j hj =>
          rw [pow_succ, pow_succ]
          exact mul_le_mul hj hquot (by positivity) (by positivity)
    exact (hc d X hdpos hX).trans
      (mul_le_mul_of_nonneg_left (hp (k - 1)) hC.le)
  have hkEq : k = (k - 1) + 1 := by omega
  have hpow : (Y / X) ^ k = (Y / X) ^ (k - 1) * (Y / X) := by
    calc
      _ = (Y / X) ^ ((k - 1) + 1) := congrArg (fun j : Nat => (Y / X) ^ j) hkEq
      _ = _ := pow_succ _ _
  calc
    _ <= (smallDivisors q Y).sum (fun d => norm (dualRow f X d)) := norm_sum_le _ _
    _ <= (smallDivisors q Y).sum (fun _ => C * (Y / X) ^ (k - 1)) := by
      apply Finset.sum_le_sum
      exact hterm
    _ = ((smallDivisors q Y).card : Real) * (C * (Y / X) ^ (k - 1)) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
    _ <= Y * (C * (Y / X) ^ (k - 1)) :=
      mul_le_mul_of_nonneg_right (smallDivisors_card q hq Y hY.le) (by positivity)
    _ = _ := by
      rw [hpow]
      field_simp <;> ring

theorem lowDual_gain (f : SchwartzMap Real Complex) (k : Nat) (hk : 2 <= k) :
    exists C : Real, 0 < C /\
      forall (q : Nat) (X Y J : Real),
      0 < q -> 0 < X -> 0 < Y -> 0 < J -> Y * J <= X ->
      norm (lowDual q X Y f) <= C * X / J ^ k := by
  choose C hC hc using lowDual_norm_bound f k hk
  refine Exists.intro C (And.intro hC ?_)
  intro q X Y J hq hX hY hJ hYJ
  have hquot : Y / X <= 1 / J := by
    apply le_of_mul_le_mul_left (a := X * J) ?_ (mul_pos hX hJ)
    calc
      _ = Y * J := by field_simp
      _ <= X := hYJ
      _ = _ := by field_simp
  have hp : forall j : Nat, (Y / X) ^ j <= (1 / J) ^ j := by
    intro j
    induction j with
    | zero => simp only [pow_zero, le_refl]
    | succ j hj =>
        rw [pow_succ, pow_succ]
        exact mul_le_mul hj hquot (by positivity) (by positivity)
  calc
    _ <= C * X * (Y / X) ^ k := hc q X Y hq hX hY
    _ <= C * X * (1 / J) ^ k :=
      mul_le_mul_of_nonneg_left (hp k) (by positivity)
    _ = _ := by rw [div_pow, one_pow]; ring

end PrimeFactorOscillations.CoprimeSchwartzLow

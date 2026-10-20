/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Assembly.DetectorPackets.DepletedMobiusPhysical
import PrimeFactorOscillations.Assembly.DetectorPackets.DepletedMobiusUniform
import PrimeFactorOscillations.Assembly.DetectorPackets.WeightedDivisorConvolution

/-!
# SmoothMobiusDepletion

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

def smoothBase {R : Type*} [Ring R]
    (eta : Nat -> R) (W : Real -> R) (b y : Real) : R :=
  weightedBase eta (fun n => W ((n : Real) / y)) (Nat.floor (b * y))

def smoothDepleted {R : Type*} [Ring R]
    (h : Nat) (eta : Nat -> R) (W : Real -> R) (b y : Real) : R :=
  weightedDepleted h eta (fun n => W ((n : Real) / y)) (Nat.floor (b * y))

theorem window_vanishes_above {R : Type*} [Zero R] (W : Real -> R)
    (b y : Real) (hy : 0 < y) (hsup : forall t : Real, b < t -> W t = 0)
    (n : Nat) (hn : Nat.floor (b * y) < n) :
    W ((n : Real) / y) = 0 := by
  apply hsup
  calc
    b = (b * y) / y := by field_simp
    _ < (n : Real) / y := div_lt_div_of_pos_right (Nat.lt_of_floor_lt hn) hy

theorem weightedBase_eq_smooth {R : Type*} [Ring R]
    (eta : Nat -> R) (W : Real -> R) (b y : Real) (hy : 0 < y)
    (hsup : forall t : Real, b < t -> W t = 0)
    (N : Nat) (hN : Nat.floor (b * y) <= N) :
    weightedBase eta (fun n => W ((n : Real) / y)) N = smoothBase eta W b y := by
  unfold smoothBase weightedBase
  symm
  apply Finset.sum_subset
  . intro n hn
    have hn' := Finset.mem_Ioc.mp hn
    exact Finset.mem_Ioc.mpr (And.intro hn'.1 (hn'.2.trans hN))
  . intro n hn hnot
    have hnpos := (Finset.mem_Ioc.mp hn).1
    have hlt : Nat.floor (b * y) < n :=
      Nat.lt_of_not_ge (fun hnle =>
        hnot (Finset.mem_Ioc.mpr (And.intro hnpos hnle)))
    simp only [window_vanishes_above W b y hy hsup n hlt, mul_zero]

theorem smooth_depletion_identity {R : Type*} [CommRing R]
    (h : Nat) (eta : Nat -> R) (W : Real -> R)
    (heta : forall m n : Nat, eta (m * n) = eta m * eta n)
    (b y : Real) (hb : 0 <= b) (hy : 0 < y)
    (hsup : forall t : Real, b < t -> W t = 0) :
    smoothDepleted h eta W b y =
      (Finset.Ioc 0 (Nat.floor (b * y))).sum (fun d => if SupportedOn h d then
        eta d * smoothBase eta W b (y / (d : Real)) else 0) := by
  rw [smoothDepleted, weighted_depletion_separable h eta
    (fun n => W ((n : Real) / y)) heta (Nat.floor (b * y))
    (window_vanishes_above W b y hy hsup)]
  apply Finset.sum_congr rfl
  intro d hd
  have hdpos : 0 < d := (Finset.mem_Ioc.mp hd).1
  have hdreal : 0 < (d : Real) := by exact_mod_cast hdpos
  have hdone : (1 : Real) <= (d : Real) := by
    exact_mod_cast Nat.succ_le_of_lt hdpos
  have hcut : Nat.floor (b * (y / (d : Real))) <= Nat.floor (b * y) := by
    apply Nat.floor_mono
    rw [<- mul_div_assoc]
    exact div_le_self (mul_nonneg hb hy.le) hdone
  have hw : (fun m : Nat => W (((d * m : Nat) : Real) / y)) =
      (fun m : Nat => W ((m : Real) / (y / (d : Real)))) := by
    funext m
    congr 1
    simp only [Nat.cast_mul, div_div_eq_mul_div]
    ring
  rw [hw, weightedBase_eq_smooth eta W b (y / (d : Real))
    (div_pos hy hdreal) hsup (Nat.floor (b * y)) hcut]

theorem smooth_depletion_norm_le {R : Type*} [NormedField R]
    (h : Nat) (eta : Nat -> R) (W : Real -> R)
    (heta : forall m n : Nat, eta (m * n) = eta m * eta n)
    (hnorm : forall n : Nat, norm (eta n) <= 1)
    (b y alpha C : Real) (hb : 0 <= b) (hy : 0 < y) (hC : 0 <= C)
    (hsup : forall t : Real, b < t -> W t = 0)
    (hbase : forall t : Real, 0 < t -> norm (smoothBase eta W b t) <= C * t ^ alpha) :
    norm (smoothDepleted h eta W b y) <=
      C * y ^ alpha * smoothMass h (Nat.floor (b * y)) alpha := by
  rw [smooth_depletion_identity h eta W heta b y hb hy hsup]
  apply (norm_sum_le _ _).trans
  calc
    _ <= (Finset.Ioc 0 (Nat.floor (b * y))).sum (fun d =>
        C * y ^ alpha * (if SupportedOn h d then 1 / (d : Real) ^ alpha else 0)) := by
      apply Finset.sum_le_sum
      intro d hd
      have hdpos : 0 < (d : Real) := by exact_mod_cast (Finset.mem_Ioc.mp hd).1
      by_cases hs : SupportedOn h d
      . rw [ite_eq_left hs, ite_eq_left hs, norm_mul]
        calc
          _ <= 1 * (C * (y / (d : Real)) ^ alpha) :=
            mul_le_mul (hnorm d) (hbase (y / (d : Real)) (div_pos hy hdpos))
              (norm_nonneg _) (by positivity)
          _ = _ := by
            rw [Real.div_rpow hy.le hdpos.le]
            ring
      . simp only [ite_eq_right hs, norm_zero, mul_zero, le_refl]
    _ = _ := by rw [smoothMass, Finset.mul_sum]

theorem smooth_depletion_uniform {R : Type*} [NormedField R]
    (eta : Nat -> R) (W : Real -> R)
    (heta : forall m n : Nat, eta (m * n) = eta m * eta n)
    (hnorm : forall n : Nat, norm (eta n) <= 1)
    (b alpha eps C : Real) (hb : 0 <= b) (halpha : 0 < alpha)
    (heps : 0 < eps) (hC : 0 <= C)
    (hsup : forall t : Real, b < t -> W t = 0)
    (hbase : forall t : Real, 0 < t -> norm (smoothBase eta W b t) <= C * t ^ alpha) :
    Exists (fun B : Real => 0 < B /\
      forall (h : Nat) (y : Real), Not (h = 0) -> 0 < y ->
        norm (smoothDepleted h eta W b y) <= C * B * y ^ alpha * (h : Real) ^ eps) := by
  choose B hB using eulerMask_subpower alpha eps halpha heps
  refine Exists.intro B (And.intro hB.1 ?_)
  intro h y hh hy
  calc
    _ <= C * y ^ alpha * smoothMass h (Nat.floor (b * y)) alpha :=
      smooth_depletion_norm_le h eta W heta hnorm b y alpha C hb hy hC hsup hbase
    _ <= C * y ^ alpha * eulerMask h alpha :=
      mul_le_mul_of_nonneg_left
        (smoothMass_le_eulerMask h (Nat.floor (b * y)) hh halpha) (by positivity)
    _ <= C * y ^ alpha * (B * (h : Real) ^ eps) :=
      mul_le_mul_of_nonneg_left (hB.2 h hh) (by positivity)
    _ = _ := by ring

def smoothMultipleMasked {R : Type*} [Ring R]
    (h r : Nat) (eta : Nat -> R) (W : Real -> R) (b y : Real) : R :=
  (Finset.Ioc 0 (Nat.floor (b * y))).sum (fun m =>
    if (h * m).Coprime r then
      (ArithmeticFunction.moebius (h * m) : R) * eta (h * m) * W ((m : Real) / y)
    else 0)

theorem smooth_multiple_masked_eq {R : Type*} [CommRing R]
    (h r : Nat) (eta : Nat -> R) (W : Real -> R)
    (heta : forall m n : Nat, eta (m * n) = eta m * eta n) (b y : Real) :
    smoothMultipleMasked h r eta W b y =
      if h.Coprime r then (ArithmeticFunction.moebius h : R) * eta h *
        smoothDepleted (r * h) eta W b y else 0 := by
  unfold smoothMultipleMasked smoothDepleted weightedDepleted
  by_cases hh : h.Coprime r
  . rw [ite_eq_left hh, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m _
    by_cases hr : m.Coprime r
    . rw [ite_eq_left (Nat.coprime_mul_iff_left.mpr (And.intro hh hr))]
      by_cases hm : m.Coprime h
      . rw [ite_eq_left (Nat.coprime_mul_iff_right.mpr (And.intro hr hm))]
        have hmask : maskedMobius h m = ArithmeticFunction.moebius m := by
          change (if m.Coprime h then ArithmeticFunction.moebius m else 0) = _
          exact if_pos hm
        rw [moebius_mul_masked h m, Int.cast_mul, hmask, heta]
        ring
      . have hc : Not (m.Coprime (r * h)) :=
          fun hp => hm (Nat.coprime_mul_iff_right.mp hp).2
        rw [ite_eq_right hc]
        have hmask : maskedMobius h m = 0 := by
          change (if m.Coprime h then ArithmeticFunction.moebius m else 0) = _
          exact if_neg hm
        rw [moebius_mul_masked h m, hmask]
        simp
    . have hc : Not ((h * m).Coprime r) :=
        fun hp => hr (Nat.coprime_mul_iff_left.mp hp).2
      have hcr : Not (m.Coprime (r * h)) :=
        fun hp => hr (Nat.coprime_mul_iff_right.mp hp).1
      rw [ite_eq_right hc, ite_eq_right hcr, mul_zero]
  . rw [ite_eq_right hh]
    apply Finset.sum_eq_zero
    intro m _
    have hc : Not ((h * m).Coprime r) :=
      fun hp => hh (Nat.coprime_mul_iff_left.mp hp).1
    simp only [hc, ite_false]

theorem smooth_multiple_masked_norm_le {R : Type*} [NormedField R]
    (h r : Nat) (eta : Nat -> R) (W : Real -> R)
    (heta : forall m n : Nat, eta (m * n) = eta m * eta n)
    (hnorm : forall n : Nat, norm (eta n) <= 1) (b y : Real) :
    norm (smoothMultipleMasked h r eta W b y) <=
      norm (smoothDepleted (r * h) eta W b y) := by
  rw [smooth_multiple_masked_eq h r eta W heta b y]
  by_cases hh : h.Coprime r
  . rw [ite_eq_left hh, norm_mul, norm_mul]
    calc
      _ <= (1 * 1) * norm (smoothDepleted (r * h) eta W b y) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul (moebius_cast_norm_le h) (hnorm h) (norm_nonneg _) zero_le_one)
          (norm_nonneg _)
      _ = _ := by ring
  . simp only [ite_eq_right hh, norm_zero]
    exact norm_nonneg _

theorem smooth_multiple_masked_uniform {R : Type*} [NormedField R]
    (r : Nat) (hr : Not (r = 0)) (eta : Nat -> R) (W : Real -> R)
    (heta : forall m n : Nat, eta (m * n) = eta m * eta n)
    (hnorm : forall n : Nat, norm (eta n) <= 1)
    (b alpha eps C : Real) (hb : 0 <= b) (halpha : 0 < alpha)
    (heps : 0 < eps) (hC : 0 <= C)
    (hsup : forall t : Real, b < t -> W t = 0)
    (hbase : forall t : Real, 0 < t -> norm (smoothBase eta W b t) <= C * t ^ alpha) :
    Exists (fun K : Real => 0 <= K /\
      forall (h : Nat) (D : Real), Not (h = 0) -> 0 < D ->
        norm (smoothMultipleMasked h r eta W b (D / (h : Real))) <=
          K * D ^ alpha * (h : Real) ^ (eps - alpha)) := by
  choose B hB using
    smooth_depletion_uniform eta W heta hnorm b alpha eps C hb halpha heps hC hsup hbase
  have hBpos : 0 < B := hB.1
  let K : Real := C * B * (r : Real) ^ eps
  refine Exists.intro K (And.intro (by dsimp [K]; positivity) ?_)
  intro h D hh hD
  have hhpos : 0 < (h : Real) := by exact_mod_cast Nat.pos_of_ne_zero hh
  calc
    _ <= norm (smoothDepleted (r * h) eta W b (D / (h : Real))) :=
      smooth_multiple_masked_norm_le h r eta W heta hnorm b (D / (h : Real))
    _ <= C * B * (D / (h : Real)) ^ alpha * ((r * h : Nat) : Real) ^ eps :=
      hB.2 (r * h) (D / (h : Real)) (Nat.mul_ne_zero hr hh) (div_pos hD hhpos)
    _ = _ := by
      rw [Nat.cast_mul, Real.mul_rpow (Nat.cast_nonneg r) hhpos.le,
        Real.div_rpow hD.le hhpos.le, Real.rpow_sub hhpos eps alpha]
      dsimp [K]
      ring

end PrimeFactorOscillations.DepletedMobius

/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Assembly.DetectorPackets.MobiusWindowShift
import PrimeFactorOscillations.Assembly.DetectorPackets.SmoothMobiusTail

/-!
# MobiusWindowBound

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
open MeasureTheory
open PrimeFactorOscillations.DepletedMobius

namespace PrimeFactorOscillations.MobiusWindow

theorem smoothWindow_norm_bound {q : Nat}
    (chi : DirichletCharacter Complex q) (hq : 0 < q)
    (W : Real -> Complex) (lo hi : Real) (hlo : 0 < lo)
    (hsupp : Function.support W <= Set.Icc lo hi)
    (hW : ContDiff Real ((Top.top : ENat) : WithTop ENat) W)
    (a : Real) (ha : (7 / 8 : Real) < a) (ha2 : a <= 2) :
    Exists (fun C : Real => 0 <= C /\ forall y : Real, 0 < y ->
      norm (smoothWindow chi W y) <= C * y ^ a) := by
  letI : NeZero q := NeZero.mk (Nat.ne_of_gt hq)
  choose A hA using mellinInverseData_strip_decay chi hq W lo hi hlo hsupp hW a ha
  let J : Real := integral volume (fun t : Real => Inv.inv (1 + t ^ 2))
  have hJ : 0 <= J := integral_nonneg (fun t => by positivity)
  let C : Real := norm (1 / (2 * Real.pi) : Complex) * A * J
  refine Exists.intro C (And.intro (mul_nonneg
    (mul_nonneg (norm_nonneg _) hA.1) hJ) ?_)
  intro y hy
  have hmajor := integrable_inv_one_add_sq.const_mul (y ^ a * A)
  have hiBound : norm (integral volume (fun t : Real =>
      windowIntegrand chi W y ((a : Complex) + (t : Complex) * Complex.I))) <=
      (y ^ a * A) * J := by
    calc
      _ <= integral volume (fun t : Real => (y ^ a * A) * Inv.inv (1 + t ^ 2)) := by
        apply norm_integral_le_of_norm_le hmajor
        exact Filter.Eventually.of_forall (fun t => by
          rw [windowIntegrand_norm chi W y hy a t]
          calc
            _ <= y ^ a * (A / (1 + t ^ 2)) :=
              mul_le_mul_of_nonneg_left (hA.2 a (And.intro le_rfl ha2) t)
                (Real.rpow_nonneg hy.le _)
            _ = _ := by rw [div_eq_mul_inv]; ring)
      _ = _ := by rw [integral_const_mul]
  rw [smoothWindow_mellin_shift chi hq W lo hi hlo hsupp hW a ha ha2 y hy, norm_mul]
  calc
    _ <= norm (1 / (2 * Real.pi) : Complex) * ((y ^ a * A) * J) :=
      mul_le_mul_of_nonneg_left hiBound (norm_nonneg _)
    _ = C * y ^ a := by dsimp [C]; ring

theorem smoothWindow_eq_smoothBase {q : Nat}
    (chi : DirichletCharacter Complex q) (W : Real -> Complex)
    (b y : Real) (hy : 0 < y)
    (hsup : forall t : Real, b < t -> W t = 0) :
    smoothWindow chi W y =
      smoothBase (fun n : Nat => chi (n : ZMod q)) W b y := by
  let N : Nat := Nat.floor (b * y)
  have hzero : forall n : Nat, Not (Membership.mem (Finset.range N) n) ->
      coefficient chi n * W (positiveNorm n / y) = 0 := by
    intro n hn
    have hnle : N <= n :=
      Nat.le_of_not_gt (fun h => hn (Finset.mem_range.mpr h))
    have hcut : Nat.floor (b * y) < n + 1 := by
      change Nat.floor (b * y) <= n at hnle
      omega
    rw [positiveNorm, window_vanishes_above W b y hy hsup (n + 1) hcut, mul_zero]
  have hfin : smoothWindow chi W y =
      (Finset.range N).sum (fun n => coefficient chi n * W (positiveNorm n / y)) := by
    unfold smoothWindow
    exact tsum_eq_sum (s := Finset.range N) hzero
  rw [hfin]
  change (Finset.range N).sum (fun n => coefficient chi n * W (positiveNorm n / y)) =
    weightedBase (fun n : Nat => chi (n : ZMod q)) (fun n => W ((n : Real) / y)) N
  unfold weightedBase
  have hset : Finset.Ioc 0 N = Finset.Ico 1 (N + 1) := by
    ext n
    simp only [Finset.mem_Ioc, Finset.mem_Ico]
    omega
  rw [hset, Finset.sum_Ico_eq_sum_range]
  have hlen : N + 1 - 1 = N := by omega
  rw [hlen]
  apply Finset.sum_congr rfl
  intro n _
  simp only [coefficient, positiveNorm, Nat.add_comm]

theorem smoothBase_character_norm_bound {q : Nat}
    (chi : DirichletCharacter Complex q) (hq : 0 < q)
    (W : Real -> Complex) (lo hi : Real) (hlo : 0 < lo)
    (hsupp : Function.support W <= Set.Icc lo hi)
    (hW : ContDiff Real ((Top.top : ENat) : WithTop ENat) W)
    (a : Real) (ha : (7 / 8 : Real) < a) (ha2 : a <= 2) :
    Exists (fun C : Real => 0 <= C /\ forall y : Real, 0 < y ->
      norm (smoothBase (fun n : Nat => chi (n : ZMod q)) W hi y) <= C * y ^ a) := by
  choose C hC using smoothWindow_norm_bound chi hq W lo hi hlo hsupp hW a ha ha2
  refine Exists.intro C (And.intro hC.1 ?_)
  intro y hy
  have hsup : forall t : Real, hi < t -> W t = 0 := by
    intro t ht
    by_contra hn
    have hmem : Membership.mem (Function.support W) t := hn
    exact (not_le_of_gt ht) (hsupp hmem).2
  rw [<- smoothWindow_eq_smoothBase chi W hi y hy hsup]
  exact hC.2 y hy

end PrimeFactorOscillations.MobiusWindow

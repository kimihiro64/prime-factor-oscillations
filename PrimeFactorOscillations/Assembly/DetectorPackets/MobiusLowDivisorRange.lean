/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Assembly.DetectorPackets.MobiusWindowBound
import PrimeFactorOscillations.Assembly.DetectorPackets.SchwartzIntegerPowerTail
import PrimeFactorOscillations.Assembly.DetectorPackets.SmoothMobiusDepletion

/-!
# MobiusLowDivisorRange

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

namespace PrimeFactorOscillations.MobiusLowDivisorRange

theorem real_power_tail (p : Real) (hp : 1 < p) (T N : Nat) (hT : 0 < T) :
    (Finset.Ioc T N).sum (fun d => 1 / (d : Real) ^ p) <=
      (1 / (T : Real) ^ (p - 1)) / (p - 1) := by
  let w : Nat -> Real := fun n => 1 / (n : Real) ^ p
  have hw : Summable w := by
    simpa only [w, one_div] using (Real.summable_nat_rpow_inv).mpr hp
  have hTR : 0 < (T : Real) := by exact_mod_cast hT
  have hanti : AntitoneOn (fun t : Real => t ^ (-p)) (Set.Ici (T : Real)) := by
    intro x hx y hy hxy
    exact Real.rpow_le_rpow_of_nonpos (lt_of_lt_of_le hTR hx) hxy (by linarith)
  have hlt : -p < -1 := by linarith
  have hi := AntitoneOn.tsum_comp_add_le_integral T hanti
    (integrableOn_Ioi_rpow_of_lt hlt hTR)
    (fun t ht => Real.rpow_nonneg (le_of_lt (lt_trans hTR ht)) _)
  have hconvert (n : Nat) :
      (((n + T + 1 : Nat) : Real) ^ (-p)) = w (n + (T + 1)) := by
    dsimp only [w]
    rw [Real.rpow_neg (by positivity), one_div, Nat.add_assoc]
  have he : -p + 1 = -(p - 1) := by ring
  have hintegral :
      (integral (volume.restrict (Set.Ioi (T : Real))) (fun t : Real => t ^ (-p))) =
        (1 / (T : Real) ^ (p - 1)) / (p - 1) := by
    rw [integral_Ioi_rpow_of_lt hlt hTR, he, Real.rpow_neg hTR.le]
    field_simp
  rw [hintegral] at hi
  have hshift : Summable (fun n : Nat => w (n + (T + 1))) :=
    (summable_nat_add_iff (T + 1)).mpr hw
  let E := (Finset.Ioc T N).image (fun d => d - (T + 1))
  have heq : (Finset.Ioc T N).sum w = E.sum (fun n => w (n + (T + 1))) := by
    dsimp only [E]
    rw [Finset.sum_image]
    . apply Finset.sum_congr rfl
      intro d hd
      rw [Nat.sub_add_cancel (show T + 1 <= d from (Finset.mem_Ioc.mp hd).1)]
    . intro a ha b hb hab
      have hta := (Finset.mem_Ioc.mp ha).1
      have htb := (Finset.mem_Ioc.mp hb).1
      change a - (T + 1) = b - (T + 1) at hab
      omega
  calc
    _ = E.sum (fun n => w (n + (T + 1))) := heq
    _ <= tsum (fun n : Nat => w (n + (T + 1))) :=
      hshift.sum_le_tsum E (fun n hn => by dsimp only [w]; positivity)
    _ <= _ := by simpa only [hconvert] using hi

theorem signed_power_tail (a e B D : Real) (hae : 1 < 2 * (a - e))
    (hB : 0 <= B) (hD : 0 < D) (T N : Nat) (hT : 0 < T)
    (sign : Nat -> Real) (M : Nat -> Complex)
    (hsign : forall d, Membership.mem (Finset.Ioc T N) d -> abs (sign d) <= 1)
    (hM : forall d, Membership.mem (Finset.Ioc T N) d ->
      norm (M d) <= B * D ^ a * (d : Real) ^ (e - a)) :
    abs ((Finset.Ioc T N).sum (fun d => sign d * norm (M d) ^ 2)) <=
      B ^ 2 * D ^ (2 * a) *
        ((1 / (T : Real) ^ (2 * (a - e) - 1)) / (2 * (a - e) - 1)) := by
  have hpD : (D ^ a) ^ 2 = D ^ (2 * a) := by
    rw [pow_two, <- Real.rpow_add hD]
    congr 1
    ring
  calc
    _ <= (Finset.Ioc T N).sum (fun d => abs (sign d * norm (M d) ^ 2)) :=
      Finset.abs_sum_le_sum_abs _ _
    _ <= (Finset.Ioc T N).sum (fun d =>
        B ^ 2 * D ^ (2 * a) * (1 / (d : Real) ^ (2 * (a - e)))) := by
      apply Finset.sum_le_sum
      intro d hd
      have hdR : 0 < (d : Real) := by
        exact_mod_cast (lt_trans hT (Finset.mem_Ioc.mp hd).1)
      have hm := hM d hd
      have hb0 : 0 <= B * D ^ a * (d : Real) ^ (e - a) := by positivity
      have hsq : norm (M d) ^ 2 <= (B * D ^ a * (d : Real) ^ (e - a)) ^ 2 := by
        nlinarith [norm_nonneg (M d)]
      have hpd : ((d : Real) ^ (e - a)) ^ 2 =
          1 / (d : Real) ^ (2 * (a - e)) := by
        rw [pow_two, <- Real.rpow_add hdR]
        have he : (e - a) + (e - a) = -(2 * (a - e)) := by ring
        rw [he, Real.rpow_neg hdR.le, one_div]
      rw [abs_mul]
      rw [show abs (norm (M d) ^ 2) = norm (M d) ^ 2 from abs_of_nonneg (sq_nonneg _)]
      calc
        _ <= norm (M d) ^ 2 :=
          (mul_le_mul_of_nonneg_right (hsign d hd) (sq_nonneg _)).trans_eq (one_mul _)
        _ <= _ := hsq
        _ = _ := by rw [mul_pow, mul_pow, hpD, hpd]
    _ = (B ^ 2 * D ^ (2 * a)) *
        (Finset.Ioc T N).sum (fun d => 1 / (d : Real) ^ (2 * (a - e))) := by
      rw [Finset.mul_sum]
    _ <= _ := mul_le_mul_of_nonneg_left
      (real_power_tail (2 * (a - e)) hae T N hT) (by positivity)

open DepletedMobius

theorem character_masked_divisor_tail {q : Nat}
    (chi : DirichletCharacter Complex q) (hq : 0 < q)
    (W : Real -> Complex) (lo hi : Real) (hlo : 0 < lo) (hhi : 0 <= hi)
    (hsupp : Function.support W <= Set.Icc lo hi)
    (hW : ContDiff Real ((Top.top : ENat) : WithTop ENat) W)
    (a e : Real) (ha : (7 / 8 : Real) < a) (ha2 : a <= 2)
    (he : 0 < e) (hae : 1 < 2 * (a - e)) :
    Exists (fun K : Real => 0 <= K /\
      forall (r T N : Nat) (D : Real), Not (r = 0) -> 0 < T -> 0 < D ->
      abs ((Finset.Ioc T N).sum (fun d =>
        (ArithmeticFunction.moebius d : Real) *
        norm (smoothMultipleMasked d r (fun n => chi (n : ZMod q)) W hi
          (D / (d : Real))) ^ 2)) <=
        K * (r : Real) ^ (2 * e) * D ^ (2 * a) /
          (T : Real) ^ (2 * (a - e) - 1)) := by
  let eta : Nat -> Complex := fun n => chi (n : ZMod q)
  have heta : forall m n : Nat, eta (m * n) = eta m * eta n := by
    intro m n
    simp only [eta, Nat.cast_mul, map_mul]
  have hnorm : forall n : Nat, norm (eta n) <= 1 := fun n => chi.norm_le_one _
  have hsup : forall t : Real, hi < t -> W t = 0 := by
    intro t ht
    by_contra hn
    exact (not_le_of_gt ht) (hsupp (show Membership.mem (Function.support W) t from hn)).2
  choose C hC using MobiusWindow.smoothBase_character_norm_bound
    chi hq W lo hi hlo hsupp hW a ha ha2
  have ha0 : 0 < a := by linarith
  choose B hB using smooth_depletion_uniform eta W heta hnorm hi a e C hhi ha0 he hC.1
    hsup hC.2
  have hB0 : 0 <= B := hB.1.le
  have hC0 : 0 <= C := hC.1
  let K : Real := (C * B) ^ 2 / (2 * (a - e) - 1)
  refine Exists.intro K (And.intro (by dsimp [K]; positivity) ?_)
  intro r T N D hr hT hD
  have hMr (d : Nat) (hd : Membership.mem (Finset.Ioc T N) d) :
      norm (smoothMultipleMasked d r eta W hi (D / (d : Real))) <=
        (C * B * (r : Real) ^ e) * D ^ a * (d : Real) ^ (e - a) := by
    have hd0 : 0 < d := lt_trans hT (Finset.mem_Ioc.mp hd).1
    have hdR : 0 < (d : Real) := by exact_mod_cast hd0
    calc
      _ <= norm (smoothDepleted (r * d) eta W hi (D / (d : Real))) :=
        smooth_multiple_masked_norm_le d r eta W heta hnorm hi (D / (d : Real))
      _ <= C * B * (D / (d : Real)) ^ a * ((r * d : Nat) : Real) ^ e :=
        hB.2 (r * d) (D / (d : Real)) (Nat.mul_ne_zero hr (Nat.ne_of_gt hd0))
          (div_pos hD hdR)
      _ = _ := by
        rw [Nat.cast_mul, Real.mul_rpow (Nat.cast_nonneg r) hdR.le,
          Real.div_rpow hD.le hdR.le, Real.rpow_sub hdR e a]
        ring
  have hsign (d : Nat) (hd : Membership.mem (Finset.Ioc T N) d) :
      abs (ArithmeticFunction.moebius d : Real) <= 1 := by
    rcases ArithmeticFunction.moebius_eq_or d with h | h | h <;> simp [h]
  have ht := signed_power_tail a e (C * B * (r : Real) ^ e) D hae
    (by positivity) hD T N hT (fun d => (ArithmeticFunction.moebius d : Real))
    (fun d => smoothMultipleMasked d r eta W hi (D / (d : Real))) hsign hMr
  have hrR : 0 < (r : Real) := by exact_mod_cast Nat.pos_of_ne_zero hr
  have hpr : ((r : Real) ^ e) ^ 2 = (r : Real) ^ (2 * e) := by
    rw [pow_two, <- Real.rpow_add hrR]
    congr 1
    ring
  apply ht.trans_eq
  dsimp [K]
  rw [mul_pow, hpr]
  ring

end PrimeFactorOscillations.MobiusLowDivisorRange


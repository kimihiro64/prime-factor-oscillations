/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import Lean.Elab.Tactic.Omega
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SumIntegralComparisons
import PrimeFactorOscillations.Assembly.DetectorPackets.SmoothMobiusDepletion

/-!
# SmoothMobiusTail

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

theorem sum_Ioc_eq_shifted {R : Type*} [AddCommMonoid R]
    (f : Nat -> R) (H N : Nat) (hHN : H <= N) :
    (Finset.Ioc H N).sum f =
      (Finset.range (N - H)).sum (fun i => f (H + (i + 1))) := by
  have hset : Finset.Ioc H N = Finset.Ico (H + 1) (N + 1) := by
    ext n
    simp only [Finset.mem_Ioc, Finset.mem_Ico]
    omega
  rw [hset, Finset.sum_Ico_eq_sum_range]
  have hlen : N + 1 - (H + 1) = N - H := by omega
  rw [hlen]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  omega

theorem sum_Ioc_negative_rpow_le (H N : Nat) (hH : 0 < H)
    (p : Real) (hp : 1 < p) :
    (Finset.Ioc H N).sum (fun h => (h : Real) ^ (-p)) <=
      (H : Real) ^ (1 - p) / (p - 1) := by
  by_cases hHN : H <= N
  . have hHreal : 0 < (H : Real) := by exact_mod_cast hH
    have hf : AntitoneOn (fun x : Real => x ^ (-p))
        (Set.Icc (H : Real) ((H : Real) + ((N - H : Nat) : Real))) := by
      intro x hx y _ hxy
      exact Real.rpow_le_rpow_of_nonpos (hHreal.trans_le hx.1) hxy (by linarith)
    have hupper : (H : Real) + ((N - H : Nat) : Real) = (N : Real) := by
      exact_mod_cast Nat.add_sub_of_le hHN
    have hcmp := hf.sum_le_integral
    rw [hupper] at hcmp
    have heq : (Finset.Ioc H N).sum (fun h => (h : Real) ^ (-p)) =
        (Finset.range (N - H)).sum
          (fun i => ((H : Real) + ((i + 1 : Nat) : Real)) ^ (-p)) := by
      rw [sum_Ioc_eq_shifted (fun h => (h : Real) ^ (-p)) H N hHN]
      simp only [Nat.cast_add]
    apply (heq.le.trans hcmp).trans
    have hzero : Not (Membership.mem (Set.uIcc (H : Real) (N : Real)) (0 : Real)) := by
      rw [Set.uIcc_of_le (by exact_mod_cast hHN)]
      intro hz
      exact (not_le_of_gt hHreal) hz.1
    rw [integral_rpow (Or.inr (And.intro (by linarith : Not (-p = -1)) hzero))]
    have he : -p + 1 = 1 - p := by ring
    rw [he]
    calc
      _ = ((H : Real) ^ (1 - p) - (N : Real) ^ (1 - p)) / (p - 1) := by
        have hi : Inv.inv (1 - p) = -(Inv.inv (p - 1)) := by
          rw [show 1 - p = -(p - 1) by ring, inv_neg]
        simp only [div_eq_mul_inv, hi]
        ring
      _ <= _ := div_le_div_of_nonneg_right
        (sub_le_self _ (Real.rpow_nonneg (Nat.cast_nonneg N) _)) (by linarith)
  . rw [Finset.Ioc_eq_empty_of_le (Nat.le_of_not_ge hHN), Finset.sum_empty]
    positivity

def normalizedSmoothSize {R : Type*} [NormedField R]
    (h r : Nat) (eta : Nat -> R) (W : Real -> R) (b D : Real) : Real :=
  D ^ (-(1 / 2 : Real)) *
    norm (smoothMultipleMasked h r eta W b (D / (h : Real)))

theorem normalized_smooth_size_nonneg {R : Type*} [NormedField R]
    (h r : Nat) (eta : Nat -> R) (W : Real -> R) (b D : Real) (hD : 0 <= D) :
    0 <= normalizedSmoothSize h r eta W b D :=
  mul_nonneg (Real.rpow_nonneg hD _) (norm_nonneg _)

theorem normalized_smooth_size_uniform {R : Type*} [NormedField R]
    (r : Nat) (hr : Not (r = 0)) (eta : Nat -> R) (W : Real -> R)
    (heta : forall m n : Nat, eta (m * n) = eta m * eta n)
    (hnorm : forall n : Nat, norm (eta n) <= 1)
    (b alpha eps C : Real) (hb : 0 <= b) (halpha : 0 < alpha)
    (heps : 0 < eps) (hC : 0 <= C)
    (hsup : forall t : Real, b < t -> W t = 0)
    (hbase : forall t : Real, 0 < t -> norm (smoothBase eta W b t) <= C * t ^ alpha) :
    Exists (fun K : Real => 0 <= K /\
      forall (h : Nat) (D : Real), Not (h = 0) -> 0 < D ->
        normalizedSmoothSize h r eta W b D <=
          K * D ^ (alpha - 1 / 2) * (h : Real) ^ (eps - alpha)) := by
  choose K hK using
    smooth_multiple_masked_uniform r hr eta W heta hnorm
      b alpha eps C hb halpha heps hC hsup hbase
  refine Exists.intro K (And.intro hK.1 ?_)
  intro h D hh hD
  unfold normalizedSmoothSize
  calc
    _ <= D ^ (-(1 / 2 : Real)) * (K * D ^ alpha * (h : Real) ^ (eps - alpha)) :=
      mul_le_mul_of_nonneg_left (hK.2 h D hh hD) (Real.rpow_nonneg hD.le _)
    _ = _ := by
      rw [Real.rpow_sub hD alpha (1 / 2), Real.rpow_neg hD.le]
      ring

theorem finite_energy_tail_le (A : Nat -> Real)
    (K D u : Real) (hK : 0 <= K) (hD : 0 < D) (H N : Nat) (hH : 0 < H)
    (hA : forall h : Nat, Membership.mem (Finset.Ioc H N) h ->
      0 <= A h /\ A h <= K * D ^ (3 / 8 + u) * (h : Real) ^ (-(7 / 8 : Real))) :
    (Finset.Ioc H N).sum (fun h => (A h) ^ 2) <=
      (4 / 3 : Real) * K ^ 2 * D ^ (3 / 4 + 2 * u) * (H : Real) ^ (-(3 / 4 : Real)) := by
  have hterm : (Finset.Ioc H N).sum (fun h => (A h) ^ 2) <=
      (K ^ 2 * D ^ (3 / 4 + 2 * u)) *
        (Finset.Ioc H N).sum (fun h => (h : Real) ^ (-(7 / 4 : Real))) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro h hh
    have hhpos : 0 < (h : Real) := by
      exact_mod_cast Nat.lt_of_le_of_lt (Nat.zero_le H) (Finset.mem_Ioc.mp hh).1
    have hsq := mul_self_le_mul_self (hA h hh).1 (hA h hh).2
    calc
      _ <= (K * D ^ (3 / 8 + u) * (h : Real) ^ (-(7 / 8 : Real))) ^ 2 := by
        simpa only [pow_two] using hsq
      _ = _ := by
        rw [mul_pow, mul_pow, <- Real.rpow_mul_natCast hD.le,
          <- Real.rpow_mul_natCast hhpos.le]
        norm_num only [Nat.cast_ofNat]
        rw [show ((3 / 8 : Real) + u) * (2 : Real) = 3 / 4 + 2 * u by ring]
  apply hterm.trans
  have ht := sum_Ioc_negative_rpow_le H N hH (7 / 4) (by norm_num)
  norm_num at ht
  calc
    _ <= (K ^ 2 * D ^ (3 / 4 + 2 * u)) *
        ((H : Real) ^ (-(3 / 4 : Real)) / (3 / 4 : Real)) :=
      mul_le_mul_of_nonneg_left ht (by positivity)
    _ = _ := by ring

theorem signed_energy_tail_abs_le (A : Nat -> Real) (H N : Nat) :
    norm ((Finset.Ioc H N).sum
      (fun h => (ArithmeticFunction.moebius h : Real) * (A h) ^ 2)) <=
      (Finset.Ioc H N).sum (fun h => (A h) ^ 2) := by
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro h _
  rw [norm_mul, Real.norm_eq_abs ((A h) ^ 2), abs_of_nonneg (sq_nonneg _)]
  calc
    _ <= 1 * (A h) ^ 2 :=
      mul_le_mul_of_nonneg_right (moebius_cast_norm_le h) (sq_nonneg _)
    _ = _ := one_mul _

theorem smooth_packet_energy_tail {R : Type*} [NormedField R]
    (r : Nat) (hr : Not (r = 0)) (eta : Nat -> R) (W : Real -> R)
    (heta : forall m n : Nat, eta (m * n) = eta m * eta n)
    (hnorm : forall n : Nat, norm (eta n) <= 1)
    (b u C : Real) (hb : 0 <= b) (hu : 0 < u) (hC : 0 <= C)
    (hsup : forall t : Real, b < t -> W t = 0)
    (hbase : forall t : Real, 0 < t ->
      norm (smoothBase eta W b t) <= C * t ^ (7 / 8 + u)) :
    Exists (fun K : Real => 0 <= K /\
      forall (D : Real) (H N : Nat), 0 < D -> 0 < H ->
        (Finset.Ioc H N).sum (fun h => (normalizedSmoothSize h r eta W b D) ^ 2) <=
          (4 / 3 : Real) * K ^ 2 * D ^ (3 / 4 + 2 * u) *
            (H : Real) ^ (-(3 / 4 : Real))) := by
  choose K hK using normalized_smooth_size_uniform r hr eta W heta hnorm
    b (7 / 8 + u) u C hb (by linarith) hu hC hsup hbase
  refine Exists.intro K (And.intro hK.1 ?_)
  intro D H N hD hH
  apply finite_energy_tail_le (fun h => normalizedSmoothSize h r eta W b D)
    K D u hK.1 hD H N hH
  intro h hh
  have hhpos : 0 < h :=
    Nat.lt_of_le_of_lt (Nat.zero_le H) (Finset.mem_Ioc.mp hh).1
  refine And.intro (normalized_smooth_size_nonneg h r eta W b D hD.le) ?_
  have hrow := hK.2 h D (Nat.ne_of_gt hhpos) hD
  rwa [show (7 / 8 : Real) + u - 1 / 2 = 3 / 8 + u by ring,
    show u - ((7 / 8 : Real) + u) = -(7 / 8 : Real) by ring] at hrow

theorem energy_tail_endpoint_scale (E K D u tau : Real) (H : Nat)
    (hK : 0 <= K) (hD : 0 < D)
    (hscale : D ^ (1 / 3 + tau) <= (H : Real))
    (hE : E <= (4 / 3 : Real) * K ^ 2 * D ^ (3 / 4 + 2 * u) *
      (H : Real) ^ (-(3 / 4 : Real))) :
    E <= (4 / 3 : Real) * K ^ 2 * D ^ (1 / 2 - (3 * tau / 4 - 2 * u)) := by
  have hp := Real.rpow_le_rpow_of_nonpos
    (Real.rpow_pos_of_pos hD (1 / 3 + tau)) hscale
    (by norm_num : -(3 / 4 : Real) <= 0)
  apply hE.trans
  calc
    _ <= (4 / 3 : Real) * K ^ 2 *
        (D ^ (3 / 4 + 2 * u) * (D ^ (1 / 3 + tau)) ^ (-(3 / 4 : Real))) := by
      simpa only [mul_assoc] using
        mul_le_mul_of_nonneg_left hp
          (show 0 <= (4 / 3 : Real) * K ^ 2 * D ^ (3 / 4 + 2 * u) by positivity)
    _ = _ := by
      rw [<- Real.rpow_mul hD.le, <- Real.rpow_add hD]
      congr 2
      ring

theorem energy_tail_endpoint_saving (u tau : Real)
    (htau : 0 < tau) (hu : 0 < u) (hsmall : u < 3 * tau / 8) :
    0 < 3 * tau / 4 - 2 * u := by
  linarith

end PrimeFactorOscillations.DepletedMobius

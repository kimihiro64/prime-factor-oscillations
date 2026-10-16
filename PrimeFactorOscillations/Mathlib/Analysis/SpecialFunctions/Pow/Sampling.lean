/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Subpower meshes and floor-power sampling

Subpower gap bounds imply that late power windows meet the mesh.
The exact samples floor(n^q), for every real q >= 1, are strictly increasing
and have an explicit gap bound. Critical meshes approximate logarithmic times.
-/

set_option autoImplicit false
set_option Elab.async false

open Filter
open scoped Topology

noncomputable section

namespace Nat

/-- Successive samples have gaps smaller than every power above `a`. -/
def SubpowerGapBound (u : Nat -> Nat) (a : Real) : Prop :=
  forall e : Real, 0 < e -> exists C : Real, 0 < C /\
    Filter.Eventually (fun j : Nat =>
      (u (j + 1) : Real) - (u j : Real) <= C * (u j : Real) ^ (a + e)) atTop

/-- Every sufficiently late power window meets a mesh with smaller gap exponent. -/
theorem eventually_exists_sample_mem_power_window
    (u : Nat -> Nat) (hu : StrictMono u) (a d : Real)
    (ha : 0 <= a) (had : a < d) (hmesh : SubpowerGapBound u a) :
    Filter.Eventually (fun x : Real =>
      exists j : Nat, x <= (u j : Real) /\ (u j : Real) <= x + x ^ d) atTop := by
  classical
  choose C hC hgap using hmesh ((d - a) / 2) (by linarith)
  choose J hJ using eventually_atTop.1 hgap
  have hdecay : Tendsto (fun x : Real => C * x ^ (-(d - a) / 2))
      atTop (nhds 0) := by
    simpa only [mul_zero, neg_div] using
      (tendsto_rpow_neg_atTop (by linarith : 0 < (d - a) / 2)).const_mul C
  have hsmall : Filter.Eventually
      (fun x : Real => C * x ^ (-(d - a) / 2) <= 1) atTop :=
    hdecay.eventually (eventually_le_nhds (by norm_num : (0 : Real) < 1))
  filter_upwards [hsmall, eventually_gt_atTop (0 : Real),
      eventually_gt_atTop (u (J + 1) : Real)] with x hxsmall hx hxJ
  have hex : exists j : Nat, x <= (u j : Real) := by
    choose j hj using exists_nat_gt x
    exact Exists.intro j (le_trans (le_of_lt hj) (by exact_mod_cast hu.id_le j))
  let j := Nat.find hex
  have hj : x <= (u j : Real) := Nat.find_spec hex
  have hJj : J + 1 < j := by
    by_contra h
    have hle : j <= J + 1 := le_of_not_gt h
    have hule : (u j : Real) <= (u (J + 1) : Real) := by
      exact_mod_cast hu.monotone hle
    linarith
  have hjpos : 0 < j := lt_of_le_of_lt (Nat.zero_le (J + 1)) hJj
  have hpredlt : j - 1 < j := Nat.sub_lt hjpos (by decide)
  have hpred : (u (j - 1) : Real) < x :=
    lt_of_not_ge (Nat.find_min hex hpredlt)
  have hJpred : J <= j - 1 := by omega
  have hsucc : j - 1 + 1 = j := Nat.sub_add_cancel (by omega)
  have hgap' := hJ (j - 1) hJpred
  rw [hsucc] at hgap'
  have hpow : (u (j - 1) : Real) ^ (a + (d - a) / 2) <=
      x ^ (a + (d - a) / 2) :=
    Real.rpow_le_rpow (Nat.cast_nonneg _) (le_of_lt hpred) (by linarith)
  have hbound : C * x ^ (a + (d - a) / 2) <= x ^ d := by
    have hmul := mul_le_mul_of_nonneg_left hxsmall
      (Real.rpow_nonneg (le_of_lt hx) d)
    have hid : d + (-(d - a) / 2) = a + (d - a) / 2 := by ring
    rw [mul_one, mul_left_comm, <- Real.rpow_add hx, hid] at hmul
    exact hmul
  exact Exists.intro j (And.intro hj (by
    have := mul_le_mul_of_nonneg_left hpow (le_of_lt hC)
    linarith))

theorem strictMono_fourthPower : StrictMono (fun j : Nat => j ^ 4) := by
  intro i j hij
  exact Nat.pow_lt_pow_left hij (by decide)

theorem subpowerGapBound_fourthPower :
    SubpowerGapBound (fun j : Nat => j ^ 4) (3 / 4) := by
  intro e he
  refine Exists.intro 15 (And.intro (by norm_num) ?_)
  filter_upwards [eventually_ge_atTop (1 : Nat)] with j hj
  have hJ : (1 : Real) <= j := by exact_mod_cast hj
  have hJ0 : (0 : Real) <= j := Nat.cast_nonneg j
  have hJ2 : (j : Real) <= (j : Real) ^ 2 := by nlinarith
  have hJ3 : (j : Real) ^ 2 <= (j : Real) ^ 3 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hJ) (sq_nonneg (j : Real))]
  have hgap : ((j + 1) ^ 4 : Nat) - (j ^ 4 : Real) <= 15 * (j : Real) ^ 3 := by
    push_cast
    nlinarith [sq_nonneg ((j : Real) - 1)]
  have hid : ((j : Real) ^ 4) ^ (3 / 4 : Real) = (j : Real) ^ 3 := by
    rw [<- Real.rpow_natCast]
    rw [<- Real.rpow_mul hJ0]
    norm_num
  have hexp : ((j : Real) ^ 4) ^ (3 / 4 : Real) <=
      ((j : Real) ^ 4) ^ (3 / 4 + e) :=
    Real.rpow_le_rpow_of_exponent_le (by nlinarith [sq_nonneg ((j : Real) ^ 2 - 1)])
      (by linarith)
  push_cast
  rw [hid] at hexp
  linarith

end Nat


namespace Nat

/-- Exact samples for a fixed real q >= 1, including the endpoints n = 0 and n = 1.
Strict increase will rule out overlaps and repeated cutoffs on this domain. -/
def powerSamples (q : Real) (n : Nat) : Nat := Nat.floor ((n : Real) ^ q)

end Nat

namespace Real

/-- Uniform real-power increment bounds on the exact domain q >= 1 and x >= 1. -/
theorem rpow_succ_sub_bounds (q : Real) (hq : 1 <= q) (x : Real) (hx : 1 <= x) :
    1 <= (x + 1) ^ q - x ^ q /\
      (x + 1) ^ q - x ^ q <= q * 2 ^ (q - 1) * x ^ (q - 1) := by
  have hCont : ContinuousOn (fun t : Real => t ^ q) (Set.Icc x (x + 1)) := by
    intro t _
    exact (Real.continuousAt_rpow_const t q (Or.inr (by linarith))).continuousWithinAt
  have hDeriv : forall t : Real, Set.Ioo x (x + 1) t ->
      HasDerivAt (fun t : Real => t ^ q) (q * t ^ (q - 1)) t :=
    fun _ _ => Real.hasDerivAt_rpow_const (Or.inr hq)
  choose c hc hRaw using exists_hasDerivAt_eq_slope (fun t : Real => t ^ q)
    (fun t : Real => q * t ^ (q - 1)) (by linarith : x < x + 1) hCont hDeriv
  have hEq : q * c ^ (q - 1) = (x + 1) ^ q - x ^ q := by
    simpa only [add_sub_cancel_left, div_one] using hRaw
  have hExponent : 0 <= q - 1 := by linarith
  have hcOne : 1 <= c := hx.trans hc.1.le
  have hPowLow : 1 <= c ^ (q - 1) := Real.one_le_rpow hcOne hExponent
  have hcUpper : c <= 2 * x := by linarith [hc.2]
  have hPowHigh : c ^ (q - 1) <= (2 * x) ^ (q - 1) :=
    Real.rpow_le_rpow (by linarith) hcUpper hExponent
  rw [Real.mul_rpow (by norm_num : (0 : Real) <= 2) (by linarith : 0 <= x)] at hPowHigh
  refine And.intro ?_ ?_
  . rw [<- hEq]
    have hMul := _root_.mul_le_mul_of_nonneg_right hq
      (Real.rpow_nonneg (by linarith : 0 <= c) (q - 1))
    simp only [one_mul] at hMul
    exact hPowLow.trans hMul
  . rw [<- hEq]
    have hMul := mul_le_mul_of_nonneg_left hPowHigh (by linarith : 0 <= q)
    convert hMul using 1 <;> ring

end Real

namespace Nat

theorem strictMono_powerSamples (q : Real) (hq : 1 <= q) : StrictMono (powerSamples q) := by
  apply strictMono_nat_of_lt_succ
  intro n
  by_cases hn : n = 0
  . subst n
    have hqZero : Not (q = 0) := ne_of_gt (lt_of_lt_of_le zero_lt_one hq)
    simp [powerSamples, Real.zero_rpow hqZero]
  . have hnOne : 1 <= n := Nat.one_le_iff_ne_zero.mpr hn
    have hx : (1 : Real) <= n := by
      simpa only [Nat.cast_one] using (Nat.cast_le.mpr hnOne : ((1 : Nat) : Real) <= (n : Real))
    have hBound := (Real.rpow_succ_sub_bounds q hq (n : Real) hx).1
    have hFloor : (powerSamples q n : Real) <= (n : Real) ^ q :=
      Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg n) q)
    have hCast : ((powerSamples q n + 1 : Nat) : Real) <= ((n + 1 : Nat) : Real) ^ q := by
      simp only [Nat.cast_add, Nat.cast_one]
      linarith
    exact Nat.lt_of_succ_le (Nat.le_floor hCast)

theorem powerSamples_ge_base (q : Real) (hq : 1 <= q) (n : Nat) (hn : 1 <= n) :
    n <= powerSamples q n := by
  have hx : (1 : Real) <= n := by
    simpa only [Nat.cast_one] using (Nat.cast_le.mpr hn : ((1 : Nat) : Real) <= (n : Real))
  apply Nat.le_floor
  simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hx hq

theorem powerSamples_gap_le (q : Real) (hq : 1 <= q) (n : Nat) (hn : 2 <= n) :
    (powerSamples q (n + 1) : Real) - (powerSamples q n : Real) <=
      ((q * 2 ^ (q - 1) + 1) * 2 ^ (1 - 1 / q)) *
        (powerSamples q n : Real) ^ (1 - 1 / q) := by
  have hqPos : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have hnOne : 1 <= n := by omega
  have hx : (1 : Real) <= n := by
    simpa only [Nat.cast_one] using (Nat.cast_le.mpr hnOne : ((1 : Nat) : Real) <= (n : Real))
  have hxTwo : (2 : Real) <= n := by
    simpa only [Nat.cast_ofNat] using (Nat.cast_le.mpr hn : ((2 : Nat) : Real) <= (n : Real))
  have hBase : (n : Real) <= (n : Real) ^ q := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hx hq
  have hFloorLower := Nat.sub_one_lt_floor ((n : Real) ^ q)
  change (n : Real) ^ q - 1 < (powerSamples q n : Real) at hFloorLower
  have hHalf : (n : Real) ^ q / 2 <= (powerSamples q n : Real) := by linarith
  have hUOne : (1 : Real) <= powerSamples q n := by linarith
  have hExponent : 0 <= 1 - 1 / q := by
    have hInv := _root_.div_le_self (by norm_num : (0 : Real) <= 1) hq
    linarith
  have hId : (n : Real) ^ (q - 1) = ((n : Real) ^ q) ^ (1 - 1 / q) := by
    rw [<- Real.rpow_mul (Nat.cast_nonneg n)]
    congr 1
    field_simp [hqPos.ne'] <;> ring
  have hPower : (n : Real) ^ (q - 1) <=
      2 ^ (1 - 1 / q) * (powerSamples q n : Real) ^ (1 - 1 / q) := by
    rw [hId]
    have h := Real.rpow_le_rpow (Real.rpow_nonneg (Nat.cast_nonneg n) q)
      (by linarith : (n : Real) ^ q <= 2 * (powerSamples q n : Real)) hExponent
    rwa [Real.mul_rpow (by norm_num : (0 : Real) <= 2) (by linarith : (0 : Real) <= powerSamples q n)] at h
  have hSuccFloor : (powerSamples q (n + 1) : Real) <= ((n : Real) + 1) ^ q := by
    simpa only [powerSamples, Nat.cast_add, Nat.cast_one] using
      (Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg (n + 1)) q) :
        ((powerSamples q (n + 1)) : Real) <= ((n + 1 : Nat) : Real) ^ q)
  have hUpper := (Real.rpow_succ_sub_bounds q hq (n : Real) hx).2
  have hPowOne : 1 <= (n : Real) ^ (q - 1) :=
    Real.one_le_rpow hx (by linarith)
  have hC : 0 <= q * 2 ^ (q - 1) + 1 := by positivity
  calc
    _ <= q * 2 ^ (q - 1) * (n : Real) ^ (q - 1) + 1 := by linarith
    _ <= q * 2 ^ (q - 1) * (n : Real) ^ (q - 1) + (n : Real) ^ (q - 1) :=
      _root_.add_le_add (le_refl _) hPowOne
    _ = (q * 2 ^ (q - 1) + 1) * (n : Real) ^ (q - 1) := by ring
    _ <= (q * 2 ^ (q - 1) + 1) *
        (2 ^ (1 - 1 / q) * (powerSamples q n : Real) ^ (1 - 1 / q)) :=
      mul_le_mul_of_nonneg_left hPower hC
    _ = _ := by ring

theorem subpowerGapBound_powerSamples (q : Real) (hq : 1 <= q) :
    SubpowerGapBound (powerSamples q) (1 - 1 / q) := by
  intro eps heps
  let C : Real := (q * 2 ^ (q - 1) + 1) * 2 ^ (1 - 1 / q)
  have hqPos : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have hC : 0 < C := by dsimp only [C]; positivity
  refine Exists.intro C (And.intro hC ?_)
  filter_upwards [eventually_ge_atTop (2 : Nat)] with n hn
  have hUOne : (1 : Real) <= powerSamples q n := by
    have hBase := powerSamples_ge_base q hq n (by omega)
    have hNat : 1 <= powerSamples q n := le_trans (by omega) hBase
    simpa only [Nat.cast_one] using
      (Nat.cast_le.mpr hNat : ((1 : Nat) : Real) <= (powerSamples q n : Real))
  have hPower := Real.rpow_le_rpow_of_exponent_le hUOne
    (by linarith : 1 - 1 / q <= (1 - 1 / q) + eps)
  exact (powerSamples_gap_le q hq n hn).trans (mul_le_mul_of_nonneg_left hPower hC.le)

end Nat

namespace Nat

theorem exists_subpower_mesh_log_approximation
    (u : Nat -> Nat) (hu : StrictMono u) (hmesh : Nat.SubpowerGapBound u (3 / 4 : Real))
    (t : Nat -> Real) (ht : Tendsto t atTop atTop) :
    Exists (fun j : Nat -> Nat => Tendsto j atTop atTop /\
      Tendsto (fun n : Nat => Real.log (u (j n) : Real) - t n) atTop (nhds 0)) := by
  classical
  let x : Nat -> Real := fun n => Real.exp (t n)
  have hx : Tendsto x atTop atTop := Real.tendsto_exp_atTop.comp ht
  have hWindow := Nat.eventually_exists_sample_mem_power_window u hu
    (3 / 4 : Real) (7 / 8 : Real) (by norm_num) (by norm_num) hmesh
  have hHit : Filter.Eventually (fun n : Nat =>
      Exists (fun k : Nat => x n <= (u k : Real) /\
        (u k : Real) <= x n + (x n) ^ (7 / 8 : Real))) atTop :=
    hx.eventually hWindow
  let j : Nat -> Nat := fun n =>
    if h : Exists (fun k : Nat => x n <= (u k : Real) /\
        (u k : Real) <= x n + (x n) ^ (7 / 8 : Real))
    then Classical.choose h else 0
  have hBounds : Filter.Eventually (fun n : Nat =>
      x n <= (u (j n) : Real) /\
        (u (j n) : Real) <= x n + (x n) ^ (7 / 8 : Real)) atTop := by
    filter_upwards [hHit] with n hn
    dsimp only [j]
    rw [dif_pos hn]
    exact Classical.choose_spec hn
  have hyTop : Tendsto (fun n : Nat => (u (j n) : Real)) atTop atTop :=
    tendsto_atTop_mono' atTop (hBounds.mono (fun _ h => h.1)) hx
  have hjTop : Tendsto j atTop atTop := by
    apply tendsto_atTop.mpr
    intro K
    filter_upwards [hyTop.eventually_ge_atTop ((u K : Real) + 1)] with n hn
    have hLT : (u K : Real) < (u (j n) : Real) := (lt_add_one _).trans_le hn
    exact (hu.lt_iff_lt.mp (Nat.cast_lt.mp hLT)).le
  have hPow : Tendsto (fun n : Nat => (x n) ^ (-(1 / 8 : Real))) atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop (by norm_num : (0 : Real) < 1 / 8)).comp hx
  have hRatioError : Tendsto (fun n : Nat => (u (j n) : Real) / x n - 1)
      atTop (nhds 0) := by
    apply squeeze_zero' ?_ ?_ hPow
    . filter_upwards [hBounds] with n hn
      rw [sub_nonneg]
      exact (one_le_div (Real.exp_pos (t n))).mpr hn.1
    . filter_upwards [hBounds] with n hn
      have hPos : 0 < x n := Real.exp_pos (t n)
      calc
        (u (j n) : Real) / x n - 1 <=
            (x n + (x n) ^ (7 / 8 : Real)) / x n - 1 :=
          sub_le_sub_right (div_le_div_of_nonneg_right hn.2 hPos.le) 1
        _ = (x n) ^ (-(1 / 8 : Real)) := by
          rw [show -(1 / 8 : Real) = 7 / 8 - 1 by norm_num,
            Real.rpow_sub hPos, Real.rpow_one]
          field_simp
          ring
  have hRatio : Tendsto (fun n : Nat => (u (j n) : Real) / x n)
      atTop (nhds 1) := by
    simpa only [sub_add_cancel, zero_add] using hRatioError.add_const 1
  have hLog : Tendsto (fun n : Nat => Real.log ((u (j n) : Real) / x n))
      atTop (nhds 0) := by
    simpa only [Function.comp_def, Real.log_one] using
      (Real.continuousAt_log (by norm_num : Not ((1 : Real) = 0))).tendsto.comp hRatio
  refine Exists.intro j (And.intro hjTop ?_)
  apply hLog.congr'
  filter_upwards [hBounds] with n hn
  have hXPos : 0 < x n := Real.exp_pos (t n)
  have hYPos : 0 < (u (j n) : Real) := hXPos.trans_le hn.1
  rw [Real.log_div (ne_of_gt hYPos) (ne_of_gt hXPos)]
  dsimp only [x]
  rw [Real.log_exp]


end Nat

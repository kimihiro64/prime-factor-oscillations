/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Assembly.DetectorPackets.CoprimeSchwartzLow

/-!
# SchwartzIntegerPowerTail

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

namespace PrimeFactorOscillations.SchwartzIntegerPowerTail

open MeasureTheory

theorem nat_power_summable (k : Nat) (hk : 2 <= k) :
    Summable (fun n : Nat => 1 / (n : Real) ^ k) := by
  have hkR : (1 : Real) < (k : Real) := by exact_mod_cast hk
  simpa only [Real.rpow_natCast, one_div] using
    (Real.summable_nat_rpow_inv).mpr hkR

theorem nat_shifted_power_tail (k : Nat) (hk : 2 <= k)
    (N : Nat) (hN : 1 <= N) :
    tsum (fun n : Nat => 1 / ((n + (N + 1) : Nat) : Real) ^ k) <=
      1 / (N : Real) ^ (k - 1) := by
  have hNR : (0 : Real) < (N : Real) := by exact_mod_cast (show 0 < N by omega)
  have hkR : (2 : Real) <= (k : Real) := by exact_mod_cast hk
  have hkm : ((k - 1 : Nat) : Real) = (k : Real) - 1 := by
    rw [Nat.cast_sub (by omega : 1 <= k), Nat.cast_one]
  have he : -(k : Real) + 1 = -((k - 1 : Nat) : Real) := by rw [hkm]; ring
  have hanti : AntitoneOn (fun t : Real => t ^ (-(k : Real))) (Set.Ici (N : Real)) := by
    intro x hx y hy hxy
    exact Real.rpow_le_rpow_of_nonpos (lt_of_lt_of_le hNR hx) hxy (by linarith)
  have hlt : -(k : Real) < -1 := by linarith
  have htest := AntitoneOn.tsum_comp_add_le_integral N hanti
    (integrableOn_Ioi_rpow_of_lt hlt hNR)
    (fun t ht => Real.rpow_nonneg (le_of_lt (lt_trans hNR ht)) _)
  have hconvert (n : Nat) :
      (((n + N + 1 : Nat) : Real) ^ (-(k : Real))) =
        1 / ((n + (N + 1) : Nat) : Real) ^ k := by
    rw [Real.rpow_neg (by positivity), Real.rpow_natCast, one_div, Nat.add_assoc]
  have hintegral :
      (integral (volume.restrict (Set.Ioi (N : Real)))
        (fun t : Real => t ^ (-(k : Real)))) =
        (1 / (N : Real) ^ (k - 1)) / (k - 1 : Real) := by
    rw [integral_Ioi_rpow_of_lt hlt hNR, he,
      Real.rpow_neg (le_of_lt hNR), Real.rpow_natCast, hkm]
    field_simp
  have hkmpos : (0 : Real) < (k : Real) - 1 := by linarith
  have hkmone : (1 : Real) <= (k : Real) - 1 := by linarith
  have hfinal : (1 / (N : Real) ^ (k - 1)) / ((k : Real) - 1) <=
      1 / (N : Real) ^ (k - 1) := by
    calc
      _ <= (1 / (N : Real) ^ (k - 1)) / 1 :=
        div_le_div_of_nonneg_left (by positivity) (by norm_num) hkmone
      _ = _ := div_one _
  rw [hintegral] at htest
  simpa only [hconvert] using htest.trans hfinal

theorem finite_power_tail (k : Nat) (hk : 2 <= k) :
    exists A : Real, 0 < A /\
      forall (y : Real) (E : Finset Nat), 0 < y ->
      (forall n : Nat, Membership.mem E n -> y < (n : Real)) ->
      E.sum (fun n => 1 / (n : Real) ^ k) <= A / y ^ (k - 1) := by
  let w : Nat -> Real := fun n => 1 / (n : Real) ^ k
  let T : Real := tsum w
  have hw : Summable w := nat_power_summable k hk
  have hw0 (n : Nat) : 0 <= w n := by dsimp only [w]; positivity
  have hT : 0 <= T := tsum_nonneg hw0
  let A : Real := 2 ^ (k - 1) + T + 1
  have hA : 0 < A := by dsimp only [A]; positivity
  refine Exists.intro A (And.intro hA ?_)
  intro y E hy hE
  have hsum : E.sum w <= T := hw.sum_le_tsum E (fun n hn => hw0 n)
  have hpowY : 0 < y ^ (k - 1) := pow_pos hy _
  by_cases hy1 : y < 1
  next =>
    have hp : forall j : Nat, y ^ j <= 1 := by
      intro j
      induction j with
      | zero => simp only [pow_zero, le_refl]
      | succ j hj =>
          rw [pow_succ]
          exact (mul_le_mul hj hy1.le hy.le (by norm_num)).trans_eq (one_mul 1)
    have hAT : T <= A := by
      have htwo : (0 : Real) <= 2 ^ (k - 1) := by positivity
      dsimp only [A]
      linarith
    have hAdiv : A <= A / y ^ (k - 1) := by
      calc
        _ = A / 1 := (div_one _).symm
        _ <= _ := div_le_div_of_nonneg_left hA.le hpowY (hp (k - 1))
    exact hsum.trans (hAT.trans hAdiv)
  next =>
    have hyge : 1 <= y := le_of_not_gt hy1
    let N : Nat := Nat.floor y
    have hN : 1 <= N := Nat.le_floor (by simpa only [Nat.cast_one] using hyge)
    have hNR : (0 : Real) < (N : Real) := by exact_mod_cast (show 0 < N by omega)
    have hEN (n : Nat) (hn : Membership.mem E n) : N + 1 <= n := by
      have h := (Nat.floor_lt hy.le).mpr (hE n hn)
      dsimp only [N] at *
      omega
    let G : Finset Nat := E.image (fun n => n - (N + 1))
    have hsumeq : E.sum w = G.sum (fun n => w (n + (N + 1))) := by
      dsimp only [G]
      rw [Finset.sum_image]
      next =>
        apply Finset.sum_congr rfl
        intro n hn
        rw [Nat.sub_add_cancel (hEN n hn)]
      next =>
        intro a ha b hb hab
        have hna := hEN a ha
        have hnb := hEN b hb
        change a - (N + 1) = b - (N + 1) at hab
        omega
    have hshift : Summable (fun n : Nat => w (n + (N + 1))) :=
      (summable_nat_add_iff (N + 1)).mpr hw
    have htail : E.sum w <= 1 / (N : Real) ^ (k - 1) := by
      rw [hsumeq]
      exact (hshift.sum_le_tsum G (fun n hn => hw0 _)).trans
        (nat_shifted_power_tail k hk N hN)
    have hfloor : y < (N : Real) + 1 := Nat.lt_floor_add_one y
    have hN1 : (1 : Real) <= (N : Real) := by exact_mod_cast hN
    have hyN : y / 2 <= (N : Real) := by linarith
    have hp : forall j : Nat, (y / 2) ^ j <= (N : Real) ^ j := by
      intro j
      induction j with
      | zero => simp only [pow_zero, le_refl]
      | succ j hj =>
          rw [pow_succ, pow_succ]
          exact mul_le_mul hj hyN (by positivity) (by positivity)
    have hinv : 1 / (N : Real) ^ (k - 1) <=
        2 ^ (k - 1) / y ^ (k - 1) := by
      calc
        _ <= 1 / (y / 2) ^ (k - 1) :=
          one_div_le_one_div_of_le (pow_pos (by positivity) _) (hp (k - 1))
        _ = _ := by rw [div_pow]; field_simp
    have htwo : (2 : Real) ^ (k - 1) <= A := by dsimp only [A]; linarith
    exact htail.trans (hinv.trans (div_le_div_of_nonneg_right htwo hpowY.le))

end PrimeFactorOscillations.SchwartzIntegerPowerTail


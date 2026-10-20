/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Assembly.DetectorPackets.RHWaveRecurrence
import PrimeFactorOscillations.Assembly.DetectorPackets.RHZeroReconstruction
import PrimeFactorOscillations.Helpers.NicolasSparseRecurrence

/-!
# RHSparseLimsup

Maintained extraction of completed detector/packet proof components.
All original theorem hypotheses and retained proof bodies are preserved.
This module alone asserts no improved zero-free boundary.
-/

set_option autoImplicit false
set_option Elab.async false

open Filter
open scoped Topology

noncomputable section

namespace PrimeFactorOscillations

open Robin1984

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

/-- The full spectral amplitude is approached along every admissible sparse mesh. -/
theorem limsup_eq_of_eventually_le_and_frequently_gt
    (v : Nat -> Real) (b : Real)
    (hUpper : forall eps : Real, 0 < eps ->
      Filter.Eventually (fun n : Nat => v n <= b + eps) atTop)
    (hLower : forall eps : Real, 0 < eps ->
      Filter.Frequently (fun n : Nat => b - eps < v n) atTop) :
    Filter.limsup v atTop = b := by
  rw [Filter.limsup_eq]
  let S : Set Real := fun a => Filter.Eventually (fun n : Nat => v n <= a) atTop
  change sInf S = b
  have hNonempty : S.Nonempty := Exists.intro (b + 1) (hUpper 1 zero_lt_one)
  have hEvery (a : Real) (ha : S a) : b <= a := by
    by_contra hn
    have hlt : a < b := lt_of_not_ge hn
    have heps : 0 < (b - a) / 2 := by linarith
    have hFreq := hLower ((b - a) / 2) heps
    change Not (Filter.Eventually (fun n : Nat => Not (b - (b - a) / 2 < v n)) atTop) at hFreq
    apply hFreq
    filter_upwards [ha] with n hna
    intro hp
    linarith
  have hBdd : BddBelow S := Exists.intro b hEvery
  apply le_antisymm
  . by_contra hn
    have hlt : b < sInf S := lt_of_not_ge hn
    have heps : 0 < (sInf S - b) / 2 := by linarith
    have hMem : S (b + (sInf S - b) / 2) := hUpper ((sInf S - b) / 2) heps
    have hLe := csInf_le hBdd hMem
    linarith
  . exact le_csInf hNonempty hEvery

namespace QuadraticPrimeLaw

/- The family-specific limsup specialization is supplied by the
maintained recurrence owners imported above. -/
end QuadraticPrimeLaw

end PrimeFactorOscillations

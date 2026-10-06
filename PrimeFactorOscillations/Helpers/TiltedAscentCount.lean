/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.TiltedAscentGrid

/-!
# Exact signed counts on the tilt grid

The inclusive grid and strict ascent test give an exact ceiling count.
Actual-minus-reference counts have error strictly less than one per selected
cell. The aggregate theorem preserves the entire signed gain and explicitly
bounds every rounding loss; no prime-pair supply is assumed by this finite
lemma, and no asymptotic RH count criterion is asserted here.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

theorem tiltAscentSet_eq_range_ceil (H M : Nat) (hM : 0 < M)
    (R g : Real) (hHigh : R - g <= (H : Real) + 1) :
    tiltAscentSet H M R g =
      Finset.range (Nat.ceil ((M : Real) * (R - g - 1))) := by
  classical
  have hMr : (0 : Real) < M := by exact_mod_cast hM
  let y : Real := (M : Real) * (R - g - 1)
  have hyHigh : y <= ((H * M : Nat) : Real) := by
    have h := mul_le_mul_of_nonneg_left (show R - g - 1 <= H by linarith) hMr.le
    simp only [Nat.cast_mul]
    dsimp [y]
    nlinarith only [h]
  have hCeil : Nat.ceil y <= H * M := Nat.ceil_le.mpr hyHigh
  have hTest (j : Nat) : g + 1 + (j : Real) / M < R <-> (j : Real) < y := by
    have hCancel : ((j : Real) / M) * M = j := by field_simp [hMr.ne']
    constructor
    . intro h
      have hs := mul_lt_mul_of_pos_right h hMr
      dsimp [y]
      nlinarith only [hs, hCancel]
    . intro h
      have hs := div_lt_div_of_pos_right h hMr
      have hY : y / M = R - g - 1 := by dsimp [y]; field_simp [hMr.ne']
      rw [hY] at hs
      linarith only [hs]
  ext j
  simp only [tiltAscentSet, Finset.mem_filter, Finset.mem_range]
  rw [hTest, <- Nat.lt_ceil]
  constructor
  . intro h
    exact h.2
  . intro h
    change j < Nat.ceil y at h
    exact And.intro (Nat.lt_succ_of_le (h.le.trans hCeil)) h

theorem tiltAscentSet_card_eq_ceil (H M : Nat) (hM : 0 < M)
    (R g : Real) (hHigh : R - g <= (H : Real) + 1) :
    (tiltAscentSet H M R g).card = Nat.ceil ((M : Real) * (R - g - 1)) := by
  rw [tiltAscentSet_eq_range_ceil H M hM R g hHigh, Finset.card_range]

theorem tiltAscentSet_signed_error_lt_one (H M : Nat) (hM : 0 < M)
    (R U g : Real)
    (hRLow : 1 <= R - g) (hRHigh : R - g <= (H : Real) + 1)
    (hULow : 1 <= U - g) (hUHigh : U - g <= (H : Real) + 1) :
    abs (((tiltAscentSet H M R g).card : Real) -
      ((tiltAscentSet H M U g).card : Real) - (M : Real) * (R - U)) < 1 := by
  have hMr : (0 : Real) <= M := Nat.cast_nonneg M
  let yR : Real := (M : Real) * (R - g - 1)
  let yU : Real := (M : Real) * (U - g - 1)
  have hyR : 0 <= yR := mul_nonneg hMr (by linarith)
  have hyU : 0 <= yU := mul_nonneg hMr (by linarith)
  have hR1 : yR <= (Nat.ceil yR : Real) := Nat.le_ceil yR
  have hR2 : (Nat.ceil yR : Real) < yR + 1 := Nat.ceil_lt_add_one hyR
  have hU1 : yU <= (Nat.ceil yU : Real) := Nat.le_ceil yU
  have hU2 : (Nat.ceil yU : Real) < yU + 1 := Nat.ceil_lt_add_one hyU
  rw [tiltAscentSet_card_eq_ceil H M hM R g hRHigh,
    tiltAscentSet_card_eq_ceil H M hM U g hUHigh]
  have hDiff : (M : Real) * (R - U) = yR - yU := by dsimp [yR, yU]; ring
  rw [hDiff]
  change abs ((Nat.ceil yR : Real) - (Nat.ceil yU : Real) - (yR - yU)) < 1
  exact abs_lt.mpr (And.intro (by linarith only [hR1, hU2])
    (by linarith only [hR2, hU1]))

theorem tiltAscentSet_sum_lower {I : Type*} (s : Finset I)
    (H M : Nat) (hM : 0 < M) (R U g : I -> Real) (delta : Real)
    (hRLow : forall i, Membership.mem s i -> 1 <= R i - g i)
    (hRHigh : forall i, Membership.mem s i -> R i - g i <= (H : Real) + 1)
    (hULow : forall i, Membership.mem s i -> 1 <= U i - g i)
    (hUHigh : forall i, Membership.mem s i -> U i - g i <= (H : Real) + 1)
    (hDelta : forall i, Membership.mem s i -> delta <= R i - U i) :
    (s.card : Real) * ((M : Real) * delta - 1) <=
      Finset.sum s (fun i => ((tiltAscentSet H M (R i) (g i)).card : Real) -
        ((tiltAscentSet H M (U i) (g i)).card : Real)) := by
  classical
  calc
    _ = Finset.sum s (fun _ => (M : Real) * delta - 1) := by simp [mul_sub]
    _ <= _ := by
      apply Finset.sum_le_sum
      intro i hi
      have hError := tiltAscentSet_signed_error_lt_one H M hM (R i) (U i) (g i)
        (hRLow i hi) (hRHigh i hi) (hULow i hi) (hUHigh i hi)
      have hLower := (abs_lt.mp hError).1
      have hGain := mul_le_mul_of_nonneg_left (hDelta i hi) (Nat.cast_nonneg M : (0 : Real) <= M)
      linarith only [hLower, hGain]

end PrimeFactorOscillations

/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.LPFGoldbachWindows

/-!
# Fixed subwindows for the positive LPF source

Contained intervals give a positive convolution kernel without approximating
the complete moving window. The covering has a bounded number of intervals.
-/

set_option Elab.async false

namespace PrimeFactorOscillations.LPF

def goldbachFixedSubwindow (h c : Nat) : Finset Nat :=
  Finset.Ioo (c - h) (c + 2 * h)

/-- Every member of the fixed interval belongs to the raw moving window. -/
theorem goldbachFixedSubwindow_subset (M h c t : Nat)
    (hWidth : 2 * h <= M / 64) (hCenter : h <= c)
    (hTarget : 2 * c <= t) (hTargetUpper : t < 2 * c + 2 * h) :
    goldbachFixedSubwindow h c <= goldbachWindowInputs M t := by
  intro p hp
  have hP := Finset.mem_Ioo.mp hp
  apply Finset.mem_Ioo.mpr
  omega

/-- An explicit core of h consecutive inputs has its partner in the same interval. -/
theorem goldbachFixedSubwindow_main_card (h c t : Nat)
    (hCenter : h <= c)
    (hTarget : 2 * c <= t) (hTargetUpper : t < 2 * c + 2 * h) :
    h <= (Finset.sumPartners (goldbachFixedSubwindow h c) t).card := by
  have hCore : Finset.Ico c (c + h) <=
      Finset.sumPartners (goldbachFixedSubwindow h c) t := by
    intro p hp
    have hP := Finset.mem_Ico.mp hp
    apply Finset.mem_filter.mpr
    refine And.intro (Finset.mem_Ioo.mpr (by omega)) ?_
    exact And.intro (Finset.mem_Ioo.mpr (by omega)) (by omega)
  have hCard := Finset.card_le_card hCore
  simpa only [Nat.card_Ico, Nat.add_sub_cancel_left] using hCard

/-- The same 257 fixed intervals cover both even-target source pools. -/
theorem goldbachFixedSubwindow_cover (M t : Nat) (hM : 256 <= M)
    (ht : Membership.mem
      (Union.union (goldbachEvenTargets (M / 2)) (goldbachEvenTargets M)) t) :
    exists b : Nat, And (b <= 256)
      (And (goldbachFixedSubwindow (M / 128) (b * (M / 128)) <= goldbachWindowInputs M t)
        (M / 256 <=
          (Finset.sumPartners (goldbachFixedSubwindow (M / 128) (b * (M / 128))) t).card)) := by
  have hLo : M / 2 < t := by
    rcases Finset.mem_union.mp ht with h | h
    next => exact (Finset.mem_Ioo.mp (Finset.mem_filter.mp h).1).1
    next => have hI := Finset.mem_Ioo.mp (Finset.mem_filter.mp h).1; omega
  have hHi : t < 2 * M := by
    rcases Finset.mem_union.mp ht with h | h
    next => have hI := Finset.mem_Ioo.mp (Finset.mem_filter.mp h).1; omega
    next => exact (Finset.mem_Ioo.mp (Finset.mem_filter.mp h).1).2
  let h := M / 128
  let b := t / (2 * h)
  let c := b * h
  have hPos : 0 < h := by dsimp [h]; omega
  have hWidth : 2 * h <= M / 64 := by dsimp [h]; omega
  have hScale : M <= 256 * h := by dsimp [h]; omega
  have hLowScale : 2 * h <= M / 2 := by dsimp [h]; omega
  have hRem : t % (2 * h) < 2 * h := Nat.mod_lt _ (by omega)
  have hDecomp : t = 2 * c + t % (2 * h) := by
    dsimp [c, b]
    nlinarith [Nat.mod_add_div t (2 * h)]
  have hTarget : 2 * c <= t := by omega
  have hTargetUpper : t < 2 * c + 2 * h := by omega
  have hbPos : 1 <= b := by
    by_contra hBad
    have hbZero : b = 0 := by
      by_contra hNe
      exact hBad (Nat.one_le_iff_ne_zero.mpr hNe)
    have hcZero : c = 0 := by dsimp [c]; rw [hbZero]; simp
    omega
  have hCenter : h <= c := by
    have hMul := Nat.mul_le_mul_right h hbPos
    simpa only [Nat.one_mul] using hMul
  have hbBound : b <= 256 := by
    by_contra hBad
    have hbLarge : 257 <= b := by omega
    have hMul := Nat.mul_le_mul_right h hbLarge
    dsimp [c] at hTarget
    nlinarith
  refine Exists.intro b (And.intro hbBound (And.intro
    (goldbachFixedSubwindow_subset M h c t hWidth hCenter hTarget hTargetUpper) ?_))
  have hKernel := goldbachFixedSubwindow_main_card h c t hCenter hTarget hTargetUpper
  have hHalf : M / 256 <= h := by dsimp [h]; omega
  exact hHalf.trans hKernel

end PrimeFactorOscillations.LPF

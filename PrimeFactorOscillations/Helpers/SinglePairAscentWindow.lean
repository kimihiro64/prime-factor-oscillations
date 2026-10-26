/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.LocalizedAscentPointwise

/-!
# One localized prime pair retains an unbounded false-RH ascent signal

The locator asks for one actual consecutive bounded-gap prime pair per cutoff.
No quantitative count or injectivity across cutoffs is assumed. The observable
keeps the original growing rank, square-root tilt mesh and complete grid error.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

open Filter PrimeFactorUnimodality

def LocalAscentLocator (H : Nat) (a : Nat -> Nat) : Prop :=
  Filter.Eventually (fun X : Nat =>
    2 <= primeGap (a X) /\ primeGap (a X) <= H /\
      (X : Real) <= ((primeAt (a X) - 1 : Nat) : Real) /\
      ((primeAt (a X) - 1 : Nat) : Real) <=
        (X : Real) + (X : Real) ^ (3 / 4 : Real)) atTop

theorem singleAscentMesh_power_unbounded (b C : Real) (hb : b < 1 / 2) :
    Filter.Eventually (fun X : Nat =>
      C < (localTiltMesh X : Real) * (X : Real) ^ (-b) - 1) atTop := by
  have he : 0 < (1 / 2 : Real) - b := by linarith
  have hCast : Tendsto (fun n : Nat => (n : Real)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hGrow := hCast.eventually ((tendsto_rpow_atTop he).eventually_gt_atTop (C + 1))
  filter_upwards [hGrow, eventually_ge_atTop (1 : Nat)] with X hLarge hOne
  have hx : 0 < (X : Real) := by exact_mod_cast (by omega : 0 < X)
  have hMesh := mul_le_mul_of_nonneg_right
    (Nat.le_ceil ((X : Real) ^ (1 / 2 : Real)))
    (Real.rpow_nonneg hx.le (-b))
  change (X : Real) ^ (1 / 2 : Real) * (X : Real) ^ (-b) <=
    (localTiltMesh X : Real) * (X : Real) ^ (-b) at hMesh
  rw [<- Real.rpow_add hx] at hMesh
  have hExponent : (1 / 2 : Real) + -b = 1 / 2 - b := by ring
  rw [hExponent] at hMesh
  linarith

theorem singleAscentPairExcess_nonpos_eventually_of_RH
    (H : Nat) (a : Nat -> Nat) (hs : LocalAscentLocator H a)
    (hRH : RiemannHypothesis) :
    Filter.Eventually (fun X : Nat => localAscentPairExcess H X (a X) <= 0) atTop := by
  let alpha : Real := (H : Real) + 2
  have ha : 0 < alpha := by dsimp [alpha]; positivity
  have hCast : Tendsto (fun n : Nat => (n : Real)) atTop atTop := tendsto_natCast_atTop_atTop
  have hBands := hCast.eventually (eventually_primeProfile_fixed_window_bands alpha ha)
  choose Y hY using eventually_atTop.mp
    (eventually_densityRatio_thetaClock_lt_reference_uniform_of_RH hRH
      (alpha / 3) (2 * alpha) (by linarith) (by linarith))
  filter_upwards [hs, hBands, hCast.eventually (eventually_ge_atTop Y),
    eventually_ge_atTop (1 : Nat)] with X hc hb hxY hx
  have hx1 : (1 : Real) <= X := by exact_mod_cast hx
  have hp : (X : Real) ^ (3 / 4 : Real) <= X := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hx1
      (by norm_num : (3 / 4 : Real) <= 1)
  have hPair := hc
  let y : Real := ((primeAt (a X) - 1 : Nat) : Real)
  have hy : X <= y := hPair.2.2.1
  have hB := hb.2 y hy (by dsimp [y]; linarith [hPair.2.2.2])
  have hCompare := (hY y (hxY.trans hy)).2.2 (localTiltRank H X) hB.1 hB.2.1
  have hCut : Nat.floor y + 1 = primeAt (a X) := by
    dsimp [y]
    rw [Nat.floor_natCast, Nat.sub_add_cancel (prime_primeAt (a X)).one_lt.le]
  rw [hCut] at hB hCompare
  have hActual := localTiltAscentSet_eq_scalar H (localTiltMesh X) (localTiltRank H X)
    (a X) hb.1 (weightEsymm_positive_degree_supported _ _ hB.2.2.1)
  have hLe := tiltAscentSet_card_le H (localTiltMesh X)
    (localTiltReference H X (a X))
    (densityRatio (primesBelow (primeAt (a X))) (localTiltRank H X) : Real)
    (primeGap (a X) : Real) hCompare.2.2.le
  unfold localAscentPairExcess
  rw [hActual]
  exact sub_nonpos.mpr (by exact_mod_cast hLe)

theorem singleAscentPairExcess_unbounded_of_not_RH
    (H : Nat) (a : Nat -> Nat) (hs : LocalAscentLocator H a)
    (hNotRH : Not RiemannHypothesis) (C X0 : Real) :
    exists n : Nat, X0 < (n : Real) /\ C < localAscentPairExcess H n (a n) := by
  let alpha : Real := (H : Real) + 2
  have ha : 0 < alpha := by dsimp [alpha]; positivity
  choose b hb hbHalf hWindows using exists_densityRatio_uniform_power_excess_of_not_RH
    hNotRH (alpha / 3) (2 * alpha) (by linarith) (by linarith)
  have hCast : Tendsto (fun n : Nat => (n : Real)) atTop atTop := tendsto_natCast_atTop_atTop
  have hBands := hCast.eventually (eventually_primeProfile_fixed_window_bands alpha ha)
  have hAmplify := singleAscentMesh_power_unbounded b C hbHalf
  choose N hN using eventually_atTop.mp (hs.and (hBands.and hAmplify))
  choose n hn hnSix hEx using hWindows (3 / 4) (by norm_num) 1
    (max X0 (N : Real)) (by norm_num)
  have hnN : N <= n := by
    have hh := (le_max_right X0 (N : Real)).trans hn.le
    exact_mod_cast hh
  have hPairData := (hN n hnN).1
  have hBand := (hN n hnN).2.1
  have hAmplitude := (hN n hnN).2.2
  have hnPos : (0 : Real) < n := by exact_mod_cast (by omega : 0 < n)
  have hnOne : (1 : Real) <= n := by exact_mod_cast (by omega : 1 <= n)
  have hPow : (n : Real) ^ (3 / 4 : Real) <= n := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hnOne
      (by norm_num : (3 / 4 : Real) <= 1)
  let r := localTiltRank H n
  let M := localTiltMesh n
  have hMle : (n : Real) ^ (1 / 2 : Real) <= (M : Real) := Nat.le_ceil _
  have hMPos : 0 < M := by
    have h := (Real.rpow_pos_of_pos hnPos (1 / 2 : Real)).trans_le hMle
    exact_mod_cast h
  refine Exists.intro n (And.intro ((le_max_left _ _).trans_lt hn) ?_)
  have hi := hPairData
  let y : Real := ((primeAt (a n) - 1 : Nat) : Real)
  have hyLow : (n : Real) <= y := hi.2.2.1
  have hyHigh : y <= n + (n : Real) ^ (3 / 4 : Real) := hi.2.2.2
  have hData := hBand.2 y hyLow (by linarith)
  have hDiff := (hEx y hyLow hyHigh).2 r hData.1 hData.2.1
  have hCut : Nat.floor y + 1 = primeAt (a n) := by
    dsimp [y]
    rw [Nat.floor_natCast, Nat.sub_add_cancel (prime_primeAt (a n)).one_lt.le]
  rw [hCut] at hData hDiff
  let R : Real := (densityRatio (primesBelow (primeAt (a n))) r : Real)
  let U : Real := localTiltReference H n (a n)
  let g : Real := (primeGap (a n) : Real)
  have hG : (2 : Real) <= g := by dsimp [g]; exact_mod_cast hi.1
  have hGH : g <= H := by dsimp [g]; exact_mod_cast hi.2.1
  have hRNear : -(1 / 2 : Real) <= R - alpha /\ R - alpha <= 1 / 2 :=
    abs_le.mp hData.2.2.2.2
  have hUNear : -(1 / 2 : Real) <= U - alpha /\ U - alpha <= 1 / 2 :=
    abs_le.mp hData.2.2.2.1
  dsimp only [alpha] at hRNear hUNear
  have hError := tiltAscentSet_signed_error_lt_one H M hMPos R U g
    (by linarith) (by linarith) (by linarith) (by linarith)
  have hDelta : (n : Real) ^ (-b) <= R - U := by
    simpa only [one_mul, R, U, r, localTiltReference, y] using hDiff.2.2.le
  have hGain := mul_le_mul_of_nonneg_left hDelta (Nat.cast_nonneg M : (0 : Real) <= M)
  have hActual := localTiltAscentSet_eq_scalar H M r (a n) hBand.1
    (weightEsymm_positive_degree_supported _ _ hData.2.2.1)
  unfold localAscentPairExcess
  rw [hActual]
  change C < ((tiltAscentSet H M R g).card : Real) - ((tiltAscentSet H M U g).card : Real)
  have hLower := (abs_lt.mp hError).1
  change C < (M : Real) * (n : Real) ^ (-b) - 1 at hAmplitude
  linarith

end PrimeFactorOscillations

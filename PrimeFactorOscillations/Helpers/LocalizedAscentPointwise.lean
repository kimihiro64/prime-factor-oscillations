/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.AscentSamplingGrowth
import PrimeFactorOscillations.Helpers.LocalizedAscentCount

/-!
# Pointwise signed ascent windows

The same actual density, rank, prime pair and inclusive tilt grid are retained
in every summand. False RH gives a common positive lower bound at all selected
pairs, not merely a positive unweighted total. This permits arithmetic weights.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

open Filter PrimeFactorUnimodality

def localAscentPairExcess (H X i : Nat) : Real :=
  ((localTiltAscentSet H (localTiltMesh X) (localTiltRank H X) i).card : Real) -
    ((tiltAscentSet H (localTiltMesh X) (localTiltReference H X i)
      (primeGap i : Real)).card : Real)

theorem localAscentPairExcess_nonpos_eventually_of_RH
    (H : Nat) (m : Nat -> Nat) (a : (X : Nat) -> Fin (m X) -> Nat)
    (hs : LocalAscentSampling H m a) (hRH : RiemannHypothesis) :
    Filter.Eventually (fun X : Nat => forall i : Fin (m X),
      localAscentPairExcess H X (a X i) <= 0) atTop := by
  let alpha : Real := (H : Real) + 2
  have ha : 0 < alpha := by dsimp [alpha]; positivity
  have hCast : Tendsto (fun n : Nat => (n : Real)) atTop atTop := tendsto_natCast_atTop_atTop
  have hBands := hCast.eventually (eventually_primeProfile_fixed_window_bands alpha ha)
  choose Y hY using eventually_atTop.mp
    (eventually_densityRatio_thetaClock_lt_reference_uniform_of_RH hRH
      (alpha / 3) (2 * alpha) (by linarith) (by linarith))
  filter_upwards [hs.2, hBands, hCast.eventually (eventually_ge_atTop Y),
    eventually_ge_atTop (1 : Nat)] with X hc hb hxY hx
  intro i
  have hx1 : (1 : Real) <= X := by exact_mod_cast hx
  have hp : (X : Real) ^ (3 / 4 : Real) <= X := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hx1
      (by norm_num : (3 / 4 : Real) <= 1)
  have hPair := hc.2 i
  let y : Real := ((primeAt (a X i) - 1 : Nat) : Real)
  have hy : X <= y := hPair.2.2.1
  have hB := hb.2 y hy (by dsimp [y]; linarith [hPair.2.2.2])
  have hCompare := (hY y (hxY.trans hy)).2.2 (localTiltRank H X) hB.1 hB.2.1
  have hCut : Nat.floor y + 1 = primeAt (a X i) := by
    dsimp [y]
    rw [Nat.floor_natCast, Nat.sub_add_cancel (prime_primeAt (a X i)).one_lt.le]
  rw [hCut] at hB hCompare
  have hActual := localTiltAscentSet_eq_scalar H (localTiltMesh X) (localTiltRank H X)
    (a X i) hb.1 (weightEsymm_positive_degree_supported _ _ hB.2.2.1)
  have hLe := tiltAscentSet_card_le H (localTiltMesh X)
    (localTiltReference H X (a X i))
    (densityRatio (primesBelow (primeAt (a X i))) (localTiltRank H X) : Real)
    (primeGap (a X i) : Real) hCompare.2.2.le
  unfold localAscentPairExcess
  rw [hActual]
  exact sub_nonpos.mpr (by exact_mod_cast hLe)

theorem localAscentPairExcess_common_large_window_of_not_RH
    (H : Nat) (m : Nat -> Nat) (a : (X : Nat) -> Fin (m X) -> Nat)
    (hs : LocalAscentSampling H m a) (hNotRH : Not RiemannHypothesis)
    (C X0 : Real) (hC : 0 < C) :
    exists n : Nat, X0 < (n : Real) /\
      exists B : Real, 0 <= B /\
        C * (n : Real) ^ (7 / 10 : Real) < (m n : Real) * B /\
        forall i : Fin (m n), B <= localAscentPairExcess H n (a n i) := by
  let alpha : Real := (H : Real) + 2
  have ha : 0 < alpha := by dsimp [alpha]; positivity
  choose b hb hbHalf hWindows using exists_densityRatio_uniform_power_excess_of_not_RH
    hNotRH (alpha / 3) (2 * alpha) (by linarith) (by linarith)
  have hCast : Tendsto (fun n : Nat => (n : Real)) atTop atTop := tendsto_natCast_atTop_atTop
  have hBands := hCast.eventually (eventually_primeProfile_fixed_window_bands alpha ha)
  have hAmplify := power_subpower_mesh_amplification m hs.1 b C hbHalf hC
  choose N hN using eventually_atTop.mp (hs.2.and (hBands.and hAmplify))
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
  let B : Real := (M : Real) * (n : Real) ^ (-b) - 1
  have hMle : (n : Real) ^ (1 / 2 : Real) <= (M : Real) := Nat.le_ceil _
  have hMPos : 0 < M := by
    have h := (Real.rpow_pos_of_pos hnPos (1 / 2 : Real)).trans_le hMle
    exact_mod_cast h
  have hAmp : C * (n : Real) ^ (7 / 10 : Real) < (m n : Real) * B := hAmplitude
  have hB : 0 <= B := by
    by_contra hnB
    have hProduct := mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg (m n))
      (le_of_not_ge hnB)
    have hPositive := mul_pos hC (Real.rpow_pos_of_pos hnPos (7 / 10 : Real))
    linarith
  refine Exists.intro n (And.intro ((le_max_left _ _).trans_lt hn)
    (Exists.intro B (And.intro hB (And.intro hAmp ?_))))
  intro i
  have hi := hPairData.2 i
  let y : Real := ((primeAt (a n i) - 1 : Nat) : Real)
  have hyLow : (n : Real) <= y := hi.2.2.1
  have hyHigh : y <= n + (n : Real) ^ (3 / 4 : Real) := hi.2.2.2
  have hData := hBand.2 y hyLow (by linarith)
  have hDiff := (hEx y hyLow hyHigh).2 r hData.1 hData.2.1
  have hCut : Nat.floor y + 1 = primeAt (a n i) := by
    dsimp [y]
    rw [Nat.floor_natCast, Nat.sub_add_cancel (prime_primeAt (a n i)).one_lt.le]
  rw [hCut] at hData hDiff
  let R : Real := (densityRatio (primesBelow (primeAt (a n i))) r : Real)
  let U : Real := localTiltReference H n (a n i)
  let g : Real := (primeGap (a n i) : Real)
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
  have hActual := localTiltAscentSet_eq_scalar H M r (a n i) hBand.1
    (weightEsymm_positive_degree_supported _ _ hData.2.2.1)
  unfold localAscentPairExcess
  rw [hActual]
  change B <= ((tiltAscentSet H M R g).card : Real) - ((tiltAscentSet H M U g).card : Real)
  dsimp only [B]
  have hLower := (abs_lt.mp hError).1
  linarith

end PrimeFactorOscillations
